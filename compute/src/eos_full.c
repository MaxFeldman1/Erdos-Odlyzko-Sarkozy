/*
 * eos_full: full representation counts N(a) = #{(p,q) ordered : p,q <= m, p,q not | m, pq = a mod m}
 * for each m in a range or list, plus derived statistics:
 *   R(m)   = min_a N(a) / lambda,  lambda = pi_m^2 / phi(m)
 *   E(m)   = sum_a N(a)^2  (multiplicative energy of P mod m), compared with pi^4/phi + 2 pi^2
 *   y(m)   = least y such that {p,q <= y} covers every reduced class (computed in the same pass:
 *            the outer loop runs over q increasing, the inner over p <= q, so the first time a
 *            class is hit is with the least possible max(p,q)).
 *   class-type breakdown: a = 1, a = -1, squares vs non-squares of G, small a.
 *
 * usage: eos_full range m0 m1 out.csv     |   eos_full list file out.csv
 */
#include "common.h"
#include <omp.h>

static int cmpu(const void *a, const void *b) {
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b; return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage\n"); return 1; }
    uint32_t *ms = NULL; size_t nms = 0; const char *out;
    if (!strcmp(argv[1], "range")) {
        uint32_t m0 = atol(argv[2]), m1 = atol(argv[3]); out = argv[4];
        if (m0 < 3) m0 = 3;
        nms = m1 - m0 + 1; ms = malloc(nms * 4);
        for (size_t i = 0; i < nms; i++) ms[i] = m0 + (uint32_t)i;
    } else {
        FILE *f = fopen(argv[2], "r"); out = argv[3];
        size_t cap = 1024; ms = malloc(cap * 4); unsigned long v;
        while (fscanf(f, "%lu", &v) == 1) { if (nms == cap) { cap *= 2; ms = realloc(ms, cap * 4); } ms[nms++] = (uint32_t)v; }
        fclose(f);
        qsort(ms, nms, 4, cmpu);
    }
    uint32_t mmax = ms[nms - 1];
    sieve_t S; sieve_init(&S, mmax + 1);
    char **lines = calloc(nms, sizeof(char *));
    double t0 = omp_get_wtime();

#pragma omp parallel
    {
        uint32_t *N = malloc((size_t)(mmax + 1) * 4);
        uint8_t *u = malloc(mmax + 1), *sq = malloc(mmax + 1);
        uint32_t *P = malloc((size_t)S.npr * 4), *D = calloc(mmax + 1, 4);
        uint32_t *T = malloc(4096 * 4);
#pragma omp for schedule(dynamic, 1)
        for (size_t idx = 0; idx < nms; idx++) {
            /* process largest first for load balance */
            uint32_t m = ms[nms - 1 - idx];
            uint32_t f[16]; int k = factor_distinct(&S, m, f);
            uint64_t ph = euler_phi(m, f, k);
            unit_mask(u, m, f, k);
            uint32_t np = 0;
            for (uint32_t j = 0; j < S.picnt[m]; j++) if (u[S.pr[j] % m]) P[np++] = S.pr[j];
            uint32_t maxgap = 0;
            for (uint32_t j = 1; j < np; j++) if (P[j] - P[j - 1] > maxgap) maxgap = P[j] - P[j - 1];
            if (maxgap >= 4096) { fprintf(stderr, "gap too big\n"); exit(1); }
            memset(N, 0, (size_t)m * 4);
            uint64_t cov = 0; uint32_t y = 0, y_a = 0;
            for (uint32_t j = 0; j < np; j++) {
                uint32_t q = P[j];
                for (uint32_t d = 0; d <= maxgap; d++) T[d] = (uint32_t)(((uint64_t)q * d) % m);
                uint32_t r = (uint32_t)(((uint64_t)q * P[0]) % m);
                for (uint32_t i = 0; i < j; i++) {
                    if (N[r] == 0) { cov++; if (cov == ph) y_a = r; }
                    N[r] += 2;
                    r += T[P[i + 1] - P[i]]; if (r >= m) r -= m;
                }
                /* r = q*q mod m now */
                if (N[r] == 0) { cov++; if (cov == ph) y_a = r; }
                N[r] += 1;
                if (!y && cov == ph) y = q;
            }
            /* diagonal counts D[a] = #{p : p^2 = a} */
            for (uint32_t j = 0; j < np; j++) D[(uint32_t)(((uint64_t)P[j] * P[j]) % m)]++;
            /* squares of G */
            memset(sq, 0, m);
            for (uint32_t x = 1; x < m; x++) if (u[x]) sq[(uint32_t)(((uint64_t)x * x) % m)] = 1;
            double lam = (double)np * np / (double)ph;
            uint32_t mn = UINT32_MAX, amn = 0, mx = 0, amx = 0, nfail = 0, nfd = 0;
            uint32_t mnsq = UINT32_MAX, mnns = UINT32_MAX, mnsmall = UINT32_MAX, amnsmall = 0;
            double E = 0, sumsq = 0, sumns = 0; uint64_t nsq = 0;
            uint32_t b5[5], ba5[5]; int nb = 0;
            for (uint32_t a = 1; a < m; a++) {
                if (!u[a]) continue;
                uint32_t v = N[a];
                E += (double)v * v;
                if (v == 0) nfail++;
                if (v == D[a]) nfd++;
                if (v < mn) { mn = v; amn = a; }
                if (v > mx) { mx = v; amx = a; }
                if (sq[a]) { nsq++; sumsq += v; if (v < mnsq) mnsq = v; }
                else { sumns += v; if (v < mnns) mnns = v; }
                if (a <= 100 && v < mnsmall) { mnsmall = v; amnsmall = a; }
                /* keep 5 smallest */
                if (nb < 5 || v < b5[nb - 1]) {
                    int pos = (nb < 5) ? nb++ : 4;
                    while (pos > 0 && b5[pos - 1] > v) { b5[pos] = b5[pos - 1]; ba5[pos] = ba5[pos - 1]; pos--; }
                    b5[pos] = v; ba5[pos] = a;
                }
            }
            for (uint32_t j = 0; j < np; j++) D[(uint32_t)(((uint64_t)P[j] * P[j]) % m)] = 0;
            double pi = np, pi2 = pi * pi;
            double Erand = pi2 * pi2 / ph + 2 * pi2;
            double X = (E - pi2 * pi2 / ph) / (2 * pi2);
            double Rr = 1 - 2 * sqrt(log((double)ph) / lam);
            char bott[200]; int off = 0;
            for (int t = 0; t < nb; t++) off += snprintf(bott + off, sizeof(bott) - off, "%s%u", t ? ";" : "", ba5[t]);
            char *line = malloc(1024);
            snprintf(line, 1024,
                "%u,%llu,%u,%d,%d,%.6f,%.4f,%u,%u,%.6f,%.6f,%.4f,%u,%u,%.6f,%.12e,%.12e,%.8f,%.6f,%u,%u,%.6f,%.6f,"
                "%.6f,%.6f,%.6f,%.6f,%.6f,%.6f,%llu,%.6f,%u,%d,%u,%u,%s\n",
                m, (unsigned long long)ph, np, k, S.isp[m], (double)ph / m, lam, mn, amn, mn / lam, Rr,
                (lam - mn) / sqrt(2 * lam), mx, amx, mx / lam, E, Erand, E / Erand, X, y, y_a,
                (double)y / m, y / sqrt((double)m),
                N[1] / lam, N[m - 1] / lam, nsq ? sumsq / nsq / lam : 0, (ph - nsq) ? sumns / (ph - nsq) / lam : 0,
                mnsq / lam, (ph - nsq) ? mnns / lam : 0, (unsigned long long)nsq, mnsmall / lam, amnsmall,
                sq[amn], nfail, nfd, bott);
            lines[nms - 1 - idx] = line;
        }
        free(N); free(u); free(sq); free(P); free(D); free(T);
    }
    FILE *fo = fopen(out, "w");
    fprintf(fo, "m,phi,pi_m,omega,is_prime,phi_over_m,lambda,minN,argmin_a,R,R_rand,zscore_min,maxN,argmax_a,Rmax,"
                "E,E_rand,E_ratio,X_excess,y,y_a,y_over_m,y_over_sqrtm,N1_norm,Nminus1_norm,mean_sq_norm,mean_nonsq_norm,"
                "min_sq_norm,min_nonsq_norm,nsquares,min_small_norm,argmin_small,argmin_is_square,nfail,nfail_distinct,bottom5\n");
    for (size_t i = 0; i < nms; i++) fputs(lines[i], fo);
    fclose(fo);
    fprintf(stderr, "%zu moduli up to %u: %.1f s\n", nms, mmax, omp_get_wtime() - t0);
    return 0;
}
