/*
 * eos_char: for prime m, compute all character sums S(chi) = sum_{p < m} chi(p) at once.
 * Write G = <g>, f[k] = 1 if g^k is prime (k = 0..m-2). The DFT F[j] = sum_k f[k] e(-jk/(m-1)) equals
 * S(chi_j), with chi_j(g^k) = e(-jk/(m-1)), so a single FFT gives every S(chi).
 * Then N(g^k) = (f * f)[k] (cyclic convolution) = IFFT(F^2), so R(m) is available for large prime m.
 *
 * Outputs per m: pi, max_{chi != chi0} |S(chi)|, its order, |S(quadratic)|, the energy E = (1/phi) sum |S|^4,
 * the excess X = (E - pi^4/phi) / (2 pi^2), min N, argmin, R(m), N(1), N(-1), and square / non-square means.
 *
 * usage: eos_char primes.txt out.csv
 */
#include "common.h"
#include <omp.h>
#include <complex.h>
#include <fftw3.h>

static uint64_t powmod(uint64_t b, uint64_t e, uint64_t m) {
    uint64_t r = 1; b %= m;
    while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static uint64_t gcd64(uint64_t a, uint64_t b) { while (b) { uint64_t t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s primes.txt out.csv\n", argv[0]); return 1; }
    FILE *fi = fopen(argv[1], "r");
    size_t cap = 1024, nms = 0; uint32_t *ms = malloc(cap * 4); unsigned long v;
    while (fscanf(fi, "%lu", &v) == 1) { if (nms == cap) { cap *= 2; ms = realloc(ms, cap * 4); } ms[nms++] = (uint32_t)v; }
    fclose(fi);
    uint32_t mmax = 0; for (size_t i = 0; i < nms; i++) if (ms[i] > mmax) mmax = ms[i];
    sieve_t S; sieve_init(&S, mmax + 1);
    char **lines = calloc(nms, sizeof(char *));
    double t0 = omp_get_wtime();
#pragma omp parallel for schedule(dynamic, 1)
    for (size_t idx = 0; idx < nms; idx++) {
        uint32_t m = ms[idx];
        if (m < 5 || !S.isp[m]) continue;
        uint32_t n = m - 1;
        uint32_t f[16]; int k = factor_distinct(&S, n, f);
        uint32_t g = 2;
        for (;; g++) {
            int ok = 1;
            for (int i = 0; i < k; i++) if (powmod(g, n / f[i], m) == 1) { ok = 0; break; }
            if (ok) break;
        }
        double *x = fftw_malloc(sizeof(double) * n);
        fftw_complex *F = fftw_malloc(sizeof(fftw_complex) * (n / 2 + 1));
        fftw_plan pf, pb;
#pragma omp critical(plan)
        {
            pf = fftw_plan_dft_r2c_1d(n, x, F, FFTW_ESTIMATE);
            pb = fftw_plan_dft_c2r_1d(n, F, x, FFTW_ESTIMATE);
        }
        uint32_t smallind[101]; for (int i = 0; i <= 100; i++) smallind[i] = UINT32_MAX;
        uint64_t y = 1; uint32_t pi = 0;
        for (uint32_t t = 0; t < n; t++) {
            x[t] = S.isp[y] ? 1.0 : 0.0; pi += S.isp[y];
            if (y <= 100) smallind[y] = t;
            y = y * g % m;
        }
        fftw_execute(pf);
        double maxS = 0, E = 0, sum2 = 0; uint32_t jmax = 0;
        for (uint32_t j = 0; j <= n / 2; j++) {
            double a2 = creal(F[j]) * creal(F[j]) + cimag(F[j]) * cimag(F[j]);
            double w = (j == 0 || 2 * j == n) ? 1 : 2;
            E += w * a2 * a2;
            if (j) { sum2 += w * a2; if (a2 > maxS) { maxS = a2; jmax = j; } }
        }
        E /= n;
        double quad = cabs(F[n / 2]);
        double reS_quad = creal(F[n / 2]);
        /* second largest |S| among nontrivial, excluding conj pair of jmax */
        double max2 = 0;
        for (uint32_t j = 1; j <= n / 2; j++) {
            if (j == jmax) continue;
            double a2 = creal(F[j]) * creal(F[j]) + cimag(F[j]) * cimag(F[j]);
            if (a2 > max2) max2 = a2;
        }
        /* distribution: count |S|^2/pi > t for t = 5, 10 */
        uint64_t c5 = 0, c10 = 0;
        for (uint32_t j = 1; j <= n / 2; j++) {
            double a2 = (creal(F[j]) * creal(F[j]) + cimag(F[j]) * cimag(F[j])) / pi;
            double w = (2 * j == n) ? 1 : 2;
            if (a2 > 5) c5 += w;
            if (a2 > 10) c10 += w;
        }
        for (uint32_t j = 0; j <= n / 2; j++) F[j] = F[j] * F[j];
        fftw_execute(pb);
        double lam = (double)pi * pi / n;
        double mn = 1e300, sumN = 0, sse = 0, sq = 0, ns = 0; uint32_t kmn = 0;
        double maxround = 0;
        for (uint32_t t = 0; t < n; t++) {
            double val = x[t] / n, rv = floor(val + 0.5);
            if (fabs(val - rv) > maxround) maxround = fabs(val - rv);
            sumN += rv; sse += (rv - lam) * (rv - lam);
            if (t % 2 == 0) sq += rv; else ns += rv;
            if (rv < mn) { mn = rv; kmn = t; }
        }
        double N1 = floor(x[0] / n + 0.5), Nm1 = floor(x[n / 2] / n + 0.5);
        double mnsmall = 1e300; uint32_t amnsmall = 0;
        for (int a = 1; a <= 100 && a < (int)m; a++) {
            double val = floor(x[smallind[a]] / n + 0.5);
            if (val < mnsmall) { mnsmall = val; amnsmall = a; }
        }
        uint64_t amn = powmod(g, kmn, m);
        uint64_t ordmax = n / gcd64(jmax, n);
        double pi2 = (double)pi * pi;
        double X = (E - pi2 * pi2 / n) / (2 * pi2);
        char *line = malloc(1024);
        snprintf(line, 1024,
            "%u,%u,%u,%.6f,%.6f,%llu,%.6f,%.6f,%.6f,%.6f,%.6f,%llu,%llu,%.8e,%.6f,%.6f,%.0f,%llu,%d,%.6f,%.6f,%.6f,%.6f,%.6f,%.6f,%u,%.3e,%.0f\n",
            m, g, pi, sqrt(maxS) / sqrt((double)pi), sqrt(maxS) / (sqrt((double)m) * log((double)m)),
            (unsigned long long)ordmax, sqrt(max2) / sqrt((double)pi), quad / sqrt((double)pi), reS_quad / sqrt((double)pi),
            maxS / pi / log((double)n), sum2 / (n - 1) / pi, (unsigned long long)c5, (unsigned long long)c10,
            E, E / (pi2 * pi2 / n + 2 * pi2), X, mn, (unsigned long long)amn, (int)(kmn % 2 == 0), mn / lam,
            1 - 2 * sqrt(log((double)n) / lam), (lam - mn) / sqrt(2 * lam), N1 / lam, Nm1 / lam,
            mnsmall / lam, amnsmall, maxround, sumN - pi2);
        lines[idx] = line;
        (void)sq; (void)ns; (void)sse;
#pragma omp critical(plan)
        { fftw_destroy_plan(pf); fftw_destroy_plan(pb); }
        fftw_free(x); fftw_free(F);
    }
    FILE *fo = fopen(argv[2], "w");
    fprintf(fo, "m,g,pi,maxS_over_sqrtpi,maxS_over_sqrtm_logm,order_of_max_chi,second_max_over_sqrtpi,abs_S_quad_over_sqrtpi,"
                "S_quad_over_sqrtpi,maxS2_over_pi_logphi,mean_S2_over_pi,count_S2_gt_5pi,count_S2_gt_10pi,"
                "E,E_ratio,X_excess,minN,argmin_a,argmin_is_square,R,R_rand,zscore_min,N1_norm,Nminus1_norm,"
                "min_small_norm,argmin_small,max_round_err,sumN_minus_pi2\n");
    for (size_t i = 0; i < nms; i++) if (lines[i]) fputs(lines[i], fo);
    fclose(fo);
    fprintf(stderr, "%zu primes up to %u: %.1f s\n", nms, mmax, omp_get_wtime() - t0);
    return 0;
}
