/*
 * eos_cover: for every m in [m0, m1], and every reduced class a mod m, search primes p <= m
 * (p not dividing m) in increasing order for one with  q := a * p^{-1} mod m  prime (q in [2, m-1]).
 * Since q is determined mod m and q <= m, this decides EOS for (m, a) exactly
 * (reformulation 2 in notes/00-setup.md).
 *
 * Per m it records:
 *   nfail      #classes a with no pq = a, p, q <= m
 *   nfail_dist #classes a with no pq = a with p != q  (the "p < q" variant)
 *   z          max over a of the least p that works (so theta(m) = log z / log m is the least theta
 *              with {p <= m^theta} x {q <= m} covering all classes)
 * The variants "p,q < m" and "p <= q" are provably identical to the base problem
 * (p = m forces p | m; pq = qp), so they are not computed separately.
 *
 * usage: eos_cover m0 m1 out.csv fails.csv
 */
#include "common.h"
#include <omp.h>

typedef struct { uint32_t m, a, variant; } fail_t;

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: %s m0 m1 out.csv fails.csv\n", argv[0]); return 1; }
    uint32_t m0 = (uint32_t)atol(argv[1]), m1 = (uint32_t)atol(argv[2]);
    if (m0 < 2) m0 = 2;
    sieve_t S; sieve_init(&S, m1 + 1);
    uint32_t nm = m1 - m0 + 1;
    uint32_t *r_phi = calloc(nm, 4), *r_pi = calloc(nm, 4), *r_nf = calloc(nm, 4), *r_nfd = calloc(nm, 4);
    uint32_t *r_z = calloc(nm, 4), *r_za = calloc(nm, 4), *r_zq = calloc(nm, 4);
    double *r_meanz = calloc(nm, 8);
    fail_t *fails = NULL; size_t nfails = 0, capf = 0;
    double t0 = omp_get_wtime();

#pragma omp parallel
    {
        uint8_t *u = malloc(m1 + 2);
        uint32_t npr_all = S.npr;
        uint32_t *pinv = malloc((size_t)npr_all * 4), *stamp = calloc(npr_all, 4);
        fail_t *lf = NULL; size_t nlf = 0, caplf = 0;
#pragma omp for schedule(dynamic, 16)
        for (uint32_t m = m0; m <= m1; m++) {
            uint32_t f[16]; int k = factor_distinct(&S, m, f);
            uint64_t ph = euler_phi(m, f, k);
            unit_mask(u, m, f, k);
            uint32_t np = S.picnt[m];           /* primes <= m */
            uint32_t pim = np - (uint32_t)k;      /* all prime divisors of m are <= m */
            uint32_t nf = 0, nfd = 0, z = 0, za = 0, zq = 0;
            double sumz = 0;
            for (uint32_t a = 1; a < m; a++) {
                if (!u[a]) continue;
                uint32_t first = 0, firstq = 0; int dist = 0;
                for (uint32_t j = 0; j < np; j++) {
                    uint32_t p = S.pr[j];
                    if (!u[p % m]) continue;
                    if (stamp[j] != m) { stamp[j] = m; pinv[j] = modinv(p, m); }
                    uint32_t q = (uint32_t)(((uint64_t)a * pinv[j]) % m);
                    if (S.isp[q]) {
                        if (!first) { first = p; firstq = q; }
                        if (q != p) { dist = 1; break; }
                    }
                }
                if (!first) {
                    nf++;
                    if (nlf == caplf) { caplf = caplf ? 2 * caplf : 64; lf = realloc(lf, caplf * sizeof(fail_t)); }
                    lf[nlf++] = (fail_t){m, a, 0};
                } else {
                    sumz += log((double)first);
                    if (first > z) { z = first; za = a; zq = firstq; }
                }
                if (!dist) {
                    nfd++;
                    if (first) { /* fails only in the distinct variant */
                        if (nlf == caplf) { caplf = caplf ? 2 * caplf : 64; lf = realloc(lf, caplf * sizeof(fail_t)); }
                        lf[nlf++] = (fail_t){m, a, 1};
                    }
                }
            }
            uint32_t i = m - m0;
            r_phi[i] = (uint32_t)ph; r_pi[i] = pim; r_nf[i] = nf; r_nfd[i] = nfd;
            r_z[i] = z; r_za[i] = za; r_zq[i] = zq;
            r_meanz[i] = (ph > nf) ? sumz / (double)(ph - nf) : 0;
        }
#pragma omp critical
        {
            if (nfails + nlf > capf) { capf = nfails + nlf + 1024; fails = realloc(fails, capf * sizeof(fail_t)); }
            memcpy(fails + nfails, lf, nlf * sizeof(fail_t)); nfails += nlf;
        }
        free(u); free(pinv); free(stamp); free(lf);
    }
    double t1 = omp_get_wtime();
    FILE *fo = fopen(argv[3], "w");
    fprintf(fo, "m,phi,pi_m,nfail,nfail_distinct,z,z_a,z_q,theta,mean_log_first_p\n");
    for (uint32_t i = 0; i < nm; i++) {
        uint32_t m = m0 + i;
        double th = (r_z[i] > 1) ? log((double)r_z[i]) / log((double)m) : 0;
        fprintf(fo, "%u,%u,%u,%u,%u,%u,%u,%u,%.6f,%.5f\n", m, r_phi[i], r_pi[i], r_nf[i], r_nfd[i],
                r_z[i], r_za[i], r_zq[i], th, r_meanz[i]);
    }
    fclose(fo);
    /* sort fails by (m, variant, a) */
    int cmp(const void *x, const void *y);
    qsort(fails, nfails, sizeof(fail_t), cmp);
    FILE *ff = fopen(argv[4], "w");
    fprintf(ff, "m,a,variant\n");
    for (size_t i = 0; i < nfails; i++)
        fprintf(ff, "%u,%u,%s\n", fails[i].m, fails[i].a, fails[i].variant ? "distinct_only" : "all");
    fclose(ff);
    fprintf(stderr, "m in [%u,%u]: %.1f s, %zu fail records\n", m0, m1, t1 - t0, nfails);
    return 0;
}
int cmp(const void *x, const void *y) {
    const fail_t *a = x, *b = y;
    if (a->m != b->m) return a->m < b->m ? -1 : 1;
    if (a->variant != b->variant) return a->variant < b->variant ? -1 : 1;
    return a->a < b->a ? -1 : (a->a > b->a);
}
