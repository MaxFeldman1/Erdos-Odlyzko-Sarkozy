/* Shared helpers: sieve, factorisation via smallest-prime-factor table, modular inverse. */
#ifndef EOS_COMMON_H
#define EOS_COMMON_H
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

typedef struct {
    uint32_t N;        /* sieve limit (inclusive) */
    uint32_t *spf;     /* smallest prime factor, spf[0]=spf[1]=0 */
    uint8_t  *isp;     /* isp[n] = 1 iff n prime */
    uint32_t *pr;      /* primes in increasing order */
    uint32_t npr;
    uint32_t *picnt;   /* picnt[n] = #primes <= n */
} sieve_t;

static void sieve_init(sieve_t *S, uint32_t N) {
    S->N = N;
    S->spf = calloc((size_t)N + 1, sizeof(uint32_t));
    S->isp = calloc((size_t)N + 1, 1);
    S->picnt = calloc((size_t)N + 1, sizeof(uint32_t));
    uint32_t cap = (uint32_t)(1.3 * N / (log((double)N + 2) - 1.1) + 100);
    S->pr = malloc((size_t)cap * sizeof(uint32_t));
    S->npr = 0;
    for (uint32_t i = 2; i <= N; i++) {
        if (S->spf[i] == 0) { S->spf[i] = i; S->isp[i] = 1; S->pr[S->npr++] = i; }
        for (uint32_t j = 0; j < S->npr; j++) {
            uint32_t p = S->pr[j];
            uint64_t ip = (uint64_t)i * p;
            if (p > S->spf[i] || ip > N) break;
            S->spf[ip] = p;
        }
    }
    uint32_t c = 0;
    for (uint32_t i = 0; i <= N; i++) { if (S->isp[i]) c++; S->picnt[i] = c; }
}

/* distinct prime factors of m, returns count */
static int factor_distinct(const sieve_t *S, uint32_t m, uint32_t *f) {
    int k = 0;
    while (m > 1) {
        uint32_t p = S->spf[m];
        f[k++] = p;
        while (m % p == 0) m /= p;
    }
    return k;
}

static uint64_t euler_phi(uint32_t m, const uint32_t *f, int k) {
    uint64_t ph = m;
    for (int i = 0; i < k; i++) ph = ph / f[i] * (f[i] - 1);
    return ph;
}

/* inverse of a mod m, gcd(a,m)=1 assumed */
static uint32_t modinv(uint32_t a, uint32_t m) {
    int64_t t = 0, nt = 1, r = m, nr = a % m;
    while (nr) {
        int64_t q = r / nr, tmp;
        tmp = t - q * nt; t = nt; nt = tmp;
        tmp = r - q * nr; r = nr; nr = tmp;
    }
    if (t < 0) t += m;
    return (uint32_t)t;
}

/* unit mask: u[a]=1 iff gcd(a,m)=1, for 0<=a<m */
static void unit_mask(uint8_t *u, uint32_t m, const uint32_t *f, int k) {
    memset(u, 1, m);
    u[0] = (m == 1);
    for (int i = 0; i < k; i++)
        for (uint32_t x = 0; x < m; x += f[i]) u[x] = 0;
}
#endif
