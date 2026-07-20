#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#define MOD 1000000007LL

// Authors: Morteza Farrokhnejad, Ali Farrokhnejad
// Pattern: https://oeis.org/A001523
// NTT for optimization: https://codeforces.com/blog/entry/43499
// Cannot use given mod number for NTT directly, hence using Garner approach
// https://en.wikipedia.org/wiki/Number-theoretic_transform


static const int64_t M0 = 167772161LL;
static const int64_t M1 = 469762049LL;
static const int64_t M2 = 1224736769LL;
static const int64_t G0 = 3;
static const int64_t G1 = 3;
static const int64_t G2 = 3;

static const int64_t INV_M0_M1 = 104391568LL;   // inv(M0) mod M1
static const int64_t INV_M0M1_M2 = 721017874LL; // inv((M0*M1)%M2) mod M2

static const uint64_t MU0 = ((__uint128_t)1 << 64) / M0;
static const uint64_t MU1 = ((__uint128_t)1 << 64) / M1;
static const uint64_t MU2 = ((__uint128_t)1 << 64) / M2;
static const uint64_t MU_MOD = ((__uint128_t)1 << 64) / MOD;

static int64_t mul_mod(int64_t a, int64_t b, int64_t mod, uint64_t mu) {
    __uint128_t x = (__uint128_t)(uint64_t)a * (uint64_t)b;
    __uint128_t q = x * mu >> 64;
    int64_t r = (int64_t)(x - q * mod);
    if (r >= mod) r -= mod;
    if (r < 0) r += mod;
    return r;
}

static int64_t mod_pow(int64_t base, int64_t exp, int64_t mod, uint64_t mu) {
    int64_t res = 1 % mod;
    int64_t a = base % mod;
    if (a < 0) a += mod;
    while (exp > 0) {
        if (exp & 1) res = mul_mod(res, a, mod, mu);
        a = mul_mod(a, a, mod, mu);
        exp >>= 1;
    }
    return res;
}

static int *make_rev(int n) {
    int logn = 0;
    while ((1 << logn) < n) logn++;
    int *rev = (int *)malloc(n * sizeof(int));
    for (int i = 0; i < n; ++i) {
        int x = i;
        int y = 0;
        for (int j = 0; j < logn; ++j) {
            y = (y << 1) | (x & 1);
            x >>= 1;
        }
        rev[i] = y;
    }
    return rev;
}

static int64_t *precompute_root_pw(int n, int64_t mod, int64_t primitive_root, uint64_t mu) {
    int logn = 0;
    while ((1 << logn) < n) logn++;
    int64_t *root_pw = (int64_t *)malloc((logn + 1) * sizeof(int64_t));
    // root_pw[0] unused (length 1)
    for (int k = 1; k <= logn; ++k) {
        int len = 1 << k;
        root_pw[k] = mod_pow(primitive_root, (mod - 1) / len, mod, mu);
    }
    return root_pw;
}

static void ntt_inplace(int64_t *a, int n, int invert, int *rev,
                        int64_t mod, int64_t *root_pw, uint64_t mu) {

    for (int i = 0; i < n; ++i) {
        int j = rev[i];
        if (i < j) {
            int64_t tmp = a[i];
            a[i] = a[j];
            a[j] = tmp;
        }
    }

    int logn = 0;
    while ((1 << logn) < n) logn++;

    for (int k = 1; k <= logn; ++k) {
        int len = 1 << k;
        int half = len >> 1;
        int64_t wlen = root_pw[k];
        if (invert) wlen = mod_pow(wlen, mod - 2, mod, mu);
        for (int i = 0; i < n; i += len) {
            int64_t w = 1;
            for (int j = 0; j < half; ++j) {
                int idx1 = i + j;
                int idx2 = idx1 + half;
                int64_t u = a[idx1];
                int64_t v = mul_mod(a[idx2], w, mod, mu);
                int64_t x = u + v;
                if (x >= mod) x -= mod;
                int64_t y = u - v;
                if (y < 0) y += mod;
                a[idx1] = x;
                a[idx2] = y;
                w = mul_mod(w, wlen, mod, mu);
            }
        }
    }

    if (invert) {
        int64_t inv_n = mod_pow(n, mod - 2, mod, mu);
        for (int i = 0; i < n; ++i) a[i] = mul_mod(a[i], inv_n, mod, mu);
    }
}

static void convolution_three(int64_t *a, int na, int64_t *b, int nb,
                              int64_t **out0, int64_t **out1, int64_t **out2, int *out_len) {
    int need = na + nb - 1;
    int n = 1;
    while (n < need) n <<= 1;

    int64_t *fa0 = (int64_t *)calloc(n, sizeof(int64_t));
    int64_t *fa1 = (int64_t *)calloc(n, sizeof(int64_t));
    int64_t *fa2 = (int64_t *)calloc(n, sizeof(int64_t));


    for (int i = 0; i < na; ++i) {
        int64_t v = a[i] % M0; if (v < 0) v += M0; fa0[i] = v;
        v = a[i] % M1; if (v < 0) v += M1; fa1[i] = v;
        v = a[i] % M2; if (v < 0) v += M2; fa2[i] = v;
    }
    for (int i = na; i < n; ++i) { fa0[i] = fa1[i] = fa2[i] = 0; }

    int64_t *fb0 = (int64_t *)calloc(n, sizeof(int64_t));
    int64_t *fb1 = (int64_t *)calloc(n, sizeof(int64_t));
    int64_t *fb2 = (int64_t *)calloc(n, sizeof(int64_t));
    for (int i = 0; i < nb; ++i) {
        int64_t v = b[i] % M0; if (v < 0) v += M0; fb0[i] = v;
        v = b[i] % M1; if (v < 0) v += M1; fb1[i] = v;
        v = b[i] % M2; if (v < 0) v += M2; fb2[i] = v;
    }
    for (int i = nb; i < n; ++i) { fb0[i] = fb1[i] = fb2[i] = 0; }

    int *rev = make_rev(n);

    int64_t *root0 = precompute_root_pw(n, M0, G0, MU0);
    int64_t *root1 = precompute_root_pw(n, M1, G1, MU1);
    int64_t *root2 = precompute_root_pw(n, M2, G2, MU2);

    ntt_inplace(fa0, n, 0, rev, M0, root0, MU0);
    if (a != b) {
        ntt_inplace(fb0, n, 0, rev, M0, root0, MU0);
        for (int i = 0; i < n; ++i) {
            fa0[i] = mul_mod(fa0[i], fb0[i], M0, MU0);
        }
    } else {
        for (int i = 0; i < n; ++i) {
            fa0[i] = mul_mod(fa0[i], fa0[i], M0, MU0);
        }
    }
    ntt_inplace(fa0, n, 1, rev, M0, root0, MU0);

    ntt_inplace(fa1, n, 0, rev, M1, root1, MU1);
    if (a != b) {
        ntt_inplace(fb1, n, 0, rev, M1, root1, MU1);
        for (int i = 0; i < n; ++i) {
            fa1[i] = mul_mod(fa1[i], fb1[i], M1, MU1);
        }
    } else {
        for (int i = 0; i < n; ++i) {
            fa1[i] = mul_mod(fa1[i], fa1[i], M1, MU1);
        }
    }
    ntt_inplace(fa1, n, 1, rev, M1, root1, MU1);

    ntt_inplace(fa2, n, 0, rev, M2, root2, MU2);
    if (a != b) {
        ntt_inplace(fb2, n, 0, rev, M2, root2, MU2);
        for (int i = 0; i < n; ++i) {
            fa2[i] = mul_mod(fa2[i], fb2[i], M2, MU2);
        }
    } else {
        for (int i = 0; i < n; ++i) {
            fa2[i] = mul_mod(fa2[i], fa2[i], M2, MU2);
        }
    }
    ntt_inplace(fa2, n, 1, rev, M2, root2, MU2);

    int64_t *res0 = (int64_t *)malloc(need * sizeof(int64_t));
    int64_t *res1 = (int64_t *)malloc(need * sizeof(int64_t));
    int64_t *res2 = (int64_t *)malloc(need * sizeof(int64_t));

    for (int i = 0; i < need; ++i) {
        res0[i] = fa0[i];
        res1[i] = fa1[i];
        res2[i] = fa2[i];
    }

 
    free(fa0); free(fa1); free(fa2);
    free(fb0); free(fb1); free(fb2);
    free(rev); free(root0); free(root1); free(root2);

    *out0 = res0; *out1 = res1; *out2 = res2; *out_len = need;
}

static inline int64_t garner3(int64_t r0, int64_t r1, int64_t r2) {
    int64_t diff = (r1 - r0) % M1;
    if (diff < 0) diff += M1;
    int64_t t1 = mul_mod(diff, INV_M0_M1, M1, MU1);

    int64_t temp = mul_mod(M0, t1, M2, MU2);
    int64_t x0_mod_m2 = (r0 + temp) % M2;
    if (x0_mod_m2 < 0) x0_mod_m2 += M2;

    diff = (r2 - x0_mod_m2) % M2;
    if (diff < 0) diff += M2;
    int64_t t2 = mul_mod(diff, INV_M0M1_M2, M2, MU2);

    int64_t part1 = mul_mod(M0, t1, MOD, MU_MOD);
    int64_t m1_t2 = mul_mod(M1, t2, MOD, MU_MOD);
    int64_t part2 = mul_mod(M0, m1_t2, MOD, MU_MOD);

    int64_t result = (r0 + part1) % MOD;
    result = (result + part2) % MOD;
    if (result < 0) result += MOD;
    return result;
}

int main() {
    int cases;
    if (scanf("%d", &cases) != 1) return 0;

    int max_pents = 0;
    for (int k = 1;; ++k) {
        int p1 = (3*k*k - k)/2;
        if (p1 > cases) break;
        ++max_pents;
        int p2 = (3*k*k + k)/2;
        if (p2 <= cases) ++max_pents;
    }

    int *pnums = (int *)malloc(max_pents * sizeof(int));
    int *psigns = (int *)malloc(max_pents * sizeof(int));
    int idx = 0;
    for (int k = 1;; ++k) {
        int p1 = (3*k*k - k)/2;
        if (p1 > cases) break;
        pnums[idx] = p1;
        psigns[idx] = (k % 2 == 1) ? 1 : -1;
        idx++;
        int p2 = (3*k*k + k)/2;
        if (p2 <= cases) {
            pnums[idx] = p2;
            psigns[idx] = (k % 2 == 1) ? 1 : -1;
            idx++;
        }
    }
    max_pents = idx;

    int n_p = cases + 1;
    int64_t *pents = (int64_t *)calloc(n_p, sizeof(int64_t));
    pents[0] = 1;
    for (int num = 1; num <= cases; ++num) {
        int64_t count = 0;
        for (int i = 0; i < max_pents && pnums[i] <= num; ++i) {
            count += (int64_t)psigns[i] * pents[num - pnums[i]];
        }
        count %= MOD;
        if (count < 0) count += MOD;
        pents[num] = count;
    }

    int64_t *conv0 = NULL, *conv1 = NULL, *conv2 = NULL;
    int conv_len = 0;
    convolution_three(pents, n_p, pents, n_p, &conv0, &conv1, &conv2, &conv_len);

    int need = conv_len; 
    int64_t *c = (int64_t *)malloc(need * sizeof(int64_t));
    for (int i = 0; i < need; ++i) {
        c[i] = garner3(conv0[i], conv1[i], conv2[i]);
    }

    free(conv0); free(conv1); free(conv2);

    int max_m = (int)((-1 + sqrt(1 + 8.0 * cases)) / 2) + 2;

    int64_t *d = (int64_t *)calloc(cases + 1, sizeof(int64_t));
    for (int m = 1; m <= max_m; ++m) {
        int x = m * (m + 1) / 2;
        if (x > cases) break;
        d[x] = (m % 2 == 0) ? (MOD - 1LL) : 1LL;
    }

    int64_t *res0 = NULL, *res1 = NULL, *res2 = NULL;
    int res_len = 0;
    convolution_three(d, cases + 1, c, need, &res0, &res1, &res2, &res_len);

    int64_t *res = (int64_t *)malloc((cases + 1) * sizeof(int64_t));
    for (int i = 0; i <= cases; ++i) {
        res[i] = garner3(res0[i], res1[i], res2[i]);
    }

    for (int i = 1; i <= cases; ++i) {
        if (i > 1) putchar(' ');
        printf("%lld", (long long)(res[i]));
    }
    putchar('\n');

    free(pnums); free(psigns); free(pents); free(c); free(res); free(d); free(res0); free(res1); free(res2);
    return 0;
}