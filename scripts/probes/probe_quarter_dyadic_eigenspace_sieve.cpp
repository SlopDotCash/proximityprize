// Exhaustive 8-generator cyclotomic-unit sieve for the sole constant-phase s = 1
// antipodal opposite-parity pair (d1 = 7, d2 = 6) on mu_64 (7 same-parity roots in mu_32).
//
// Runs at both independent primes MOD = 101 and MOD = 103, verifies exact orbit sum
// C(32, 7) = 3,365,856 across all 6,903 orbits, and certifies 0 ternary solutions.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <unordered_set>
#include <vector>

using namespace std;

static constexpr int N = 32;
static constexpr int U = 8;

static int modpow(long long a, long long e, int m) {
    long long r = 1;
    a %= m;
    if (a < 0) a += m;
    while (e > 0) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return static_cast<int>(r);
}

static int EXPS[N][U];

static void init_exps() {
    memset(EXPS, 0, sizeof(EXPS));
    for (int d = 1; d < N; ++d) {
        int mult = d & -d;
        int u = d / mult;
        int step = N / mult;
        for (int j = 0; j < mult; ++j) {
            int r = (u + j * step) % N;
            int rep = min(r, N - r);
            EXPS[d][(rep - 1) / 2] += 1;
        }
    }
}

static uint32_t canon7(const int C[7], int& orbit_size) {
    uint32_t best = ~0U;
    uint32_t imgs[512];
    int ni = 0;
    for (int shift = 0; shift < N; ++shift) {
        for (int k = 1; k < N; k += 2) {
            uint32_t m = 0;
            for (int i = 0; i < 7; ++i) {
                int v = ((C[i] - shift + N) * k) & (N - 1);
                m |= (1U << v);
            }
            if (m < best) best = m;
            imgs[ni++] = m;
        }
    }
    sort(imgs, imgs + ni);
    orbit_size = static_cast<int>(unique(imgs, imgs + ni) - imgs);
    return best;
}

static void run_mod(int MOD) {
    int INV[256] = {0};
    for (int i = 1; i < MOD; ++i) INV[i] = modpow(i, MOD - 2, MOD);

    unordered_set<uint32_t> seen;
    seen.reserve(10000);
    vector<array<int, 7>> reps;
    long long orbit_sum = 0;
    int C[7];
    C[0] = 0;
    for (int a = 1; a < N; ++a)
    for (int b = a + 1; b < N; ++b)
    for (int c = b + 1; c < N; ++c)
    for (int d = c + 1; d < N; ++d)
    for (int e = d + 1; e < N; ++e)
    for (int f = e + 1; f < N; ++f) {
        C[1] = a; C[2] = b; C[3] = c; C[4] = d; C[5] = e; C[6] = f;
        int osz = 0;
        uint32_t key = canon7(C, osz);
        if (seen.insert(key).second) {
            reps.push_back({C[0], C[1], C[2], C[3], C[4], C[5], C[6]});
            orbit_sum += osz;
        }
    }
    assert(orbit_sum == 3365856LL);  // C(32, 7)
    assert(reps.size() == 6903ULL);

    long long ternary_hits = 0;
    int max_nullity = 0;
    for (const auto& rep : reps) {
        uint32_t cmask = 0;
        for (int i = 0; i < 7; ++i) cmask |= (1U << rep[i]);
        int sites[25], ns = 0;
        for (int z = 0; z < N; ++z) if (!(cmask & (1U << z))) sites[ns++] = z;

        int M[49][26], nr = 0;
        for (int i = 1; i < 7; ++i) {
            for (int u = 0; u < U; ++u) {
                for (int j = 0; j < ns; ++j) {
                    int d1 = (rep[i] - sites[j] + N) & (N - 1);
                    int d0 = (rep[0] - sites[j] + N) & (N - 1);
                    int diff = (EXPS[d1][u] - EXPS[d0][u]) % MOD;
                    if (diff < 0) diff += MOD;
                    M[nr][j] = diff;
                }
                M[nr][ns] = 0;
                nr++;
            }
        }
        for (int j = 0; j < ns; ++j) M[nr][j] = 1;
        M[nr][ns] = 1;  // |A| - |B| = 7 - 6 = 1
        nr++;

        int piv_col[25], free_col[25], np = 0, nf = 0;
        for (int col = 0; col < ns; ++col) {
            int piv = -1;
            for (int r = np; r < nr; ++r) if (M[r][col] != 0) { piv = r; break; }
            if (piv == -1) { free_col[nf++] = col; continue; }
            if (piv != np) for (int j = col; j <= ns; ++j) swap(M[np][j], M[piv][j]);
            int inv = INV[M[np][col]];
            for (int j = col; j <= ns; ++j) M[np][j] = M[np][j] * inv % MOD;
            for (int r = 0; r < nr; ++r) if (r != np && M[r][col] != 0) {
                int f = M[r][col];
                for (int j = col; j <= ns; ++j) {
                    int v = (M[r][j] - f * M[np][j]) % MOD;
                    if (v < 0) v += MOD;
                    M[r][j] = v;
                }
            }
            piv_col[np++] = col;
        }
        bool incons = false;
        for (int r = np; r < nr; ++r) if (M[r][ns] != 0) { incons = true; break; }
        if (incons) continue;
        if (nf > max_nullity) max_nullity = nf;
        assert(nf <= 6);

        int total3 = 1;
        for (int i = 0; i < nf; ++i) total3 *= 3;
        int fval[6];
        for (int idx = 0; idx < total3; ++idx) {
            int tmp = idx;
            for (int i = 0; i < nf; ++i) {
                int d = tmp % 3;
                tmp /= 3;
                fval[i] = (d == 0 ? 0 : (d == 1 ? 1 : -1));
            }
            bool ok = true;
            for (int r = 0; r < np; ++r) {
                int s = M[r][ns];
                for (int i = 0; i < nf; ++i) {
                    if (fval[i] == 1) s -= M[r][free_col[i]];
                    else if (fval[i] == -1) s += M[r][free_col[i]];
                }
                s %= MOD;
                if (s < 0) s += MOD;
                if (s != 0 && s != 1 && s != MOD - 1) { ok = false; break; }
            }
            if (ok) ternary_hits++;
        }
    }
    assert(ternary_hits == 0);
    cout << "s=1 (7,6) MOD=" << MOD
         << " reps=" << reps.size()
         << " orbit_sum=" << orbit_sum
         << " max_nullity=" << max_nullity
         << " ternary_hits=" << ternary_hits << endl;
}

int main() {
    init_exps();
    run_mod(101);
    run_mod(103);
    return 0;
}
