// Exhaustive 16-generator cyclotomic-unit sieve for anti-invariant degree-15 reflections
// on mu_64: P(z) = (z+1) z^7 U(z+1/z), Q(z) = (z-1) z^7 V(z+1/z).
// Runs at both MOD = 101 and MOD = 103 across all 47,251 Galois orbits of 6-subsets in {1..31}
// (verified orbit sum C(31, 6) = 736,281), certifying 0 consistent systems.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <unordered_set>
#include <vector>

using namespace std;

static constexpr int N = 64;
static constexpr int U = 16;

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
        int mult = d & -d, u = d / mult, step = N / mult;
        for (int j = 0; j < mult; ++j) {
            int r = (u + j * step) % N;
            EXPS[d][(min(r, N - r) - 1) / 2] += 1;
        }
    }
}

static uint64_t canon_even(const int C[6], int& osz) {
    uint64_t best = ~0ULL;
    uint64_t imgs[16];
    int ni = 0;
    for (int k = 1; k < 32; k += 2) {
        uint64_t mask = 0;
        for (int i = 0; i < 6; ++i) {
            int r = (C[i] * k) & 63;
            mask |= (1ULL << min(r, 64 - r));
        }
        if (mask < best) best = mask;
        imgs[ni++] = mask;
    }
    sort(imgs, imgs + ni);
    osz = static_cast<int>(unique(imgs, imgs + ni) - imgs);
    return best;
}

static void run_mod(int MOD) {
    int INV[256] = {0};
    for (int i = 1; i < MOD; ++i) INV[i] = modpow(i, MOD - 2, MOD);
    int EXP_MAT[32][32][U], COT[32][U];
    memset(EXP_MAT, 0, sizeof(EXP_MAT));
    for (int i = 1; i <= 31; ++i) {
        for (int u = 0; u < U; ++u) COT[i][u] = EXPS[(i + 32) & 63][u] - EXPS[i][u];
        for (int j = 1; j <= 31; ++j) {
            if (i == j) continue;
            int d1 = (i - j + 64) & 63, d2 = (i + j) & 63;
            for (int u = 0; u < U; ++u) EXP_MAT[i][j][u] = EXPS[d1][u] + EXPS[d2][u];
        }
    }

    unordered_set<uint64_t> seen;
    seen.reserve(60000);
    vector<array<int, 6>> reps;
    long long orbit_sum = 0;
    int C[6];
    for (int a = 1; a <= 31; ++a)
    for (int b = a + 1; b <= 31; ++b)
    for (int c = b + 1; c <= 31; ++c)
    for (int d = c + 1; d <= 31; ++d)
    for (int e = d + 1; e <= 31; ++e)
    for (int f = e + 1; f <= 31; ++f) {
        C[0] = a; C[1] = b; C[2] = c; C[3] = d; C[4] = e; C[5] = f;
        int osz = 0;
        if (seen.insert(canon_even(C, osz)).second) {
            reps.push_back({a, b, c, d, e, f});
            orbit_sum += osz;
        }
    }
    assert(orbit_sum == 736281LL);  // C(31, 6)
    assert(reps.size() == 47251ULL);

    long long consistent = 0;
    for (const auto& rep : reps) {
        uint64_t cm = 0;
        for (int i = 0; i < 6; ++i) cm |= (1ULL << rep[i]);
        int sites[25], ns = 0;
        for (int z = 1; z <= 31; ++z) if (!(cm & (1ULL << z))) sites[ns++] = z;

        int M[81][26], nr = 0;
        for (int i = 1; i < 6; ++i) {
            for (int u = 0; u < U; ++u) {
                for (int j = 0; j < ns; ++j) {
                    int v = (EXP_MAT[rep[i]][sites[j]][u] - EXP_MAT[rep[0]][sites[j]][u]) % MOD;
                    if (v < 0) v += MOD;
                    M[nr][j] = v;
                }
                int rhs = (-(COT[rep[i]][u] - COT[rep[0]][u])) % MOD;
                if (rhs < 0) rhs += MOD;
                M[nr][ns] = rhs;
                nr++;
            }
        }
        for (int j = 0; j < ns; ++j) M[nr][j] = 1;
        M[nr][ns] = 0;
        nr++;

        int np = 0;
        for (int col = 0; col < ns; ++col) {
            int piv = -1;
            for (int r = np; r < nr; ++r) if (M[r][col] != 0) { piv = r; break; }
            if (piv == -1) continue;
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
            np++;
        }
        bool incons = false;
        for (int r = np; r < nr; ++r) if (M[r][ns] != 0) { incons = true; break; }
        if (!incons) consistent++;
    }
    assert(consistent == 0);
    cout << "Anti-deg15 MOD=" << MOD
         << " reps=" << reps.size()
         << " orbit_sum=" << orbit_sum
         << " consistent=" << consistent << endl;
}

int main() {
    init_exps();
    run_mod(101);
    run_mod(103);
    return 0;
}
