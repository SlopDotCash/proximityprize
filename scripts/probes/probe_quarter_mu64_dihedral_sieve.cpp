// Exhaustive characteristic-zero 16-unit cyclotomic rank sieve for mu_64 dihedral
// reflection pullbacks (both odd c = zeta_64 and even c = 1) at degree 7.
//
// Companion to scripts/probes/probe_quarter_mu64_dihedral_sieve.py.
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
static constexpr int U = 16;     // 16 odd cyclotomic generators |1 - zeta_64^{2k+1}|
static constexpr int FMOD = 65537;

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
            int r_rep = min(r, N - r);
            EXPS[d][(r_rep - 1) / 2] += 1;
        }
    }
}

static uint64_t canon_odd(const int C[6], int& orbit_size) {
    uint64_t best = ~0ULL;
    uint64_t images[32];
    int n_img = 0;
    for (int k = 1; k < 64; k += 2) {
        uint64_t mask = 0;
        for (int i = 0; i < 6; ++i) {
            int r = ((2 * C[i] + 1) * k) & 127;
            int rep = min(r, 128 - r);
            mask |= (1ULL << ((rep - 1) / 2));
        }
        if (mask < best) best = mask;
        images[n_img++] = mask;
    }
    sort(images, images + n_img);
    orbit_size = static_cast<int>(unique(images, images + n_img) - images);
    return best;
}

static uint64_t canon_even(const int C[6], int& orbit_size) {
    uint64_t best = ~0ULL;
    uint64_t images[16];
    int n_img = 0;
    for (int k = 1; k < 32; k += 2) {
        uint64_t mask = 0;
        for (int i = 0; i < 6; ++i) {
            int r = (C[i] * k) & 63;
            int rep = min(r, 64 - r);
            mask |= (1ULL << rep);
        }
        if (mask < best) best = mask;
        images[n_img++] = mask;
    }
    sort(images, images + n_img);
    orbit_size = static_cast<int>(unique(images, images + n_img) - images);
    return best;
}

static void run_sieve(bool is_odd, int MOD) {
    int INV_MOD[256] = {0};
    for (int i = 1; i < MOD; ++i) INV_MOD[i] = modpow(i, MOD - 2, MOD);

    int n_sites = is_odd ? 32 : 33;
    int EXP_MAT[33][33][U];
    memset(EXP_MAT, 0, sizeof(EXP_MAT));
    for (int i = 0; i < n_sites; ++i) {
        for (int j = 0; j < n_sites; ++j) {
            if (i == j) continue;
            if (is_odd) {
                int x = i + 1, a = j + 1;
                int d1 = (x - a + 64) & 63;
                int d2 = (x + a - 1) & 63;
                for (int u = 0; u < U; ++u) EXP_MAT[i][j][u] = EXPS[d1][u] + EXPS[d2][u];
            } else {
                int d1 = (i - j + 64) & 63;
                int d2 = (i + j) & 63;
                for (int u = 0; u < U; ++u) EXP_MAT[i][j][u] = EXPS[d1][u] + EXPS[d2][u];
            }
        }
    }

    int g128 = modpow(3, (FMOD - 1) / 128, FMOD);
    int fpts[33];
    for (int i = 0; i < n_sites; ++i) {
        int e = is_odd ? (2 * i + 1) : (2 * i);
        fpts[i] = (modpow(g128, e, FMOD) + modpow(g128, (128 - e) % 128, FMOD)) % FMOD;
    }

    unordered_set<uint64_t> seen;
    vector<array<int, 6>> reps;
    long long orbit_sum = 0;
    if (is_odd) {
        seen.reserve(40000);
        int C[6];
        C[0] = 0;
        for (int a = 1; a < 32; ++a)
        for (int b = a + 1; b < 32; ++b)
        for (int c = b + 1; c < 32; ++c)
        for (int d = c + 1; d < 32; ++d)
        for (int e = d + 1; e < 32; ++e) {
            C[1] = a; C[2] = b; C[3] = c; C[4] = d; C[5] = e;
            int osz = 0;
            uint64_t key = canon_odd(C, osz);
            if (seen.insert(key).second) {
                reps.push_back({C[0], C[1], C[2], C[3], C[4], C[5]});
                orbit_sum += osz;
            }
        }
        assert(orbit_sum == 906192LL);  // C(32, 6)
        assert(reps.size() == 28336ULL);
    } else {
        seen.reserve(60000);
        int C[6];
        for (int a = 1; a < 32; ++a)
        for (int b = a + 1; b < 32; ++b)
        for (int c = b + 1; c < 32; ++c)
        for (int d = c + 1; d < 32; ++d)
        for (int e = d + 1; e < 32; ++e)
        for (int f = e + 1; f < 32; ++f) {
            C[0] = a; C[1] = b; C[2] = c; C[3] = d; C[4] = e; C[5] = f;
            int osz = 0;
            uint64_t key = canon_even(C, osz);
            if (seen.insert(key).second) {
                reps.push_back({C[0], C[1], C[2], C[3], C[4], C[5]});
                orbit_sum += osz;
            }
        }
        assert(orbit_sum == 736281LL);  // C(31, 6)
        assert(reps.size() == 47251ULL);
    }

    int max_nullity = 0;
    long long ternary_hits = 0;
    long long size7_hits = 0;
    long long chebyshev8_hits = 0;

    for (const auto& C : reps) {
        uint64_t cmask = 0;
        for (int i = 0; i < 6; ++i) cmask |= (1ULL << C[i]);
        int sites[27], ns = 0;
        for (int z = 0; z < n_sites; ++z) if (!(cmask & (1ULL << z))) sites[ns++] = z;

        int M[81][27], nr = 0;
        for (int i = 1; i < 6; ++i) {
            for (int u = 0; u < U; ++u) {
                for (int j = 0; j < ns; ++j) {
                    int diff = EXP_MAT[C[i]][sites[j]][u] - EXP_MAT[C[0]][sites[j]][u];
                    diff %= MOD;
                    if (diff < 0) diff += MOD;
                    M[nr][j] = diff;
                }
                nr++;
            }
        }
        for (int j = 0; j < ns; ++j) M[nr][j] = 1;
        nr++;

        int piv_col[27], free_col[27], np = 0, nf = 0;
        for (int col = 0; col < ns; ++col) {
            int piv = -1;
            for (int r = np; r < nr; ++r) {
                if (M[r][col] != 0) { piv = r; break; }
            }
            if (piv == -1) {
                free_col[nf++] = col;
                continue;
            }
            if (piv != np) {
                for (int j = col; j < ns; ++j) swap(M[np][j], M[piv][j]);
            }
            int inv = INV_MOD[M[np][col]];
            for (int j = col; j < ns; ++j) M[np][j] = M[np][j] * inv % MOD;
            for (int r = 0; r < nr; ++r) {
                if (r != np && M[r][col] != 0) {
                    int f = M[r][col];
                    for (int j = col; j < ns; ++j) {
                        int v = M[r][j] - f * M[np][j];
                        v %= MOD;
                        if (v < 0) v += MOD;
                        M[r][j] = v;
                    }
                }
            }
            piv_col[np++] = col;
        }
        if (nf > max_nullity) max_nullity = nf;
        if (nf == 0) continue;
        assert(nf <= 6);

        int total3 = 1;
        for (int i = 0; i < nf; ++i) total3 *= 3;
        int fval[6], w[27];
        for (int idx = 1; idx < total3; ++idx) {
            int tmp = idx, first_nz = 0;
            for (int i = 0; i < nf; ++i) {
                int d = tmp % 3;
                tmp /= 3;
                fval[i] = (d == 0 ? 0 : (d == 1 ? 1 : -1));
                if (first_nz == 0 && fval[i] != 0) first_nz = fval[i];
            }
            if (first_nz != 1) continue;

            bool ok = true;
            int cp = 0, cn = 0;
            for (int i = 0; i < nf; ++i) {
                w[free_col[i]] = fval[i];
                if (fval[i] == 1) cp++;
                else if (fval[i] == -1) cn++;
            }
            for (int r = 0; r < np; ++r) {
                int s = 0;
                for (int i = 0; i < nf; ++i) {
                    if (fval[i] == 1) s -= M[r][free_col[i]];
                    else if (fval[i] == -1) s += M[r][free_col[i]];
                }
                s %= MOD;
                if (s < 0) s += MOD;
                if (s == 0) {
                    w[piv_col[r]] = 0;
                } else if (s == 1) {
                    w[piv_col[r]] = 1;
                    cp++;
                } else if (s == MOD - 1) {
                    w[piv_col[r]] = -1;
                    cn++;
                } else {
                    ok = false;
                    break;
                }
            }
            if (!ok) continue;
            ternary_hits++;
            if (cp == 7 && cn == 7) size7_hits++;
            if (cp == 8 && cn == 8) {
                int r0 = -1;
                bool f_ok = true;
                for (int i = 0; i < 6; ++i) {
                    long long num = 1, den = 1;
                    for (int j = 0; j < ns; ++j) {
                        if (w[j] == 0) continue;
                        int diff = (fpts[C[i]] - fpts[sites[j]] + FMOD) % FMOD;
                        if (w[j] == 1) num = num * diff % FMOD;
                        else den = den * diff % FMOD;
                    }
                    int rat = static_cast<int>(num * modpow(den, FMOD - 2, FMOD) % FMOD);
                    if (i == 0) r0 = rat;
                    else if (rat != r0) { f_ok = false; break; }
                }
                if (f_ok) chebyshev8_hits++;
            }
        }
    }

    assert(size7_hits == 0);
    assert(chebyshev8_hits == (is_odd ? 12 : 8));
    assert(ternary_hits == (is_odd ? 12 : 8));
    cout << (is_odd ? "ODD " : "EVEN") << " MOD=" << MOD
         << " reps=" << reps.size()
         << " orbit_sum=" << orbit_sum
         << " max_nullity=" << max_nullity
         << " ternary_hits=" << ternary_hits
         << " size7_hits=" << size7_hits
         << " chebyshev_T8_controls=" << chebyshev8_hits << endl;
}

int main() {
    init_exps();
    for (int mod : {101, 103}) {
        run_sieve(true, mod);
        run_sieve(false, mod);
    }
    return 0;
}
