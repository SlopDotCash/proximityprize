// Exhaustive small-length census of four-head families one error past the quarter radius.
//
// Setting: N = 4h sites (the N-th roots of unity in F_p), heads f_0..f_3 of degree at most
// 2h-2 after removing the primitive linear direction, and a received scalar row y. By the
// profile analysis in docs/research/proximity-gap/first-prime-quarter-successor.md, an
// over-budget four-head family has all four cores {f_i = y} of size 3h-2 and one uncovered
// site, and at most one of its six differences has fewer than 2h-2 roots on the domain.
// Number the heads so that a deficient difference, if any, is f_0 - f_1, and subtract f_3:
//     f_0 = V_{Z0},   f_1 = l1 V_{Z1},   f_2 = l2 V_{Z2},   f_3 = 0
// for site sets of size 2h-2 and nonzero constants l1, l2, where f_0 - f_2 and f_1 - f_2
// have exactly 2h-2 roots on the domain and f_0 - f_1 has at least 2h-3.
//
// The search enumerates Z0 containing site 0 (rotation) and then Z2 and Z1. Two of the
// sets meet in the triple sites omitting the third head plus a possible four-core site,
// which the profiles confine to between h-3 and h sites. The constants are the ratio
// values that occur often enough. For every family found, a dynamic programme over the
// sites chooses the received value at each site (any head value there, or none) so that
// all four cores reach 3h-2 sites and the number of bad scalars these heads supply is
// largest: one for a covered site outside some core, four for an uncovered site. Families
// with more than N such scalars are printed.
//
// build: c++ -O2 -o probe_successor_four_head_census probe_successor_four_head_census.cpp
// usage: probe_successor_four_head_census h p g [mod res]
//   g of exact order 4h modulo the prime p < 2^31; h = 4 or 5. "mod res" splits the work.
// Reference runs (families, admitting an uncovered site, largest count, over budget):
//   4 2147483489 1550676160  ->  15502872, 2880, 16, 0
//   4 97 8                   ->  26875824, 4080, 19, 48
//   4 337 191                ->  16093128, 3456, 19, 288
//   5 2147482921 759095567   ->  236400, 0, none, 0   (twelve parts, "12 r", summed)
// Progress lines go to standard error.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <utility>
#include <vector>

typedef uint64_t u64;
typedef uint32_t u32;
static u64 P;
static inline u64 mulm(u64 a, u64 b) { return (a * b) % P; }
static inline u64 subm(u64 a, u64 b) { return a >= b ? a - b : a + P - b; }
static u64 powm(u64 a, u64 e) {
  u64 r = 1;
  while (e) { if (e & 1) r = mulm(r, a); a = mulm(a, a); e >>= 1; }
  return r;
}

static int N, H, W, T1;             // sites, h, set size 2h-2, rich core size 3h-2
static u64 root[32];
static std::vector<u32> sets;       // all W-subsets as bit masks
static std::vector<u32> val, ival;  // V_Z(x) and its inverse (0 on Z), indexed [set * N + x]
static std::vector<int> dp, dq;
static long long pairs_seen = 0, pair_hits = 0, families = 0, screened = 0, feasible = 0,
    over_budget = 0;
static int best_count = 0;

static inline int popc(u32 m) { return __builtin_popcount(m); }

// values l with V_{set a}(x) = l V_{set b}(x) on at least `need` sites outside both sets
static int ratio_modes(int a, int b, int need, u64 *out) {
  u32 skip = sets[a] | sets[b];
  u64 r[32];
  int nr = 0, found = 0;
  for (int x = 0; x < N; x++)
    if (!(skip >> x & 1)) r[nr++] = mulm(val[(size_t)a * N + x], ival[(size_t)b * N + x]);
  for (int i = 0; i < nr; i++) {
    int count = 0, first = 1;
    for (int j = 0; j < nr; j++) if (r[j] == r[i]) { if (j < i) { first = 0; break; } count++; }
    if (first && count >= need) out[found++] = r[i];
  }
  return found;
}

// largest number of bad scalars with all four cores of size at least 3h-2, or -1
static int best_assignment(int a, int b, int c, u64 l1, u64 l2) {
  const int B = T1 + 1, states = B * B * B * B;
  dp.assign(states, -1);
  dp[0] = 0;
  for (int x = 0; x < N; x++) {
    u64 f[4] = {val[(size_t)a * N + x], mulm(l1, val[(size_t)b * N + x]),
                mulm(l2, val[(size_t)c * N + x]), 0};
    int masks[5], gains[5], no = 0;
    for (int i = 0; i < 4; i++) {
      int first = 1, mask = 0;
      for (int j = 0; j < 4; j++) if (f[j] == f[i]) { if (j < i) first = 0; mask |= 1 << j; }
      if (first) { masks[no] = mask; gains[no++] = mask == 15 ? 0 : 1; }
    }
    masks[no] = 0;
    gains[no++] = 4;
    dq.assign(states, -1);
    for (int s = 0; s < states; s++) {
      if (dp[s] < 0) continue;
      int c0 = s % B, c1 = s / B % B, c2 = s / (B * B) % B, c3 = s / (B * B * B);
      for (int o = 0; o < no; o++) {
        int m = masks[o];
        int n0 = c0 + (m & 1), n1 = c1 + (m >> 1 & 1), n2 = c2 + (m >> 2 & 1), n3 = c3 + (m >> 3 & 1);
        if (n0 > T1) n0 = T1;
        if (n1 > T1) n1 = T1;
        if (n2 > T1) n2 = T1;
        if (n3 > T1) n3 = T1;
        int t = n0 + B * (n1 + B * (n2 + B * n3));
        if (dq[t] < dp[s] + gains[o]) dq[t] = dp[s] + gains[o];
      }
    }
    dp.swap(dq);
  }
  return dp[states - 1];
}

static void finish(int a, int b, int c, u64 l1, u64 l2) {
  families++;
  // Necessary for four cores of size 3h-2 beside an uncovered site: the largest groups of
  // equal head values, summed over all sites but one, reach 4 (3h-2).
  int total = 0, least = 4;
  for (int x = 0; x < N; x++) {
    u64 f[4] = {val[(size_t)a * N + x], mulm(l1, val[(size_t)b * N + x]),
                mulm(l2, val[(size_t)c * N + x]), 0};
    int most = 1;
    for (int i = 0; i < 4; i++) {
      int same = 0;
      for (int j = 0; j < 4; j++) same += f[j] == f[i];
      if (same > most) most = same;
    }
    total += most;
    if (most < least) least = most;
  }
  if (total - least < 4 * T1) return;
  screened++;
  int count = best_assignment(a, b, c, l1, l2);
  if (count < 0) return;
  feasible++;
  if (count > best_count) best_count = count;
  if (count > N) {
    over_budget++;
    std::printf("over budget: %d scalars, Z0 %06x Z1 %06x Z2 %06x l1 %llu l2 %llu\n", count,
                sets[a], sets[b], sets[c], (unsigned long long)l1, (unsigned long long)l2);
    std::fflush(stdout);
  }
}

int main(int argc, char **argv) {
  if (argc != 4 && argc != 6) {
    std::fprintf(stderr, "usage: %s h p g [mod res]\n", argv[0]);
    return 2;
  }
  int mod = 1, res = 0;
  if (argc == 6) { mod = std::atoi(argv[4]); res = std::atoi(argv[5]); }
  H = std::atoi(argv[1]);
  P = std::strtoull(argv[2], 0, 10);
  u64 g = std::strtoull(argv[3], 0, 10);
  N = 4 * H;
  W = 2 * H - 2;
  T1 = 3 * H - 2;
  if (H < 4 || H > 5 || P >= (1ULL << 31)) {
    std::fprintf(stderr, "need h = 4 or 5 and p < 2^31\n");
    return 2;
  }
  root[0] = 1;
  for (int i = 1; i < N; i++) root[i] = mulm(root[i - 1], g);
  int exact = mulm(root[N - 1], g) == 1;
  for (int i = 1; i < N; i++) if (root[i] == 1) exact = 0;
  if (!exact) { std::fprintf(stderr, "g does not have order 4h\n"); return 2; }
  for (u32 m = 0; m < (1u << N); m++) if (popc(m) == W) sets.push_back(m);
  size_t ns = sets.size();
  val.assign(ns * N, 0);
  ival.assign(ns * N, 0);
  for (size_t s = 0; s < ns; s++)
    for (int x = 0; x < N; x++) {
      if (sets[s] >> x & 1) continue;
      u64 v = 1;
      for (int z = 0; z < N; z++) if (sets[s] >> z & 1) v = mulm(v, subm(root[x], root[z]));
      val[s * N + x] = (u32)v;
      ival[s * N + x] = (u32)powm(v, P - 2);
    }
  // hits[s]: all (t, l) with V_{Zs} - l V_{Zt} full, computed on first use
  std::vector<std::vector<std::pair<int, u64> > > hits(ns);
  std::vector<char> done(ns, 0);
  u64 ls[32];
  auto full_partners = [&](int s) -> const std::vector<std::pair<int, u64> > & {
    if (!done[s]) {
      done[s] = 1;
      for (size_t t = 0; t < ns; t++) {
        int meet = popc(sets[s] & sets[t]);
        if ((int)t == s || meet < H - 3 || meet > H) continue;
        pairs_seen++;
        int n = ratio_modes(s, (int)t, W - meet, ls);
        for (int i = 0; i < n; i++) { hits[s].push_back(std::make_pair((int)t, ls[i])); pair_hits++; }
      }
    }
    return hits[s];
  };
  long long a_index = 0;
  for (size_t a = 0; a < ns; a++) {
    if (!(sets[a] & 1)) continue;
    if ((a_index++ % mod) != res) continue;
    const std::vector<std::pair<int, u64> > from_a = full_partners((int)a);
    if (a_index % 500 == 1)
      std::fprintf(stderr, "progress: %lld sets, %lld families, %lld screened, %zu partners\n",
                   a_index, families, screened, from_a.size());
    for (size_t ci = 0; ci < from_a.size(); ci++) {
      // f_0 - f_2 full: V_{Z0} = l2 V_{Z2}
      int c = from_a[ci].first;
      u64 l2 = from_a[ci].second;
      const std::vector<std::pair<int, u64> > from_c = full_partners(c);
      for (size_t bi = 0; bi < from_c.size(); bi++) {
        // f_1 - f_2 full: V_{Z2} = mu V_{Z1}, so l1 = l2 * mu
        int b = from_c[bi].first;
        int meet = popc(sets[a] & sets[b]);
        if (b == (int)a || meet < H - 3 || meet > H) continue;
        u64 l1 = mulm(l2, from_c[bi].second);
        // f_0 - f_1 needs at least 2h-3 roots on the domain
        int have = meet;
        u32 skip = sets[a] | sets[b];
        for (int x = 0; x < N; x++)
          if (!(skip >> x & 1) && val[a * N + x] == mulm(l1, val[(size_t)b * N + x])) have++;
        if (have >= W - 1) finish((int)a, b, c, l1, l2);
      }
    }
  }
  std::printf("h = %d, p = %llu: %lld set pairs examined, %lld full differences, %lld "
              "four-head families, %lld passing the incidence screen, %lld with four cores of "
              "size %d, largest scalar count %d, %lld over the budget %d\n", H,
              (unsigned long long)P, pairs_seen, pair_hits, families, screened, feasible, T1,
              best_count, over_budget, N);
  return 0;
}
