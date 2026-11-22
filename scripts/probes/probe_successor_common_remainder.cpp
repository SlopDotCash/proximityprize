// Exhaustive small-length census for the one-hole successor profile with three two-core sites.
//
// Setting: N = 4h evaluation sites, the N-th roots of unity in F_p, written g^0 .. g^(N-1).
// In the profile with one uncovered site, one single-core site and three two-core sites,
// the four polynomial heads exist exactly when there are pairwise disjoint site sets
//   S0, S1, S2 of size h-1 and S3 of size h-2,
// with monic vanishing polynomials v0, v1, v2, v3, and three further distinct sites
// r01, r02, r12 outside them, such that v1 - c1 v0, v2 - c2 v0 and c1' v2 - c2' v1 are
// constant multiples of (X - r01) v3, (X - r02) v3 and (X - r12) v3. Equivalently v0, v1, v2
// have proportional values on S3: they share a remainder modulo v3 up to scalars.
//
// The search fixes 0 in S3 by rotation. For each (S3, S0) it looks for lines Y = l(X)
// through at least h-1 of the points (x, -v0(x)/v3(x)), x outside S0 and S3. Such a line
// is a further split member v0 + l v3 of span(v0, v3, X v3). A configuration needs two
// lines on disjoint point sets whose three vertices (the roots of l1, l2 and l1 - l2)
// are distinct sites outside S0, S1, S2, S3. When the three vertices coincide the four
// sets are fibers of one pencil and every site is covered, which gives exactly N labels.
//
// build: c++ -O2 -o probe_successor_common_remainder probe_successor_common_remainder.cpp
// usage: probe_successor_common_remainder h p g [mod res]
//   g must have exact order 4h modulo the prime p < 2^31; "mod res" splits the work.
// Reference runs (pairs, with a further member, with two disjoint, configurations):
//   4 2147483489 1550676160   ->  5460, 1348, 152, 0
//   5 2147482921 759095567    ->  406980, 1272, 108, 0
//   6 2147483497 138348335    ->  27457584, 80, 0, 0
#include <cstdint>
#include <cstdio>
#include <cstdlib>

typedef uint64_t u64;
static u64 P;
static inline u64 mulm(u64 a, u64 b) { return (a * b) % P; }
static inline u64 subm(u64 a, u64 b) { return a >= b ? a - b : a + P - b; }
static u64 powm(u64 a, u64 e) {
  u64 r = 1;
  while (e) { if (e & 1) r = mulm(r, a); a = mulm(a, a); e >>= 1; }
  return r;
}
static u64 invm(u64 a) { return powm(a, P - 2); }

#define MAXN 64
static int N, H, MOD = 1, RES = 0;
static u64 root[MAXN], diff[MAXN][MAXN];
static int s3[MAXN], s0[MAXN], in3[MAXN], in0[MAXN];
static long long pairs_seen = 0, with_line = 0, with_two = 0, configurations = 0, s3_index = 0;

static void examine() {
  int pts[MAXN], np = 0;
  u64 y[MAXN];
  pairs_seen++;
  for (int x = 0; x < N; x++) {
    if (in3[x] || in0[x]) continue;
    u64 num = 1, den = 1;
    for (int i = 0; i < H - 1; i++) num = mulm(num, diff[x][s0[i]]);
    for (int i = 0; i < H - 2; i++) den = mulm(den, diff[x][s3[i]]);
    y[np] = subm(0, mulm(num, invm(den)));
    pts[np++] = x;
  }
  static u64 masks[512], la[512], lb[512];
  int nm = 0;
  for (int i = 0; i < np; i++) for (int j = i + 1; j < np; j++) {
    u64 dx = subm(root[pts[j]], root[pts[i]]), dy = subm(y[j], y[i]);
    u64 mask = 0;
    int count = 0, first = 1;
    for (int k = 0; k < np; k++) {
      u64 lhs = mulm(subm(y[k], y[i]), dx);
      u64 rhs = mulm(subm(root[pts[k]], root[pts[i]]), dy);
      if (lhs == rhs) {
        if (k < j && k != i) { first = 0; break; }
        mask |= 1ULL << k;
        count++;
      }
    }
    if (first && count >= H - 1 && nm < 512) {
      u64 a = mulm(dy, invm(dx));
      la[nm] = a;
      lb[nm] = subm(y[i], mulm(a, root[pts[i]]));
      masks[nm++] = mask;
    }
  }
  if (!nm) return;
  with_line++;
  int two = 0;
  for (int a = 0; a < nm; a++) for (int b = a + 1; b < nm; b++) {
    if (masks[a] & masks[b]) continue;
    two = 1;
    int v[3] = {-1, -1, -1}, ok[3] = {0, 0, 0};
    u64 xs[3] = {0, 0, 0};
    if (la[a]) { xs[0] = mulm(subm(0, lb[a]), invm(la[a])); ok[0] = 1; }
    if (la[b]) { xs[1] = mulm(subm(0, lb[b]), invm(la[b])); ok[1] = 1; }
    if (la[a] != la[b]) { xs[2] = mulm(subm(lb[b], lb[a]), invm(subm(la[a], la[b]))); ok[2] = 1; }
    for (int t = 0; t < 3; t++) if (ok[t]) for (int e = 0; e < N; e++) if (root[e] == xs[t]) v[t] = e;
    int on = (v[0] >= 0) + (v[1] >= 0) + (v[2] >= 0);
    int distinct = v[0] != v[1] && v[0] != v[2] && v[1] != v[2], outside = 1;
    for (int t = 0; t < 3; t++) if (v[t] >= 0) {
      if (in3[v[t]] || in0[v[t]]) outside = 0;
      for (int k = 0; k < np; k++)
        if (pts[k] == v[t] && ((masks[a] | masks[b]) >> k & 1)) outside = 0;
    }
    if (on == 3 && distinct && outside) {
      configurations++;
      std::printf("configuration: S3 = {");
      for (int i = 0; i < H - 2; i++) std::printf("%d ", s3[i]);
      std::printf("} S0 = {");
      for (int i = 0; i < H - 1; i++) std::printf("%d ", s0[i]);
      std::printf("} S1 = {");
      for (int k = 0; k < np; k++) if (masks[a] >> k & 1) std::printf("%d ", pts[k]);
      std::printf("} S2 = {");
      for (int k = 0; k < np; k++) if (masks[b] >> k & 1) std::printf("%d ", pts[k]);
      std::printf("} vertices %d %d %d\n", v[0], v[1], v[2]);
      std::fflush(stdout);
    }
  }
  if (two) with_two++;
}

static void choose0(int start, int depth) {
  if (depth == H - 1) { examine(); return; }
  for (int x = start; x < N; x++) {
    if (in3[x]) continue;
    s0[depth] = x;
    in0[x] = 1;
    choose0(x + 1, depth + 1);
    in0[x] = 0;
  }
}

static void choose3(int start, int depth) {
  if (depth == H - 2) {
    if ((s3_index++ % MOD) == RES) choose0(0, 0);
    return;
  }
  for (int x = start; x < N; x++) {
    s3[depth] = x;
    in3[x] = 1;
    choose3(x + 1, depth + 1);
    in3[x] = 0;
  }
}

int main(int argc, char **argv) {
  if (argc != 4 && argc != 6) {
    std::fprintf(stderr, "usage: %s h p g [mod res]\n", argv[0]);
    return 2;
  }
  H = std::atoi(argv[1]);
  P = std::strtoull(argv[2], 0, 10);
  u64 g = std::strtoull(argv[3], 0, 10);
  if (argc == 6) { MOD = std::atoi(argv[4]); RES = std::atoi(argv[5]); }
  N = 4 * H;
  if (N > MAXN || H < 3 || P >= (1ULL << 31)) {
    std::fprintf(stderr, "need 3 <= h <= 16 and p < 2^31\n");
    return 2;
  }
  root[0] = 1;
  for (int i = 1; i < N; i++) root[i] = mulm(root[i - 1], g);
  int exact = mulm(root[N - 1], g) == 1;
  for (int i = 1; i < N; i++) if (root[i] == 1) exact = 0;
  if (!exact) {
    std::fprintf(stderr, "g does not have order 4h\n");
    return 2;
  }
  for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) diff[i][j] = subm(root[i], root[j]);
  s3[0] = 0;
  in3[0] = 1;
  choose3(1, 1);
  std::printf("h = %d, p = %llu: %lld (S3, S0) pairs, %lld with a further split member, "
              "%lld with two on disjoint sets, %lld configurations\n",
              H, (unsigned long long)P, pairs_seen, with_line, with_two, configurations);
  return 0;
}
