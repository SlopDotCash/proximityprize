// Search degree-seven mu_32 locator lines parallel to lifted boundary lines.
//
// Every degree-four locator triangle on mu_16 has a direction polynomial of
// degree at most three.  Composing that direction with X^2 gives a degree-six
// direction on mu_32.  A parallel affine line containing three monic
// degree-seven locators would be exactly the missing disjoint degree-seven
// triangle.  This program exhausts all 50 boundary directions and all
// C(32,7)=3,365,856 locator points over F_193, then retests any hit over F_97.

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

template <size_t N> using Arr = std::array<int, N>;

static long long mod_pow(long long a, long long e, int p) {
  long long out = 1;
  while (e) {
    if (e & 1) out = out * a % p;
    a = a * a % p;
    e >>= 1;
  }
  return out;
}

static int primitive_root(int p) {
  std::vector<int> factors;
  int n = p - 1;
  for (int q = 2; q * q <= n; ++q) if (n % q == 0) {
    factors.push_back(q);
    while (n % q == 0) n /= q;
  }
  if (n > 1) factors.push_back(n);
  for (int g = 2; g < p; ++g) {
    bool ok = true;
    for (int q : factors) if (mod_pow(g, (p - 1) / q, p) == 1) ok = false;
    if (ok) return g;
  }
  return -1;
}

static std::array<int, 32> roots32(int p) {
  std::array<int, 32> roots{};
  int omega = static_cast<int>(mod_pow(primitive_root(p), (p - 1) / 32, p));
  roots[0] = 1;
  for (int i = 1; i < 32; ++i) roots[i] = roots[i - 1] * omega % p;
  return roots;
}

template <size_t D>
static Arr<D + 1> locator(uint32_t mask, int p, const std::array<int, 32>& roots) {
  Arr<D + 1> a{};
  a[0] = 1;
  int degree = 0;
  for (int e = 0; e < 32; ++e) if ((mask >> e) & 1U) {
    Arr<D + 1> b{};
    for (int j = 0; j <= degree; ++j) {
      b[j] = (b[j] - static_cast<long long>(roots[e]) * a[j]) % p;
      if (b[j] < 0) b[j] += p;
      b[j + 1] = (b[j + 1] + a[j]) % p;
    }
    a = b;
    ++degree;
  }
  return a;
}

static uint64_t pack7(const Arr<7>& a) {
  uint64_t key = 0;
  for (int j = 0; j < 7; ++j) key |= static_cast<uint64_t>(a[j]) << (8 * j);
  return key;
}

static uint32_t pack4(const Arr<4>& a) {
  uint32_t key = 0;
  for (int j = 0; j < 4; ++j) key |= static_cast<uint32_t>(a[j]) << (8 * j);
  return key;
}

static std::vector<uint32_t> masks_of_weight(int n, int w) {
  std::vector<uint32_t> out;
  uint64_t mask = (1ULL << w) - 1;
  const uint64_t limit = 1ULL << n;
  while (mask < limit) {
    out.push_back(static_cast<uint32_t>(mask));
    uint64_t c = mask & -mask;
    uint64_t r = mask + c;
    if (r >= limit) break;
    mask = (((r ^ mask) >> 2) / c) | r;
  }
  return out;
}

static Arr<4> normalized_direction4(const Arr<5>& a, const Arr<5>& b, int p) {
  Arr<4> q{};
  int pivot = -1;
  for (int j = 0; j < 4; ++j) {
    q[j] = (b[j] - a[j] + p) % p;
    if (pivot < 0 && q[j]) pivot = j;
  }
  int inv = static_cast<int>(mod_pow(q[pivot], p - 2, p));
  for (int& x : q) x = static_cast<int>(static_cast<long long>(x) * inv % p);
  return q;
}

static bool collinear4(const Arr<5>& a, const Arr<5>& b, const Arr<5>& c, int p) {
  int pivot = -1;
  for (int j = 0; j < 4; ++j) if (a[j] != b[j]) { pivot = j; break; }
  int lambda = static_cast<int>(static_cast<long long>(c[pivot] - a[pivot] + p) *
      mod_pow((b[pivot] - a[pivot] + p) % p, p - 2, p) % p);
  for (int j = 0; j < 4; ++j) {
    int rhs = (a[j] + static_cast<long long>(lambda) * (b[j] - a[j])) % p;
    if (rhs < 0) rhs += p;
    if (rhs != c[j]) return false;
  }
  return true;
}

static std::vector<Arr<7>> lifted_boundary_directions(int p) {
  auto roots = roots32(p);
  auto masks4small = masks_of_weight(16, 4);
  std::vector<Arr<5>> polys;
  polys.reserve(masks4small.size());
  for (uint32_t mask : masks4small) {
    // Exponent e in mu_16 is exponent 2e in mu_32.
    uint32_t lifted = 0;
    for (int e = 0; e < 16; ++e) if ((mask >> e) & 1U) lifted |= 1U << (2 * e);
    polys.push_back(locator<4>(lifted, p, roots));
  }
  std::unordered_set<uint32_t> directions4;
  for (size_t ia = 0; ia < masks4small.size(); ++ia) {
    uint32_t A = masks4small[ia];
    for (size_t ib = ia + 1; ib < masks4small.size(); ++ib) {
      uint32_t B = masks4small[ib];
      if (A & B) continue;
      uint32_t remaining = ((1U << 16) - 1) & ~(A | B);
      for (uint32_t C : masks4small) {
        if (C <= B || (C & ~remaining)) continue;
        size_t ic = __builtin_popcount(C & (C - 1)); // dummy, replaced below
        (void)ic;
        // Binary search is cheap at this scale because masks are Gosper-sorted.
        auto it = std::lower_bound(masks4small.begin(), masks4small.end(), C);
        size_t jc = static_cast<size_t>(it - masks4small.begin());
        if (collinear4(polys[ia], polys[ib], polys[jc], p))
          directions4.insert(pack4(normalized_direction4(polys[ia], polys[ib], p)));
      }
    }
  }
  std::vector<Arr<7>> out;
  for (uint32_t key : directions4) {
    Arr<7> q{};
    for (int j = 0; j < 4; ++j) q[2 * j] = (key >> (8 * j)) & 255;
    out.push_back(q);
  }
  return out;
}

static bool locator_collinear7(uint32_t A, uint32_t B, uint32_t C, int p) {
  auto roots = roots32(p);
  auto a = locator<7>(A, p, roots), b = locator<7>(B, p, roots), c = locator<7>(C, p, roots);
  int pivot = -1;
  for (int j = 0; j < 7; ++j) if (a[j] != b[j]) { pivot = j; break; }
  if (pivot < 0) return false;
  int lambda = static_cast<int>(static_cast<long long>(c[pivot] - a[pivot] + p) *
      mod_pow((b[pivot] - a[pivot] + p) % p, p - 2, p) % p);
  for (int j = 0; j < 7; ++j) {
    int rhs = (a[j] + static_cast<long long>(lambda) * (b[j] - a[j])) % p;
    if (rhs < 0) rhs += p;
    if (rhs != c[j]) return false;
  }
  return true;
}

static void print_mask(uint32_t mask) {
  std::cout << "{";
  bool first = true;
  for (int e = 0; e < 32; ++e) if ((mask >> e) & 1U) {
    if (!first) std::cout << ",";
    first = false;
    std::cout << e;
  }
  std::cout << "}";
}

int main() {
  constexpr int p = 193;
  auto roots = roots32(p);
  auto masks7 = masks_of_weight(32, 7);
  std::vector<Arr<8>> polys;
  polys.reserve(masks7.size());
  for (uint32_t mask : masks7) polys.push_back(locator<7>(mask, p, roots));
  auto directions = lifted_boundary_directions(p);

  uint64_t collision_lines = 0, triple_lines = 0, disjoint_hits = 0, cross97 = 0;
  for (const Arr<7>& q : directions) {
    int pivot = -1;
    for (int j = 0; j < 7; ++j) if (q[j]) { pivot = j; break; }
    std::unordered_map<uint64_t, uint32_t> first;
    std::unordered_map<uint64_t, std::vector<uint32_t>> groups;
    first.reserve(masks7.size() * 2);
    for (size_t i = 0; i < masks7.size(); ++i) {
      int coefficient = polys[i][pivot];
      Arr<7> base{};
      for (int j = 0; j < 7; ++j) {
        base[j] = (polys[i][j] - static_cast<long long>(coefficient) * q[j]) % p;
        if (base[j] < 0) base[j] += p;
      }
      uint64_t key = pack7(base);
      auto [it, inserted] = first.emplace(key, masks7[i]);
      if (inserted) continue;
      auto git = groups.find(key);
      if (git == groups.end()) {
        ++collision_lines;
        git = groups.emplace(key, std::vector<uint32_t>{it->second}).first;
      }
      git->second.push_back(masks7[i]);
    }
    for (const auto& [key, group] : groups) if (group.size() >= 3) {
      ++triple_lines;
      for (size_t i = 0; i < group.size(); ++i)
        for (size_t j = i + 1; j < group.size(); ++j)
          for (size_t k = j + 1; k < group.size(); ++k) {
            uint32_t A = group[i], B = group[j], C = group[k];
            if ((A & B) || (A & C) || (B & C)) continue;
            ++disjoint_hits;
            bool cross = locator_collinear7(A, B, C, 97);
            if (cross) ++cross97;
            std::cout << "hit cross97=" << cross << " A="; print_mask(A);
            std::cout << " B="; print_mask(B); std::cout << " C="; print_mask(C);
            std::cout << "\n";
          }
    }
  }
  std::cout << "summary locators=" << masks7.size()
            << " boundary_directions=" << directions.size()
            << " collision_lines=" << collision_lines
            << " triple_lines=" << triple_lines
            << " disjoint_hits193=" << disjoint_hits
            << " cross_hits97=" << cross97 << "\n";
}
