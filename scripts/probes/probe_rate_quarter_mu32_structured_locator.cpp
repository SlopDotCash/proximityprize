// Exact structured search for a degree-seven split-locator triangle on mu_32.
//
// Each structured block is the disjoint union of a four-point subgroup coset,
// an antipodal pair, and a singleton.  This is the natural degree-seven
// continuation of the mu_16 seed (an antipodal pair plus a singleton).  We
// build an exact hash table of all C(32,7) monic locators over F_193, scan every
// disjoint structured pair A,B and every affine parameter, and require the
// third root block C to be disjoint from both.  Hits are additionally tested
// over F_97, separating universal cyclotomic identities from mod-193 accidents.

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Poly = std::array<int, 8>;  // ascending coefficients, monic degree 7

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
  for (int q = 2; q * q <= n; ++q) {
    if (n % q == 0) {
      factors.push_back(q);
      while (n % q == 0) n /= q;
    }
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

static Poly locator(uint32_t mask, int p, const std::array<int, 32>& roots) {
  Poly a{};
  a[0] = 1;
  int degree = 0;
  for (int e = 0; e < 32; ++e) if ((mask >> e) & 1U) {
    Poly b{};
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

static uint64_t pack(const Poly& a) {
  uint64_t key = 0;
  for (int j = 0; j < 7; ++j) key |= static_cast<uint64_t>(a[j]) << (8 * j);
  return key;
}

static std::vector<uint32_t> all_seven_masks() {
  std::vector<uint32_t> out;
  out.reserve(3365856);
  for (uint32_t mask = (1U << 7) - 1;;) {
    out.push_back(mask);
    uint32_t c = mask & -mask;
    uint32_t r = mask + c;
    if (r == 0) break;
    mask = (((r ^ mask) >> 2) / c) | r;
  }
  return out;
}

static std::vector<uint32_t> structured_masks() {
  std::unordered_set<uint32_t> seen;
  for (int a = 0; a < 8; ++a) {
    uint32_t four = 0;
    for (int j = 0; j < 4; ++j) four |= 1U << (a + 8 * j);
    for (int b = 0; b < 16; ++b) {
      uint32_t two = (1U << b) | (1U << (b + 16));
      if (four & two) continue;
      for (int c = 0; c < 32; ++c) {
        uint32_t one = 1U << c;
        if ((four | two) & one) continue;
        seen.insert(four | two | one);
      }
    }
  }
  return {seen.begin(), seen.end()};
}

static bool collinear(uint32_t A, uint32_t B, uint32_t C, int p) {
  auto roots = roots32(p);
  Poly a = locator(A, p, roots), b = locator(B, p, roots), c = locator(C, p, roots);
  int pivot = -1;
  for (int j = 0; j < 7; ++j) if (a[j] != b[j]) { pivot = j; break; }
  if (pivot < 0) return false;
  int denom = (b[pivot] - a[pivot] + p) % p;
  int lambda = static_cast<int>((c[pivot] - a[pivot] + p) * mod_pow(denom, p - 2, p) % p);
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
  auto all = all_seven_masks();
  std::unordered_map<uint64_t, uint32_t> lookup;
  lookup.reserve(all.size() * 2);
  for (uint32_t mask : all) lookup.emplace(pack(locator(mask, p, roots)), mask);

  auto structured = structured_masks();
  std::vector<Poly> polys;
  polys.reserve(structured.size());
  for (uint32_t mask : structured) polys.push_back(locator(mask, p, roots));

  uint64_t pairs = 0, parameters = 0, hits = 0, cross_hits = 0;
  for (size_t ia = 0; ia < structured.size(); ++ia) {
    for (size_t ib = ia + 1; ib < structured.size(); ++ib) {
      uint32_t A = structured[ia], B = structured[ib];
      if (A & B) continue;
      ++pairs;
      for (int lambda = 2; lambda < p; ++lambda) {
        ++parameters;
        Poly c{};
        for (int j = 0; j < 7; ++j) {
          c[j] = (polys[ia][j] + static_cast<long long>(lambda) *
              (polys[ib][j] - polys[ia][j])) % p;
          if (c[j] < 0) c[j] += p;
        }
        c[7] = 1;
        auto it = lookup.find(pack(c));
        if (it == lookup.end()) continue;
        uint32_t C = it->second;
        if (C & (A | B)) continue;
        ++hits;
        bool cross = collinear(A, B, C, 97);
        if (cross) ++cross_hits;
        if (hits <= 30 || cross) {
          std::cout << "hit lambda=" << lambda << " cross97=" << cross << " A=";
          print_mask(A); std::cout << " B="; print_mask(B);
          std::cout << " C="; print_mask(C); std::cout << "\n";
        }
      }
    }
  }
  std::cout << "summary all_locators=" << all.size()
            << " structured=" << structured.size()
            << " disjoint_pairs=" << pairs
            << " parameters=" << parameters
            << " hits193=" << hits
            << " cross_hits97=" << cross_hits << "\n";
}
