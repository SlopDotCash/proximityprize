// Red-team the small-norm route for 8+4+2+1 prefix-coset locators on mu_64.
//
// For structured, disjoint locators A,C and roots x,y outside both sets, the
// ratio collision P_A(x)/P_C(x)=P_A(y)/P_C(y) is the vanishing of
//
//   D = P_A(x) P_C(y) - P_A(y) P_C(x).
//
// This probe represents D exactly in Z[zeta_64] with the power basis
// 1,zeta,...,zeta^31 and zeta^(e+32)=-zeta^e, then measures its squared l2
// norm.  Since a structured evaluation is a product of four binomials, each
// determinant is accumulated from exactly 512 signed terms.  The random scan
// is a falsifier for a hoped-for uniform l2Sq <= 939 norm budget: 939^16 is
// the largest integral sixteenth-power budget below the prize prime P1.
//
// Usage:
//   c++ -O3 -std=c++17 this_file.cpp -o /tmp/mu64_minor
//   /tmp/mu64_minor 5000000

// This is deliberately labelled a randomized red-team, not an exhaustive
// certificate.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

namespace {

constexpr int ORDER = 64;

struct PrefixSet {
  uint64_t mask;
  std::array<int, 4> size;
  std::array<int, 4> residue;
};

uint64_t coset_mask(int size, int residue) {
  uint64_t out = 0;
  const int step = ORDER / size;
  for (int j = 0; j < size; ++j)
    out |= uint64_t{1} << (residue + step * j);
  return out;
}

std::vector<PrefixSet> structured_sets() {
  std::vector<PrefixSet> out;
  out.reserve(145600);
  for (int a = 0; a < 8; ++a) {
    const uint64_t ma = coset_mask(8, a);
    for (int b = 0; b < 16; ++b) {
      const uint64_t mb = coset_mask(4, b);
      if (ma & mb) continue;
      for (int c = 0; c < 32; ++c) {
        const uint64_t mc = coset_mask(2, c);
        if ((ma | mb) & mc) continue;
        for (int d = 0; d < 64; ++d) {
          const uint64_t md = uint64_t{1} << d;
          if ((ma | mb | mc) & md) continue;
          out.push_back({ma | mb | mc | md,
            {8, 4, 2, 1}, {a, b, c, d}});
        }
      }
    }
  }
  return out;
}

struct Term {
  int exponent;
  int coefficient;
};

std::array<Term, 16> evaluation_terms(const PrefixSet& set, int point) {
  std::array<Term, 16> out{};
  out[0] = {0, 1};
  int used = 1;
  for (int factor = 0; factor < 4; ++factor) {
    const int old_used = used;
    const int positive = set.size[factor] * point & 63;
    const int negative = set.size[factor] * set.residue[factor] & 63;
    for (int j = 0; j < old_used; ++j) {
      out[j + old_used] = {
        (out[j].exponent + negative) & 63, -out[j].coefficient};
      out[j].exponent = (out[j].exponent + positive) & 63;
    }
    used *= 2;
  }
  return out;
}

void add_product(std::array<int, 32>& coefficients,
                 const std::array<Term, 16>& lhs,
                 const std::array<Term, 16>& rhs,
                 int outer_sign) {
  for (const Term& a : lhs) {
    for (const Term& b : rhs) {
      const int exponent = (a.exponent + b.exponent) & 63;
      const int basis = exponent & 31;
      const int fold_sign = exponent < 32 ? 1 : -1;
      coefficients[basis] +=
        outer_sign * fold_sign * a.coefficient * b.coefficient;
    }
  }
}

std::array<int, 32> determinant_coefficients(
    const PrefixSet& a, const PrefixSet& c, int x, int y) {
  const auto ax = evaluation_terms(a, x);
  const auto ay = evaluation_terms(a, y);
  const auto cx = evaluation_terms(c, x);
  const auto cy = evaluation_terms(c, y);
  std::array<int, 32> coefficients{};
  add_product(coefficients, ax, cy, 1);
  add_product(coefficients, ay, cx, -1);
  return coefficients;
}

int64_t determinant_l2_sq(const PrefixSet& a, const PrefixSet& c,
                          int x, int y) {
  const auto coefficients = determinant_coefficients(a, c, x, y);
  int64_t out = 0;
  for (int coefficient : coefficients)
    out += static_cast<int64_t>(coefficient) * coefficient;
  return out;
}

uint64_t next_random(uint64_t& state) {
  state ^= state << 13;
  state ^= state >> 7;
  state ^= state << 17;
  return state;
}

void print_set(uint64_t mask) {
  std::cout << "{";
  bool first = true;
  for (int e = 0; e < ORDER; ++e) {
    if (!(mask >> e & 1U)) continue;
    std::cout << (first ? "" : ",") << e;
    first = false;
  }
  std::cout << "}";
}

}  // namespace

int main(int argc, char** argv) {
  const uint64_t samples = argc > 1 ? std::strtoull(argv[1], nullptr, 10) :
    1000000;
  const auto sets = structured_sets();
  uint64_t state = 0xd1b54a32d192ed03ULL;
  uint64_t accepted = 0;
  int64_t maximum = -1;
  size_t best_a = 0;
  size_t best_c = 0;
  int best_x = 0;
  int best_y = 0;
  while (accepted < samples) {
    const size_t ai = next_random(state) % sets.size();
    const size_t ci = next_random(state) % sets.size();
    if (sets[ai].mask & sets[ci].mask) continue;
    const uint64_t allowed = ~(sets[ai].mask | sets[ci].mask);
    int x = next_random(state) & 63;
    if (!(allowed >> x & 1U)) continue;
    int y = next_random(state) & 63;
    if (x == y || !(allowed >> y & 1U)) continue;
    ++accepted;
    const int64_t value = determinant_l2_sq(sets[ai], sets[ci], x, y);
    if (value <= maximum) continue;
    maximum = value;
    best_a = ai;
    best_c = ci;
    best_x = x;
    best_y = y;
  }
  std::cout << "random_samples=" << accepted
            << " max_l2Sq=" << maximum
            << " hoped_budget_939_survives=" << (maximum <= 939)
            << " x=" << best_x << " y=" << best_y << " A=";
  print_set(sets[best_a].mask);
  std::cout << " C=";
  print_set(sets[best_c].mask);
  const auto coefficients = determinant_coefficients(
    sets[best_a], sets[best_c], best_x, best_y);
  std::cout << " coefficients=[";
  for (int j = 0; j < 32; ++j)
    std::cout << (j ? "," : "") << coefficients[j];
  std::cout << "]\n";
  return 0;
}
