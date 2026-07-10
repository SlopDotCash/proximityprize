// Exact collision census for the first and sixth elementary coefficients of
// seven-root locators on mu_32.
//
// Usage:
//   clang++ -O3 -std=c++17 -Wall -Wextra -Wpedantic this_file.cpp -o /tmp/e16
//   /tmp/e16
//
// In Z[zeta_32], the power basis 1,zeta,...,zeta^15 is integral and
// zeta^(e+16)=-zeta^e.  Thus a vector of sixteen integer coefficients is an
// exact equality signature, not a modular hash.  For every seven-subset S we
// encode
//
//   e_1(S) = sum_{s in S} zeta^s,
//   e_6(S) = sum_{s in S} zeta^(sum(S)-s).
//
// The program exhausts all C(32,7)=3,365,856 subsets and proves that no two
// disjoint subsets share both signatures.  This independently confirms the
// nondegeneracy used by the prize-field minor-norm lift in the accompanying
// knowledge-base note.  The conceptual proof needs only e_1 and follows from
// antipodal parity, so this census is deliberately a redundant falsifier.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

namespace {

constexpr int ORDER = 32;
constexpr int DEGREE = 7;
constexpr uint64_t EXPECTED_SETS = 3365856;
constexpr uint64_t EXPECTED_GROUPS = 3074048;
constexpr uint64_t EXPECTED_MAX_GROUP = 29;

struct Entry {
  uint64_t key;
  uint32_t mask;
};

uint32_t exact_power_basis_code(const std::array<int, DEGREE>& exponents) {
  std::array<int, ORDER / 2> coefficient{};
  for (int exponent : exponents) {
    if (exponent < ORDER / 2)
      ++coefficient[exponent];
    else
      --coefficient[exponent - ORDER / 2];
  }
  uint32_t code = 0;
  uint32_t power_of_three = 1;
  for (int value : coefficient) {
    // Both exponent lists contain distinct residues, so values lie in
    // {-1,0,1}.  Ternary encoding is therefore injective.
    if (value < -1 || value > 1) std::abort();
    code += static_cast<uint32_t>(value + 1) * power_of_three;
    power_of_three *= 3;
  }
  return code;
}

void generate(int next, int left, uint32_t mask,
              std::array<int, DEGREE>& subset, int position,
              std::vector<Entry>& entries) {
  if (left == 0) {
    int total = 0;
    for (int exponent : subset) total = (total + exponent) & (ORDER - 1);
    std::array<int, DEGREE> sixth{};
    for (int j = 0; j < DEGREE; ++j)
      sixth[j] = (total - subset[j]) & (ORDER - 1);
    const uint64_t key = exact_power_basis_code(subset) |
      (uint64_t{exact_power_basis_code(sixth)} << 32);
    entries.push_back({key, mask});
    return;
  }
  for (int exponent = next; exponent <= ORDER - left; ++exponent) {
    subset[position] = exponent;
    generate(exponent + 1, left - 1,
      mask | (uint32_t{1} << exponent), subset, position + 1, entries);
  }
}

}  // namespace

int main() {
  std::vector<Entry> entries;
  entries.reserve(EXPECTED_SETS);
  std::array<int, DEGREE> subset{};
  generate(0, DEGREE, 0, subset, 0, entries);
  std::sort(entries.begin(), entries.end(),
    [](const Entry& left, const Entry& right) { return left.key < right.key; });

  uint64_t groups = 0;
  uint64_t max_group = 0;
  uint64_t disjoint_pairs = 0;
  for (size_t first = 0; first < entries.size();) {
    size_t last = first + 1;
    while (last < entries.size() && entries[last].key == entries[first].key)
      ++last;
    ++groups;
    max_group = std::max<uint64_t>(max_group, last - first);
    for (size_t i = first; i < last; ++i)
      for (size_t j = i + 1; j < last; ++j)
        disjoint_pairs += (entries[i].mask & entries[j].mask) == 0;
    first = last;
  }

  std::cout << "sets=" << entries.size()
            << " exact_signature_groups=" << groups
            << " max_group=" << max_group
            << " disjoint_pairs=" << disjoint_pairs << "\n";

  const bool certified = entries.size() == EXPECTED_SETS &&
    groups == EXPECTED_GROUPS && max_group == EXPECTED_MAX_GROUP &&
    disjoint_pairs == 0;
  std::cout << (certified ? "CERTIFIED" : "FAILED") << "\n";
  return certified ? 0 : 1;
}
