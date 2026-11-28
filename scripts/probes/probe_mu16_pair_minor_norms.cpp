// Enumerate the pair minors for the five-pivot septic support transfer on
// mu_16.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Poly = std::array<int64_t, 8>; // Z[z]/(z^8+1)
using Wide = __int128_t;
constexpr int all = (1 << 16) - 1;

int pop(int mask) { return __builtin_popcount(static_cast<unsigned>(mask)); }

Poly shift(const Poly &a, int e) {
  Poly result{};
  for (int i = 0; i < 8; ++i)
    result[(i + e) & 7] = ((i + e) & 8) ? -a[i] : a[i];
  return result;
}

Poly product(const Poly &a, const Poly &b) {
  Poly accum{};
  for (int i = 0; i < 8; ++i)
    for (int j = 0; j < 8; ++j)
      accum[(i + j) & 7] += (i + j < 8 ? a[i] : -a[i]) * b[j];
  return accum;
}

Poly difference(Poly a, const Poly &b) {
  for (int i = 0; i < 8; ++i)
    a[i] -= b[i];
  return a;
}

// At each quadratic step take the norm E(z^2)^2-z^2 O(z^2)^2,
// dropping common rational powers of two before the next multiplication.
Wide odd_norm(const Poly &a) {
  std::array<Wide, 8> coeff{};
  std::copy(a.begin(), a.end(), coeff.begin());
  for (int n = 8; n > 1; n /= 2) {
    Wide bits = 0;
    for (int i = 0; i < n; ++i)
      bits |= coeff[i];
    if (bits == 0)
      return 0;
    while (bits % 2 == 0) {
      bits /= 2;
      for (int i = 0; i < n; ++i)
        coeff[i] /= 2;
    }
    std::array<Wide, 8> next{};
    for (int i = 0; i < n; ++i) {
      for (int j = i % 2; j < n; j += 2) {
        int k = (i + j) / 2;
        Wide term;
        if (__builtin_mul_overflow(coeff[i], coeff[j], &term))
          throw std::overflow_error("norm product");
        bool negate = (i % 2 != 0) != (k >= n / 2);
        Wide &slot = next[k % (n / 2)];
        bool overflow = negate ? __builtin_sub_overflow(slot, term, &slot)
                               : __builtin_add_overflow(slot, term, &slot);
        if (overflow)
          throw std::overflow_error("norm sum");
      }
    }
    coeff = next;
  }
  Wide n = coeff[0];
  if (n < 0)
    throw std::logic_error("negative absolute norm");
  while (n && n % 2 == 0)
    n /= 2;
  return n;
}

int affine_image(int m, int a, int b) {
  int out = 0;
  for (int j = 0; j < 16; ++j)
    if ((m >> j) & 1)
      out |= 1 << ((a * j + b) & 15);
  return out;
}

struct Locator {
  std::array<Poly, 5> values;
  std::array<std::array<Poly, 5>, 5> wedges;
};

Locator evaluate(int mask, const std::vector<int> &sites) {
  Locator data{};
  for (size_t i = 0; i < sites.size(); ++i) {
    Poly v{1};
    for (int j = 0; j < 16; ++j)
      if ((mask >> j) & 1)
        v = difference(shift(v, sites[i]), shift(v, j));
    data.values[i] = v;
    for (size_t k = 0; k < i; ++k) {
      auto p = product(data.values[k], v);
      data.wedges[k][i] = difference(shift(p, sites[i]), shift(p, sites[k]));
    }
  }
  return data;
}

struct Census {
  uint64_t count = 0;
  Wide max = 0;
  int rows = 0, first = 0, second = 0;
  std::array<int, 5> witness{};
  void observe(Wide norm, int power = 0, int omitted = -1) {
    ++count;
    if (norm > max) {
      max = norm;
      witness = {rows, first, second, power, omitted};
    }
  }
  void record(const Poly &p, int power = 0, int omitted = -1) {
    observe(odd_norm(p), power, omitted);
  }
};

void determinants(Census &out, const std::vector<int> &sites, const Locator &a,
                  const Locator &b, bool mixed) {
  int n = static_cast<int>(sites.size());
  if (n == 2) {
    // One column from each word, with y-exponents 0 or 1.
    // Removing a unit row factor lets relative powers -1,0,1 suffice.
    for (int e : {-1, 0, 1}) {
      auto pos = shift(product(a.values[0], b.values[1]), (e * sites[1]) & 15);
      auto neg = shift(product(a.values[1], b.values[0]), (e * sites[0]) & 15);
      out.record(difference(pos, neg), e);
    }
    return;
  }
  if (n == 3) {
    std::array<Poly, 3> terms;
    for (int i = 0; i < 3; ++i) {
      int j = (i == 0 ? 1 : 0), k = (i == 2 ? 1 : 2);
      terms[i] = product(a.wedges[j][k], b.values[i]);
      if (i == 1)
        for (auto &value : terms[i])
          value = -value;
    }
    // A full singleton column can carry y. For a mixed pair a
    // nonvanishing test can zero the partial column on one extra row.
    for (int e = 0; e <= (mixed ? 0 : 1); ++e) {
      Poly total{};
      std::array<Poly, 3> parts;
      for (int i = 0; i < 3; ++i) {
        parts[i] = shift(terms[i], e * sites[i]);
        for (int k = 0; k < 8; ++k)
          total[k] += parts[i][k];
      }
      out.record(total, e);
      if (mixed)
        for (int i = 0; i < 3; ++i)
          out.record(difference(total, parts[i]), e, i);
    }
    return;
  }
  Wide common = 0;
  // With all five pivots, a rank drop from four requires every one
  // of the five maximal minors to vanish at the same prime ideal.
  for (int omitted = (n == 5 ? 0 : -1); omitted < (n == 5 ? 5 : 0); ++omitted) {
    std::array<int, 4> chosen{};
    int length = 0;
    for (int i = 0; i < n; ++i)
      if (i != omitted)
        chosen[length++] = i;
    Poly total{};
    for (int i = 0; i < 4; ++i)
      for (int j = i + 1; j < 4; ++j) {
        std::array<int, 2> others{};
        int left = 0;
        for (int k = 0; k < 4; ++k)
          if (k != i && k != j)
            others[left++] = chosen[k];
        auto term = product(a.wedges[chosen[i]][chosen[j]],
                            b.wedges[others[0]][others[1]]);
        for (int k = 0; k < 8; ++k)
          total[k] += ((i + j - 1) % 2 ? -term[k] : term[k]);
      }
    Wide value = odd_norm(total);
    while (value) {
      Wide remainder = common % value;
      common = value;
      value = remainder;
    }
  }
  out.observe(common);
}

std::string decimal(Wide x) {
  if (!x)
    return "0";
  std::string digits;
  while (x > 0) {
    digits += static_cast<char>('0' + x % 10);
    x /= 10;
  }
  std::reverse(digits.begin(), digits.end());
  return digits;
}

Census measure(int n, int da, int db, bool mixed) {
  std::set<int> seen;
  Census out;
  for (int rows = 1; rows <= all; ++rows) {
    if (pop(rows) != n || seen.count(rows))
      continue;
    for (int t = 1; t < 16; t += 2)
      for (int k = 0; k < 16; ++k)
        seen.insert(affine_image(rows, t, k));
    int free = all ^ rows;
    std::vector<int> sites;
    for (int i = 0; i < 16; ++i)
      if ((rows >> i) & 1)
        sites.push_back(i);
    out.rows = rows;
    std::array<int, 1 << 16> offsets{};
    std::vector<Locator> data;
    for (int s = free; s; s = (s - 1) & free)
      if (pop(s) == da || pop(s) == db) {
        offsets[s] = static_cast<int>(data.size());
        data.push_back(evaluate(s, sites));
      }
    for (int A = free; A; A = (A - 1) & free) {
      if (pop(A) != da)
        continue;
      int rest = free ^ A;
      for (int B = rest; B; B = (B - 1) & rest) {
        if (pop(B) != db || (n >= 4 && A > B))
          continue;
        out.first = A;
        out.second = B;
        determinants(out, sites, data[offsets[A]], data[offsets[B]], mixed);
      }
    }
  }
  return out;
}

int main() {
  for (int n : {2, 3, 4, 5}) {
    for (auto [a, b] :
         {std::pair<int, int>{3, 3}, {3, 4}, {4, 4}, {4, 5}, {5, 5}}) {
      bool mixed = a != b;
      if ((n >= 3 && a == 3 && b == 3) || (n >= 4 && mixed))
        continue;
      auto out = measure(n, a, b, mixed);
      std::cout << n << " " << a << " " << b << " " << out.count << " "
                << decimal(out.max);
      for (int field : out.witness)
        std::cout << " " << field;
      std::cout << std::endl;
    }
  }
}
