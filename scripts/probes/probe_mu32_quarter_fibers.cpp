// Exhaust the affine orbits of five test sites on the 32nd roots.
// Characteristic-zero identities specialize at every primitive root in F_65537.
#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <thread>
#include <vector>
using Mask = uint32_t;
using U64 = uint64_t;
constexpr int prime = 65537;
std::array<std::array<uint32_t, 65536>, 32> low_products, high_products;
std::array<uint32_t, prime> inverses;
std::array<int, 32> sites;
int degree;
std::atomic<int> candidates{0}, asymmetric{0};
int modular_power(int x, int n) {
  U64 v = 1, b = x;
  while (n) {
    if (n & 1)
      v = v * b % prime;
    b = b * b % prime;
    n /= 2;
  }
  return v;
}
int vanisher_value(int x, Mask a) {
  return U64(low_products[x][a & 65535]) * high_products[x][a >> 16] % prime;
}
int first_index(Mask bit) { return __builtin_ctz(bit); }
Mask action(Mask m, int k, int s) {
  Mask ans = 0;
  while (m) {
    int j = first_index(m);
    ans |= Mask(1) << ((k * j + s) & 31);
    m &= m - 1;
  }
  return ans;
}
// Every orbit has a translate containing exponent zero.
bool canonical(Mask t) {
  for (int k = 1; k < 32; k += 2) {
    for (Mask m = t; m; m &= m - 1) {
      if (action(t, k, -k * first_index(m)) < t)
        return false;
    }
  }
  return true;
}
bool antipodal(Mask m) { return (m >> 16) == (m & 65535); }
void prepare() {
  for (int i = 0; i < 32; ++i)
    sites[i] = modular_power(3, 2048 * i);
  for (int i = 1; i < prime; ++i)
    inverses[i] = modular_power(i, prime - 2);
  for (int i = 0; i < 32; ++i) {
    low_products[i][0] = high_products[i][0] = 1;
    for (Mask m = 1; m < 65536; ++m) {
      int j = first_index(m);
      auto prev = m & (m - 1);
      low_products[i][m] =
          U64(low_products[i][prev]) * (prime + sites[i] - sites[j]) % prime;
      high_products[i][m] = U64(high_products[i][prev]) *
                            (prime + sites[i] - sites[j + 16]) % prime;
    }
  }
}
struct Record {
  U64 key;
  Mask support;
};
// Every true fiber passes all these specialization tests.
bool compatible_fiber(Mask t, Mask a, Mask b) {
  for (int k = 1; k < 16; k += 2) {
    Mask u = action(t, k, 0), v = action(a, k, 0), w = action(b, k, 0);
    int i = first_index(u), l = vanisher_value(i, v), r = vanisher_value(i, w);
    // Six protected points suffice to exclude two full septic edges.
    if (degree == 7) {
      int matches = 5;
      for (Mask m = ~(u | v | w); m; m &= m - 1) {
        int x = first_index(m);
        if (U64(l) * vanisher_value(x, w) % prime ==
            U64(r) * vanisher_value(x, v) % prime)
          ++matches;
      }
      if (matches < 6)
        return false;
    }
    for (u &= u - 1; u; u &= u - 1) {
      i = first_index(u);
      if ((U64)l * vanisher_value(i, w) % prime !=
          (U64)r * vanisher_value(i, v) % prime)
        return false;
    }
  }
  return true;
}
void search(Mask t) {
  std::array<int, 5> indices;
  int i = 0;
  for (Mask s = t; s; s &= s - 1)
    indices[i++] = first_index(s);
  std::vector<Record> rows;
  rows.reserve(degree == 7 ? 888030 : 296010);
  auto enumerate_supports = [&](auto &&self, Mask avail, Mask a,
                                int d) -> void {
    if (d == 0) {
      // Four nonzero ratios each range from 1 through 65536. Subtracting
      // one allows all four digits to fit in one unsigned 64-bit signature.
      int f = inverses[vanisher_value(indices[0], a)];
      U64 signature = 0;
      for (int j = 1; j < 5; ++j)
        signature = (signature << 16) +
                    (U64(f) * vanisher_value(indices[j], a) % prime - 1);
      rows.push_back({signature, a});
      return;
    }
    for (Mask m = avail; __builtin_popcount(m) >= d; m &= m - 1)
      self(self, m & (m - 1), a | (m & -m), d - 1);
  };
  enumerate_supports(enumerate_supports, ~t, 0, degree);
  std::sort(rows.begin(), rows.end(),
            [](auto &a, auto &b) { return a.key < b.key; });
  for (size_t i = 0; i < rows.size();) {
    size_t e = i + 1;
    while (e < rows.size() && rows[e].key == rows[i].key)
      ++e;
    for (size_t j = i; j < e; ++j)
      for (size_t h = j + 1; h < e; ++h) {
        Mask a = rows[j].support, b = rows[h].support;
        if (!(a & b) && compatible_fiber(t, a, b)) {
          ++candidates;
          if (!antipodal(a) || !antipodal(b))
            ++asymmetric;
        }
      }

    i = e;
  }
}
int main() {
  prepare();
  if (modular_power(sites[1], 16) != prime - 1)
    return 2;
  std::vector<Mask> representatives;
  for (int a = 1; a < 32; ++a)
    for (int b = a + 1; b < 32; ++b)
      for (int c = b + 1; c < 32; ++c)
        for (int d = c + 1; d < 32; ++d) {
          Mask t = 1 | (Mask(1) << a) | (Mask(1) << b) | (Mask(1) << c) |
                   (Mask(1) << d);
          if (canonical(t))
            representatives.push_back(t);
        }
  if (representatives.size() != 454)
    return 2;
  for (int d : {5, 6, 7}) {
    degree = d;
    candidates = 0;
    asymmetric = 0;
    std::atomic<unsigned> indices{0};
    std::vector<std::thread> pool;
    for (int u = 0; u < 4; ++u)
      pool.emplace_back([&] {
        for (;;) {
          auto j = indices++;
          if (j >= representatives.size())
            return;
          search(representatives[j]);
        }
      });
    for (auto &th : pool)
      th.join();
    std::printf(
        "degree %d: %zu test orbits, %d surviving pairs, %d asymmetric\n", d,
        representatives.size(), candidates.load(), asymmetric.load());
    std::fflush(stdout);
    if (candidates != (d == 6 ? 8 : 0) || asymmetric != 0)
      return 1;
  }
}
