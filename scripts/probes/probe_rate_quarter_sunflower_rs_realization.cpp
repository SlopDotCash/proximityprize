#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>

// Exact F_29 certificate for the rate-quarter k=7 sunflower. Build with:
//   clang++ -O3 -std=c++20 this_file.cpp -o /tmp/sunflower && /tmp/sunflower
//
// Completeness of the decoder: a degree-<7 polynomial with at least 15
// agreements is fixed by any seven agreement coordinates. For each of the
// C(28,7) information sets we interpolate u0 and u1 once. The interpolant for
// scalar gamma is c0 + gamma*c1, so all 29 scalars are checked simultaneously.

namespace {

constexpr int P = 29;
constexpr int N = 28;
constexpr int K = 7;
constexpr int T = 15;

int mod(int x) {
  x %= P;
  return x < 0 ? x + P : x;
}

int power(int a, int e) {
  int r = 1;
  while (e) {
    if (e & 1) r = r * a % P;
    a = a * a % P;
    e >>= 1;
  }
  return r;
}

std::array<int, K> interpolate(const std::array<int, K>& xs,
                               const std::array<int, K>& ys,
                               const std::array<int, P>& inv) {
  std::array<int, K + 1> prod{};
  prod[0] = 1;
  int deg = 0;
  for (int x : xs) {
    for (int d = deg + 1; d >= 1; --d)
      prod[d] = mod(prod[d - 1] - x * prod[d]);
    prod[0] = mod(-x * prod[0]);
    ++deg;
  }

  std::array<int, K> out{};
  for (int m = 0; m < K; ++m) {
    const int x = xs[m];
    std::array<int, K> quot{};
    quot[K - 1] = prod[K];
    for (int d = K - 2; d >= 0; --d)
      quot[d] = mod(prod[d + 1] + x * quot[d + 1]);
    int denom = 1;
    for (int l = 0; l < K; ++l)
      if (l != m) denom = denom * mod(x - xs[l]) % P;
    const int scale = ys[m] * inv[denom] % P;
    for (int d = 0; d < K; ++d)
      out[d] = mod(out[d] + scale * quot[d]);
  }
  return out;
}

int eval(const std::array<int, K>& c, int x) {
  int y = 0;
  for (int d = K - 1; d >= 0; --d) y = mod(y * x + c[d]);
  return y;
}

uint64_t encode(const std::array<int, K>& c) {
  uint64_t key = 0;
  for (int d = K - 1; d >= 0; --d) key = key * P + c[d];
  return key;
}

std::array<int, K> decode(uint64_t key) {
  std::array<int, K> c{};
  for (int d = 0; d < K; ++d) {
    c[d] = key % P;
    key /= P;
  }
  return c;
}

bool restricted_degree_six(const std::vector<int>& agreement,
                           const std::array<int, N>& row,
                           const std::array<int, P>& inv) {
  std::array<int, K> xs{}, ys{};
  for (int i = 0; i < K; ++i) {
    xs[i] = agreement[i];
    ys[i] = row[agreement[i]];
  }
  auto c = interpolate(xs, ys, inv);
  for (int i : agreement)
    if (eval(c, i) != row[i]) return false;
  return true;
}

}  // namespace

int main() {
  std::array<int, P> inv{};
  for (int x = 1; x < P; ++x) inv[x] = power(x, P - 2);

  std::array<int, K> h{};
  h[0] = 1;
  int hdeg = 0;
  for (int x = 0; x < 6; ++x) {
    for (int d = hdeg + 1; d >= 1; --d)
      h[d] = mod(h[d - 1] - x * h[d]);
    h[0] = mod(-x * h[0]);
    ++hdeg;
  }

  std::array<int, N> hv{}, u0{}, u1{};
  const std::array<int, 4> parameter{1, 2, 4, 8};
  std::array<int, 4> line_a{}, line_r{};
  for (int i = 0; i < 4; ++i) {
    line_a[i] = parameter[i];
    line_r[i] = parameter[i] * parameter[i] % P;
  }
  const std::array<std::array<int, 2>, 6> pairs{{
      {{0, 1}}, {{0, 2}}, {{0, 3}}, {{1, 2}}, {{1, 3}}, {{2, 3}}
  }};
  std::array<int, 6> unused_a{};
  std::array<int, 6> crossing_gamma{};
  for (int e = 0; e < 6; ++e) {
    const int i = pairs[e][0], j = pairs[e][1];
    crossing_gamma[e] = mod(-(line_a[i] - line_a[j]) *
                            inv[mod(line_r[i] - line_r[j])]);
    unused_a[e] = mod(line_a[i] + crossing_gamma[e] * line_r[i]);
  }
  for (int x = 0; x < N; ++x) {
    hv[x] = eval(h, x);
    if (x >= 6 && x <= 21) {
      const int petal = (x - 6) / 4;
      u0[x] = line_a[petal] * hv[x] % P;
      u1[x] = line_r[petal] * hv[x] % P;
    } else if (x >= 22) {
      u0[x] = unused_a[x - 22] * hv[x] % P;
      u1[x] = 0;
    }
  }

  std::cout << "field=29 domain=0..27 H=";
  for (int d = 0; d < K; ++d) std::cout << (d ? "," : "") << h[d];
  std::cout << "\n";

  for (int line = 0; line < 4; ++line) {
    int core = 0;
    for (int x = 0; x < N; ++x) {
      const bool hit = (line_a[line] * hv[x] % P == u0[x] &&
                        line_r[line] * hv[x] % P == u1[x]);
      core += hit;
      const bool expected = x < 6 ||
          (x >= 6 + 4 * line && x < 10 + 4 * line);
      if (hit != expected) {
        std::cerr << "core mismatch line=" << line << " x=" << x << "\n";
        return 2;
      }
    }
    std::cout << "core[" << line << "].card=" << core
              << " v=(" << line_a[line] << "," << line_r[line] << ")\n";
  }
  for (int e = 0; e < 6; ++e) {
    std::cout << "pair=" << pairs[e][0] << pairs[e][1]
              << " gamma=" << crossing_gamma[e]
              << " unused_v=(" << unused_a[e] << ",0)\n";
  }
  for (int i = 0; i < 4; ++i) {
    for (int j = i + 1; j < 4; ++j) {
      for (int l = j + 1; l < 4; ++l) {
        const int det = mod((line_a[j] - line_a[i]) *
                                (line_r[l] - line_r[i]) -
                            (line_a[l] - line_a[i]) *
                                (line_r[j] - line_r[i]));
        std::cout << "det[" << i << j << l << "]=" << det << "\n";
        if (det == 0) return 4;
      }
    }
  }

  std::array<std::unordered_set<uint64_t>, P> candidates;
  std::array<int, K> choose{};
  for (int i = 0; i < K; ++i) choose[i] = i;
  uint64_t subsets = 0;
  while (true) {
    ++subsets;
    std::array<int, K> y0{}, y1{};
    for (int m = 0; m < K; ++m) {
      y0[m] = u0[choose[m]];
      y1[m] = u1[choose[m]];
    }
    auto c0 = interpolate(choose, y0, inv);
    auto c1 = interpolate(choose, y1, inv);

    int base = 0;
    std::array<int, P> root_count{};
    for (int x = 0; x < N; ++x) {
      const int d0 = mod(eval(c0, x) - u0[x]);
      const int d1 = mod(eval(c1, x) - u1[x]);
      if (d0 == 0 && d1 == 0) {
        ++base;
      } else if (d1 != 0) {
        const int gamma = mod(-d0 * inv[d1]);
        ++root_count[gamma];
      }
    }
    for (int gamma = 0; gamma < P; ++gamma) {
      if (base + root_count[gamma] < T) continue;
      std::array<int, K> c{};
      for (int d = 0; d < K; ++d) c[d] = mod(c0[d] + gamma * c1[d]);
      candidates[gamma].insert(encode(c));
    }

    int pos = K - 1;
    while (pos >= 0 && choose[pos] == N - K + pos) --pos;
    if (pos < 0) break;
    ++choose[pos];
    for (int j = pos + 1; j < K; ++j) choose[j] = choose[j - 1] + 1;
  }

  std::cout << "subsets=" << subsets << "\n";
  int selected_scalars = 0;
  int total_candidates = 0;
  std::array<int, 4> line_incidence{};
  std::array<bool, P> seen_gamma{};
  for (int gamma = 0; gamma < P; ++gamma) {
    if (candidates[gamma].empty()) continue;
    ++selected_scalars;
    seen_gamma[gamma] = true;
    total_candidates += candidates[gamma].size();
    std::cout << "gamma=" << gamma << " candidates=" << candidates[gamma].size() << "\n";
    for (uint64_t key : candidates[gamma]) {
      auto c = decode(key);
      std::vector<int> agreement;
      for (int x = 0; x < N; ++x) {
        const int w = mod(u0[x] + gamma * u1[x]);
        if (eval(c, x) == w) agreement.push_back(x);
      }
      if (agreement.size() < T) {
        std::cerr << "false candidate\n";
        return 3;
      }
      const bool joint = restricted_degree_six(agreement, u0, inv) &&
                         restricted_degree_six(agreement, u1, inv);
      int line = 0;
      for (int i = 0; i < 4; ++i) {
        bool same = true;
        for (int d = 0; d < K; ++d)
          if (c[d] != mod((line_a[i] + gamma * line_r[i]) * h[d])) same = false;
        if (same) {
          line = i + 1;
          ++line_incidence[i];
        }
      }
      std::cout << "  agree=" << agreement.size() << " joint=" << joint
                << " line=" << line << " coeff=";
      for (int d = 0; d < K; ++d) std::cout << (d ? "," : "") << c[d];
      std::cout << " set=";
      for (int x : agreement) std::cout << x << ",";
      std::cout << "\n";
      if (agreement.size() != T || joint || line == 0) return 5;
    }
  }
  std::cout << "selected_scalars=" << selected_scalars
            << " total_candidates=" << total_candidates << "\n";
  const std::array<int, 6> expected_gamma{12, 16, 19, 23, 24, 26};
  if (subsets != 1184040 || selected_scalars != 6 || total_candidates != 6)
    return 6;
  for (int gamma : expected_gamma)
    if (!seen_gamma[gamma]) return 7;
  for (int i = 0; i < 4; ++i) {
    std::cout << "line_incidence[" << i << "]=" << line_incidence[i] << "\n";
    if (line_incidence[i] != 3) return 8;
  }
}
