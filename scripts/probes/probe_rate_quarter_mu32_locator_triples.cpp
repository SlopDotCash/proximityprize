#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <random>
#include <set>
#include <vector>

// Search for a degree-seven analogue of the mu_16 cubic-locator identity used
// by the smooth rate-quarter counterexample.  For seven-subsets A,C of
// mu_32 with at most one common root, the monic locator pencil
//
//   P_B = (1-lambda) P_C + lambda P_A
//
// has a third split member precisely when the ratio
//
//   lambda(x) = P_C(x) / (P_C(x)-P_A(x))
//
// takes one nontrivial value on seven further subgroup points.  The program
// exhausts every such A for each seeded C.  It then rejects identities that
// do not survive at the same exponent sets over F_193 and F_257; this filters
// characteristic-specific coincidences.  A surviving hit would lift to pair
// cores of size 7n/32, improving the known mu_16 construction.

namespace {

constexpr int P = 97;
constexpr int S = 32;
constexpr int R = 7;

int mod(int x) {
  x %= P;
  return x < 0 ? x + P : x;
}

int power(int a, int e) {
  int out = 1;
  while (e) {
    if (e & 1) out = out * a % P;
    a = a * a % P;
    e >>= 1;
  }
  return out;
}

int primitive_root() {
  for (int g = 2; g < P; ++g)
    if (power(g, 48) != 1 && power(g, 32) != 1) return g;
  return 0;
}

std::array<int, S> subgroup() {
  std::array<int, S> out{};
  const int omega = power(primitive_root(), (P - 1) / S);
  out[0] = 1;
  for (int i = 1; i < S; ++i) out[i] = out[i - 1] * omega % P;
  return out;
}

int locator_eval(uint32_t mask, int x,
                 const std::array<int, S>& mu) {
  int out = 1;
  for (int i = 0; i < S; ++i)
    if (mask >> i & 1U) out = out * mod(x - mu[i]) % P;
  return out;
}

struct Hit {
  uint32_t a = 0;
  uint32_t b = 0;
  uint32_t c = 0;
  int lambda = 0;
};

std::array<int, R + 1> locator_coeff(uint32_t mask, int modulus,
                                     int zeta) {
  std::array<int, R + 1> out{};
  out[0] = 1;
  int degree = 0;
  for (int exponent = 0; exponent < S; ++exponent) {
    if (!(mask >> exponent & 1U)) continue;
    int root = 1;
    for (int i = 0; i < exponent; ++i) root = root * zeta % modulus;
    for (int d = degree + 1; d >= 1; --d)
      out[d] = (out[d - 1] - root * out[d]) % modulus;
    out[0] = -root * out[0] % modulus;
    for (int d = 0; d <= degree + 1; ++d)
      if (out[d] < 0) out[d] += modulus;
    ++degree;
  }
  return out;
}

bool collinear_at(uint32_t a, uint32_t b, uint32_t c,
                  int modulus, int zeta) {
  const auto pa = locator_coeff(a, modulus, zeta);
  const auto pb = locator_coeff(b, modulus, zeta);
  const auto pc = locator_coeff(c, modulus, zeta);
  int lambda = -1;
  for (int i = 0; i <= R; ++i) {
    const int denominator = (pa[i] - pc[i] + modulus) % modulus;
    if (!denominator) continue;
    int inverse = 1;
    int base = denominator;
    for (int exponent = modulus - 2; exponent; exponent >>= 1) {
      if (exponent & 1) inverse = inverse * base % modulus;
      base = base * base % modulus;
    }
    lambda = (pb[i] - pc[i] + modulus) % modulus * inverse % modulus;
    break;
  }
  if (lambda < 0) return false;
  for (int i = 0; i <= R; ++i)
    if (((1 - lambda) * pc[i] + lambda * pa[i] - pb[i]) % modulus != 0)
      return false;
  return true;
}

Hit search_c(uint32_t c_mask, const std::array<int, S>& mu,
             const std::array<int, P>& inverse, uint64_t& tested,
             uint64_t& spurious) {
  std::array<int, S> c_value{};
  for (int i = 0; i < S; ++i) {
    c_value[i] = locator_eval(c_mask, mu[i], mu);
  }
  std::array<int, R> choose{};
  for (int i = 0; i < R; ++i) choose[i] = i;
  while (true) {
    ++tested;
    uint32_t a_mask = 0;
    for (int i : choose) a_mask |= 1U << i;
    const uint32_t common_mask = a_mask & c_mask;
    const int common = __builtin_popcount(common_mask);
    if (common <= 1) {
      std::array<int, P> count{};
      std::array<uint32_t, P> roots{};
      for (int point = 0; point < S; ++point) {
        if ((a_mask | c_mask) >> point & 1U) continue;
        const int av = locator_eval(a_mask, mu[point], mu);
        const int cv = c_value[point];
        const int denominator = mod(cv - av);
        if (!denominator) continue;
        const int lambda = cv * inverse[denominator] % P;
        if (lambda == 0 || lambda == 1) continue;
        roots[lambda] |= 1U << point;
        if (++count[lambda] == R - common) {
          const uint32_t b_mask = roots[lambda] | common_mask;
          if (collinear_at(a_mask, b_mask, c_mask, 193, 185) &&
              collinear_at(a_mask, b_mask, c_mask, 257, 136))
            return {a_mask, b_mask, c_mask, lambda};
          ++spurious;
        }
      }
    }
    int position = R - 1;
    while (position >= 0 &&
           choose[position] == S - R + position)
      --position;
    if (position < 0) break;
    ++choose[position];
    for (int j = position + 1; j < R; ++j)
      choose[j] = choose[j - 1] + 1;
  }
  return {};
}

std::vector<int> exponents(uint32_t mask) {
  std::vector<int> out;
  for (int i = 0; i < S; ++i)
    if (mask >> i & 1U) out.push_back(i);
  return out;
}

void print_set(const std::vector<int>& set) {
  std::cout << "{";
  for (size_t i = 0; i < set.size(); ++i)
    std::cout << (i ? "," : "") << set[i];
  std::cout << "}";
}

}  // namespace

int main(int argc, char** argv) {
  const int trials = argc > 1 ? std::stoi(argv[1]) : 64;
  const auto mu = subgroup();
  std::array<int, P> inverse{};
  for (int x = 1; x < P; ++x) inverse[x] = power(x, P - 2);
  std::mt19937 rng(20260710);
  std::set<uint32_t> seen;
  uint64_t tested = 0;
  uint64_t spurious = 0;

  // The first seed is the natural odd-coset-minus-one generalization of the
  // mu_16 certificate.  The rest are deterministic random seven-subsets.
  std::vector<uint32_t> seeds;
  uint32_t structured = 0;
  for (int e = 3; e < 16; e += 2) structured |= 1U << e;
  seeds.push_back(structured);
  while (static_cast<int>(seeds.size()) < trials) {
    std::array<int, S> permutation{};
    for (int i = 0; i < S; ++i) permutation[i] = i;
    std::shuffle(permutation.begin(), permutation.end(), rng);
    uint32_t mask = 0;
    for (int i = 0; i < R; ++i) mask |= 1U << permutation[i];
    if (seen.insert(mask).second) seeds.push_back(mask);
  }

  for (size_t trial = 0; trial < seeds.size(); ++trial) {
    const Hit hit = search_c(seeds[trial], mu, inverse, tested, spurious);
    if (hit.a) {
      std::cout << "HIT p=" << P << " mu=" << S
                << " lambda=" << hit.lambda << " A=";
      print_set(exponents(hit.a));
      std::cout << " B=";
      print_set(exponents(hit.b));
      std::cout << " C=";
      print_set(exponents(hit.c));
      std::cout << " seeded_C=" << trial
                << " tested_A=" << tested
                << " spurious=" << spurious << "\n";
      return 0;
    }
    std::cout << "seed=" << trial + 1 << "/" << seeds.size()
              << " tested_A=" << tested << " no_hit\n";
  }
  std::cout << "NO_HIT seeds=" << seeds.size()
            << " tested_A=" << tested
            << " characteristic_spurious=" << spurious << "\n";
  return 0;
}
