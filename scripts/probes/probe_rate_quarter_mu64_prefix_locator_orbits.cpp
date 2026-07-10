// Exact universal-identity filter for degree-15 locators on mu_64 with two
// 8+4+2+1 prefix-coset endpoints.
//
// Usage:
//   c++ -O3 -std=c++17 -pthread this_file.cpp -o /tmp/mu64_prefix
//   /tmp/mu64_prefix 8 8421
//   /tmp/mu64_prefix 8 44421
//
// A structured endpoint is a disjoint union of dyadic exponent cosets of
// sizes 8, 4, 2, and 1.  Equivalently its monic locator is
//
//   (X^8-a)(X^4-b)(X^2-c)(X-d).
//
// For every affine/Galois orbit representative C of these 145,600 sets and
// every disjoint structured A, the program searches for an *arbitrary*
// disjoint 15-root third locator B.  At a remaining root x it computes
//
//   lambda(x) = P_C(x) / (P_C(x)-P_A(x)).
//
// A 15-fold collision gives P_B=lambda P_A+(1-lambda)P_C.  Thus B is not
// required to have any prefix-coset structure.  The primary exact search is
// over F_193; every hit is checked coefficient-by-coefficient over F_257 and
// F_449.
//
// Translation of exponents is a symmetry over each fixed field.  Odd
// multiplication is a cyclotomic Galois symmetry only for a universal /
// characteristic-zero identity, not for an accidental identity in F_193 or
// in the prize field.  Consequently this is exhaustive for universal
// identities having two structured endpoints.  A zero three-prime survivor
// count rules out such universal identities; it does not by itself rule out
// a characteristic-specific P1 identity.

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

constexpr int ORDER = 64;
constexpr int DEGREE = 15;
constexpr int PRIMARY = 193;

int mod(int64_t x, int p) {
  x %= p;
  return x < 0 ? static_cast<int>(x + p) : static_cast<int>(x);
}

int power(int a, int e, int p) {
  int out = 1;
  while (e) {
    if (e & 1) out = static_cast<int64_t>(out) * a % p;
    a = static_cast<int64_t>(a) * a % p;
    e >>= 1;
  }
  return out;
}

int primitive_root(int p) {
  std::vector<int> factors;
  int n = p - 1;
  for (int q = 2; q * q <= n; ++q) {
    if (n % q) continue;
    factors.push_back(q);
    while (n % q == 0) n /= q;
  }
  if (n > 1) factors.push_back(n);
  for (int g = 2; g < p; ++g) {
    bool primitive = true;
    for (int q : factors)
      if (power(g, (p - 1) / q, p) == 1) primitive = false;
    if (primitive) return g;
  }
  std::abort();
}

std::array<int, ORDER> subgroup(int p) {
  std::array<int, ORDER> mu{};
  const int omega = power(primitive_root(p), (p - 1) / ORDER, p);
  mu[0] = 1;
  for (int i = 1; i < ORDER; ++i)
    mu[i] = static_cast<int64_t>(mu[i - 1]) * omega % p;
  return mu;
}

uint64_t coset_mask(int size, int residue) {
  uint64_t out = 0;
  const int step = ORDER / size;
  for (int j = 0; j < size; ++j)
    out |= uint64_t{1} << (residue + step * j);
  return out;
}

std::vector<uint64_t> structured_masks_8421() {
  std::vector<uint64_t> out;
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
          out.push_back(ma | mb | mc | md);
        }
      }
    }
  }
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  return out;
}

std::vector<uint64_t> structured_masks_44421() {
  std::vector<uint64_t> out;
  out.reserve(728000);
  for (int a = 0; a < 16; ++a) {
    const uint64_t ma = coset_mask(4, a);
    for (int b = a + 1; b < 16; ++b) {
      const uint64_t mb = coset_mask(4, b);
      for (int c = b + 1; c < 16; ++c) {
        const uint64_t mc = coset_mask(4, c);
        const uint64_t large = ma | mb | mc;
        for (int d = 0; d < 32; ++d) {
          const uint64_t md = coset_mask(2, d);
          if (large & md) continue;
          for (int e = 0; e < 64; ++e) {
            const uint64_t me = uint64_t{1} << e;
            if ((large | md) & me) continue;
            out.push_back(large | md | me);
          }
        }
      }
    }
  }
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
  return out;
}

uint64_t affine_image(uint64_t mask, int unit, int shift) {
  uint64_t out = 0;
  while (mask) {
    const int e = __builtin_ctzll(mask);
    mask &= mask - 1;
    out |= uint64_t{1} << ((unit * e + shift) & (ORDER - 1));
  }
  return out;
}

std::vector<uint64_t> affine_orbit_representatives(
    const std::vector<uint64_t>& masks) {
  std::unordered_set<uint64_t> unseen;
  unseen.reserve(masks.size() * 2);
  unseen.insert(masks.begin(), masks.end());
  std::vector<uint64_t> representatives;
  while (!unseen.empty()) {
    const uint64_t seed = *unseen.begin();
    representatives.push_back(seed);
    for (int unit = 1; unit < ORDER; unit += 2)
      for (int shift = 0; shift < ORDER; ++shift)
        unseen.erase(affine_image(seed, unit, shift));
  }
  std::sort(representatives.begin(), representatives.end());
  return representatives;
}

int locator_eval(uint64_t mask, int x,
                 const std::array<int, ORDER>& mu, int p) {
  int out = 1;
  while (mask) {
    const int e = __builtin_ctzll(mask);
    mask &= mask - 1;
    out = static_cast<int64_t>(out) * mod(x - mu[e], p) % p;
  }
  return out;
}

std::vector<uint16_t> evaluation_table(
    const std::vector<uint64_t>& masks,
    const std::array<int, ORDER>& mu) {
  std::vector<uint16_t> table(masks.size() * ORDER);
  for (size_t i = 0; i < masks.size(); ++i)
    for (int point = 0; point < ORDER; ++point)
      table[i * ORDER + point] = static_cast<uint16_t>(
        locator_eval(masks[i], mu[point], mu, PRIMARY));
  return table;
}

std::vector<int> locator_coeff(uint64_t mask, int p,
                               const std::array<int, ORDER>& mu) {
  std::vector<int> out(DEGREE + 1);
  out[0] = 1;
  int current = 0;
  while (mask) {
    const int e = __builtin_ctzll(mask);
    mask &= mask - 1;
    const int root = mu[e];
    for (int j = current + 1; j >= 1; --j)
      out[j] = mod(out[j - 1] -
        static_cast<int64_t>(root) * out[j], p);
    out[0] = mod(-static_cast<int64_t>(root) * out[0], p);
    ++current;
  }
  return out;
}

bool collinear_at(uint64_t a, uint64_t b, uint64_t c, int p) {
  const auto mu = subgroup(p);
  const auto pa = locator_coeff(a, p, mu);
  const auto pb = locator_coeff(b, p, mu);
  const auto pc = locator_coeff(c, p, mu);
  int lambda = -1;
  for (int j = 0; j < DEGREE; ++j) {
    const int denominator = mod(pa[j] - pc[j], p);
    if (!denominator) continue;
    lambda = static_cast<int64_t>(mod(pb[j] - pc[j], p)) *
      power(denominator, p - 2, p) % p;
    break;
  }
  if (lambda < 0) return false;
  for (int j = 0; j <= DEGREE; ++j) {
    const int expected = mod(static_cast<int64_t>(lambda) * pa[j] +
      static_cast<int64_t>(1 - lambda) * pc[j], p);
    if (pb[j] != expected) return false;
  }
  return true;
}

struct Hit {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  int lambda;
  bool three_prime;
};

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
  const int workers = argc > 1 ? std::atoi(argv[1]) : 4;
  const std::string shape = argc > 2 ? argv[2] : "8421";
  if (workers < 1) return 2;

  const auto masks = shape == "8421" ? structured_masks_8421() :
    shape == "44421" ? structured_masks_44421() : std::vector<uint64_t>{};
  const size_t expected = shape == "8421" ? 145600 :
    shape == "44421" ? 728000 : 0;
  if (masks.size() != expected || expected == 0) {
    std::cerr << "unexpected structured count " << masks.size() << "\n";
    return 3;
  }
  const auto representatives = affine_orbit_representatives(masks);
  const auto mu = subgroup(PRIMARY);
  const auto table = evaluation_table(masks, mu);
  std::unordered_map<uint64_t, size_t> index;
  index.reserve(masks.size() * 2);
  for (size_t i = 0; i < masks.size(); ++i) index[masks[i]] = i;
  std::array<uint16_t, PRIMARY> inverse{};
  for (int x = 1; x < PRIMARY; ++x)
    inverse[x] = static_cast<uint16_t>(power(x, PRIMARY - 2, PRIMARY));

  std::cout << "shape=" << shape
            << " structured_sets=" << masks.size()
            << " affine_galois_orbits=" << representatives.size()
            << " workers=" << workers << "\n";

  std::atomic<size_t> next{0};
  std::atomic<uint64_t> tested{0};
  std::atomic<uint64_t> primary_hits{0};
  std::atomic<uint64_t> three_prime_hits{0};
  std::mutex output_mutex;
  std::vector<std::thread> threads;
  for (int worker = 0; worker < workers; ++worker) {
    threads.emplace_back([&] {
      while (true) {
        const size_t orbit = next.fetch_add(1);
        if (orbit >= representatives.size()) break;
        const uint64_t c_mask = representatives[orbit];
        const uint16_t* cv = &table[index.at(c_mask) * ORDER];
        uint64_t local_tested = 0;
        uint64_t local_primary_hits = 0;
        uint64_t local_three_prime_hits = 0;
        std::vector<Hit> local_survivors;
        for (size_t ai = 0; ai < masks.size(); ++ai) {
          const uint64_t a_mask = masks[ai];
          if (a_mask & c_mask) continue;
          ++local_tested;
          const uint16_t* av = &table[ai * ORDER];
          std::array<uint8_t, PRIMARY> count{};
          std::array<uint64_t, PRIMARY> roots{};
          const uint64_t forbidden = a_mask | c_mask;
          for (int point = 0; point < ORDER; ++point) {
            if (forbidden >> point & 1U) continue;
            const int denominator = mod(cv[point] - av[point], PRIMARY);
            if (!denominator) continue;
            const int lambda = static_cast<int64_t>(cv[point]) *
              inverse[denominator] % PRIMARY;
            if (lambda == 0 || lambda == 1) continue;
            roots[lambda] |= uint64_t{1} << point;
            if (++count[lambda] != DEGREE) continue;
            const uint64_t b_mask = roots[lambda];
            if (!collinear_at(a_mask, b_mask, c_mask, PRIMARY)) std::abort();
            ++local_primary_hits;
            const bool three_prime =
              collinear_at(a_mask, b_mask, c_mask, 257) &&
              collinear_at(a_mask, b_mask, c_mask, 449);
            if (three_prime) {
              ++local_three_prime_hits;
              local_survivors.push_back(
                {a_mask, b_mask, c_mask, lambda, true});
            }
          }
        }
        tested.fetch_add(local_tested);
        primary_hits.fetch_add(local_primary_hits);
        three_prime_hits.fetch_add(local_three_prime_hits);
        if (!local_survivors.empty() || orbit % 8 == 0) {
          std::lock_guard<std::mutex> lock(output_mutex);
          for (const Hit& hit : local_survivors) {
            std::cout << "THREE_PRIME_HIT lambda193=" << hit.lambda
                      << " A=";
            print_set(hit.a);
            std::cout << " B=";
            print_set(hit.b);
            std::cout << " C=";
            print_set(hit.c);
            std::cout << " orbit=" << orbit << "\n";
          }
          std::cout << "progress=" << orbit << "/" << representatives.size()
                    << " tested=" << tested.load()
                    << " primary_hits=" << primary_hits.load()
                    << " three_prime_hits=" << three_prime_hits.load()
                    << "\n";
        }
      }
    });
  }
  for (auto& thread : threads) thread.join();

  std::cout << "DONE shape=" << shape
            << " structured_sets=" << masks.size()
            << " affine_galois_orbits=" << representatives.size()
            << " disjoint_structured_pairs_tested=" << tested.load()
            << " f193_hits=" << primary_hits.load()
            << " three_prime_hits=" << three_prime_hits.load()
            << "\n";
  return 0;
}
