// Exact affine-orbit census for collinear split locators on mu_32.
//
// Usage:
//   c++ -O3 -std=c++17 -pthread this_file.cpp -o /tmp/mu32_orbits
//   /tmp/mu32_orbits 7 8       # degree 7, eight worker threads
//   /tmp/mu32_orbits 6 8       # degree 6
//
// For pairwise disjoint d-subsets A,B,C of Z/32, write P_A,P_B,P_C for
// their monic locators on mu_32.  This program exhausts the affine orbits of
// C under e |-> u*e+s (u odd), then every A disjoint from C.  Translation is
// a symmetry over every field.  Multiplication by odd u is instead the
// cyclotomic Galois symmetry zeta |-> zeta^u: it is exact for the
// characteristic-zero/universal identities targeted here, but need not
// preserve a coincidence in one fixed prime field.  Thus the F_97 hit count
// below is a count on Galois-normalized representatives, not a full census of
// characteristic-specific F_97 triples.  A third split member is detected
// from a d-fold collision of
//
//     lambda(x) = P_C(x) / (P_C(x)-P_A(x)).
//
// The primary search is over F_97.  Every hit is independently checked over
// F_193 and F_257.  The output calls these `THREE_PRIME_HIT`s, deliberately
// not universal identities: finitely many reductions are evidence, not a
// characteristic-zero proof.  Conversely, a characteristic-zero identity
// would reduce at every split prime, so zero three-prime survivors is an
// exact obstruction for universal identities after the Galois-normalized
// F_97 filter.  It does not obstruct identities specific to F_97 or to the
// prize field.

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <thread>
#include <unordered_set>
#include <vector>

namespace {

constexpr int ORDER = 32;
constexpr int PRIMARY = 97;

int mod(int x, int p) {
  x %= p;
  return x < 0 ? x + p : x;
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

uint32_t affine_image(uint32_t mask, int unit, int shift) {
  uint32_t out = 0;
  for (int e = 0; e < ORDER; ++e)
    if (mask >> e & 1U)
      out |= 1U << ((unit * e + shift) & (ORDER - 1));
  return out;
}

void generate_masks_rec(int next, int left, uint32_t mask,
                        std::vector<uint32_t>& out) {
  if (left == 0) {
    out.push_back(mask);
    return;
  }
  for (int e = next; e <= ORDER - left; ++e)
    generate_masks_rec(e + 1, left - 1, mask | (1U << e), out);
}

std::vector<uint32_t> affine_orbit_representatives(int degree) {
  std::vector<uint32_t> all;
  generate_masks_rec(0, degree, 0, all);
  std::unordered_set<uint32_t> unseen;
  unseen.reserve(all.size() * 2);
  unseen.insert(all.begin(), all.end());
  std::vector<uint32_t> representatives;
  while (!unseen.empty()) {
    const uint32_t seed = *unseen.begin();
    representatives.push_back(seed);
    for (int unit = 1; unit < ORDER; unit += 2)
      for (int shift = 0; shift < ORDER; ++shift)
        unseen.erase(affine_image(seed, unit, shift));
  }
  std::sort(representatives.begin(), representatives.end());
  return representatives;
}

int locator_eval(uint32_t mask, int x,
                 const std::array<int, ORDER>& mu, int p) {
  int out = 1;
  for (int e = 0; e < ORDER; ++e)
    if (mask >> e & 1U)
      out = static_cast<int64_t>(out) * mod(x - mu[e], p) % p;
  return out;
}

std::vector<int> locator_coeff(uint32_t mask, int degree, int p,
                               const std::array<int, ORDER>& mu) {
  std::vector<int> out(degree + 1);
  out[0] = 1;
  int current = 0;
  for (int e = 0; e < ORDER; ++e) {
    if (!(mask >> e & 1U)) continue;
    const int root = mu[e];
    for (int j = current + 1; j >= 1; --j)
      out[j] = mod(out[j - 1] -
        static_cast<int64_t>(root) * out[j] % p, p);
    out[0] = mod(-static_cast<int64_t>(root) * out[0] % p, p);
    ++current;
  }
  return out;
}

bool collinear_at(uint32_t a, uint32_t b, uint32_t c, int degree,
                  int p) {
  const auto mu = subgroup(p);
  const auto pa = locator_coeff(a, degree, p, mu);
  const auto pb = locator_coeff(b, degree, p, mu);
  const auto pc = locator_coeff(c, degree, p, mu);
  int lambda = -1;
  for (int j = 0; j < degree; ++j) {
    const int denominator = mod(pa[j] - pc[j], p);
    if (!denominator) continue;
    lambda = static_cast<int64_t>(mod(pb[j] - pc[j], p)) *
      power(denominator, p - 2, p) % p;
    break;
  }
  if (lambda < 0) return false;
  for (int j = 0; j <= degree; ++j)
    if (mod(pb[j] - ((1 - lambda) * pc[j] +
        static_cast<int64_t>(lambda) * pa[j]) % p, p) != 0)
      return false;
  return true;
}

struct Hit {
  uint32_t a;
  uint32_t b;
  uint32_t c;
  int lambda;
  bool three_prime;
};

bool antipodal(uint32_t mask) {
  return ((mask << 16) | (mask >> 16)) == mask;
}

void enumerate_disjoint_rec(const std::array<int, ORDER>& complement,
                            int complement_size, int position, int left,
                            uint32_t mask, std::vector<uint32_t>& out) {
  if (left == 0) {
    out.push_back(mask);
    return;
  }
  for (int j = position; j <= complement_size - left; ++j)
    enumerate_disjoint_rec(complement, complement_size, j + 1, left - 1,
      mask | (1U << complement[j]), out);
}

std::vector<Hit> search_representative(uint32_t c_mask, int degree,
                                       uint64_t& tested) {
  const auto mu = subgroup(PRIMARY);
  std::array<int, PRIMARY> inverse{};
  for (int x = 1; x < PRIMARY; ++x)
    inverse[x] = power(x, PRIMARY - 2, PRIMARY);
  std::array<int, ORDER> c_value{};
  for (int point = 0; point < ORDER; ++point)
    c_value[point] = locator_eval(c_mask, mu[point], mu, PRIMARY);

  std::array<int, ORDER> complement{};
  int complement_size = 0;
  for (int e = 0; e < ORDER; ++e)
    if (!(c_mask >> e & 1U)) complement[complement_size++] = e;
  std::vector<uint32_t> a_masks;
  enumerate_disjoint_rec(complement, complement_size, 0, degree, 0, a_masks);
  tested += a_masks.size();

  std::vector<Hit> hits;
  for (uint32_t a_mask : a_masks) {
    std::array<uint8_t, PRIMARY> count{};
    std::array<uint32_t, PRIMARY> roots{};
    for (int point = 0; point < ORDER; ++point) {
      if ((a_mask | c_mask) >> point & 1U) continue;
      const int av = locator_eval(a_mask, mu[point], mu, PRIMARY);
      const int cv = c_value[point];
      const int denominator = mod(cv - av, PRIMARY);
      if (!denominator) continue;
      const int lambda = static_cast<int64_t>(cv) * inverse[denominator] % PRIMARY;
      if (lambda == 0 || lambda == 1) continue;
      roots[lambda] |= 1U << point;
      if (++count[lambda] != degree) continue;
      const uint32_t b_mask = roots[lambda];
      if (!collinear_at(a_mask, b_mask, c_mask, degree, PRIMARY))
        std::abort();
      const bool three_prime =
        collinear_at(a_mask, b_mask, c_mask, degree, 193) &&
        collinear_at(a_mask, b_mask, c_mask, degree, 257);
      hits.push_back({a_mask, b_mask, c_mask, lambda, three_prime});
    }
  }
  return hits;
}

void print_set(uint32_t mask) {
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
  const int degree = argc > 1 ? std::atoi(argv[1]) : 7;
  const int workers = argc > 2 ? std::atoi(argv[2]) : 4;
  if (degree < 1 || 3 * degree > ORDER || workers < 1) return 2;

  const auto representatives = affine_orbit_representatives(degree);
  std::cout << "degree=" << degree
            << " affine_orbits=" << representatives.size()
            << " workers=" << workers << "\n";
  std::atomic<size_t> next{0};
  std::atomic<uint64_t> tested{0};
  std::atomic<uint64_t> f97_hit_count{0};
  std::mutex output_mutex;
  std::vector<Hit> all_hits;
  std::atomic<uint64_t> antipodal_hits{0};
  std::vector<std::thread> threads;
  for (int worker = 0; worker < workers; ++worker) {
    threads.emplace_back([&] {
      while (true) {
        const size_t index = next.fetch_add(1);
        if (index >= representatives.size()) break;
        uint64_t local_tested = 0;
        auto hits = search_representative(representatives[index], degree,
                                          local_tested);
        tested.fetch_add(local_tested);
        f97_hit_count.fetch_add(hits.size());
        if (!hits.empty()) {
          std::lock_guard<std::mutex> lock(output_mutex);
          for (const Hit& hit : hits) {
            if (!hit.three_prime) continue;
            all_hits.push_back(hit);
            const bool is_antipodal = antipodal(hit.a) &&
              antipodal(hit.b) && antipodal(hit.c);
            antipodal_hits.fetch_add(is_antipodal);
            std::cout << "THREE_PRIME_HIT"
                      << " lambda97=" << hit.lambda << " A=";
            print_set(hit.a);
            std::cout << " B=";
            print_set(hit.b);
            std::cout << " C=";
            print_set(hit.c);
            std::cout << " antipodal=" << is_antipodal
                      << " orbit=" << index << "\n";
          }
        }
        if (index % 100 == 0) {
          std::lock_guard<std::mutex> lock(output_mutex);
          std::cout << "progress=" << index << "/" << representatives.size()
                    << " tested=" << tested.load() << "\n";
        }
      }
    });
  }
  for (auto& thread : threads) thread.join();
  std::cout << "DONE degree=" << degree
            << " affine_orbits=" << representatives.size()
            << " disjoint_pairs_tested=" << tested.load()
            << " f97_hits=" << f97_hit_count.load()
            << " three_prime_hits=" << all_hits.size()
            << " antipodal_three_prime_hits=" << antipodal_hits.load()
            << "\n";
  return 0;
}
