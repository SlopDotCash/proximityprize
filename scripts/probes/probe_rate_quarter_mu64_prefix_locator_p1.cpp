// Exact P1 census for degree-15 mu_64 locators with two 8+4+2+1
// prefix-coset endpoints.
//
// Usage:
//   c++ -O3 -std=c++17 -pthread this_file.cpp -o /tmp/mu64_prefix_p1
//   /tmp/mu64_prefix_p1 12
//
// The endpoint family consists of all 145,600 disjoint unions of dyadic
// exponent cosets of sizes 8,4,2,1.  For each translation-orbit
// representative C and each disjoint structured A, the program searches for
// an arbitrary disjoint 15-root B.  It compares the exact ratios
//
//   P_A(x) / P_C(x),  x in mu_64 \ (A union C).
//
// A 15-fold collision is equivalent to a monic affine pencil member that
// splits at those fifteen roots.  B is not required to be structured.
//
// Only exponent translations are quotiented: they come from scaling X and
// are symmetries over the fixed prize field.  Odd exponent multiplication is
// intentionally NOT used, because it is a cyclotomic Galois symmetry in
// characteristic zero but not a field automorphism of F_P1.
//
// Arithmetic is exact in
//
//   P1 = 2^158 + 192*2^30 + 1
//      = 365375409332725729550921208179070755120141565953.
//
// A three-limb Montgomery implementation keeps the full fixed-field census
// practical and is self-tested against the known order-2^30 domain
// generator used by the existing P1 certificate probes.

#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

constexpr int ORDER = 64;
constexpr int DEGREE = 15;
constexpr std::array<uint64_t, 3> MOD = {
  206158430209ULL, 0ULL, 1073741824ULL};
constexpr uint64_t N0_INVERSE = 206158430207ULL;
constexpr std::array<uint64_t, 3> R2 = {
  0ULL, 6597069766672ULL, 36864ULL};
constexpr std::array<uint64_t, 3> MONT_ONE = {
  188978561025ULL, 18446744073709551424ULL, 1073741823ULL};
constexpr std::array<uint64_t, 3> DOMAIN_GENERATOR = {
  16205747479158694566ULL, 15522888180590068078ULL, 892333719ULL};
constexpr std::array<uint64_t, 3> MU64_GENERATOR = {
  13538979697878607778ULL, 11226233905239276164ULL, 943530136ULL};
constexpr std::array<uint64_t, 3> P_MINUS_TWO = {
  206158430207ULL, 0ULL, 1073741824ULL};

struct Fp {
  std::array<uint64_t, 3> limb{};

  bool operator==(const Fp& other) const { return limb == other.limb; }
  bool operator!=(const Fp& other) const { return !(*this == other); }
};

bool geq(const Fp& a, const std::array<uint64_t, 3>& b) {
  for (int i = 2; i >= 0; --i) {
    if (a.limb[i] != b[i]) return a.limb[i] > b[i];
  }
  return true;
}

Fp subtract_raw(const Fp& a, const std::array<uint64_t, 3>& b) {
  Fp out;
  uint64_t borrow = 0;
  for (int i = 0; i < 3; ++i) {
    const uint64_t bi = b[i] + borrow;
    const bool carry = bi < b[i];
    out.limb[i] = a.limb[i] - bi;
    borrow = carry || a.limb[i] < bi;
  }
  return out;
}

Fp montgomery_mul(const Fp& a, const Fp& b) {
  std::array<uint64_t, 7> t{};
  for (int i = 0; i < 3; ++i) {
    uint64_t carry = 0;
    for (int j = 0; j < 3; ++j) {
      const unsigned __int128 value =
        static_cast<unsigned __int128>(a.limb[i]) * b.limb[j] +
        t[i + j] + carry;
      t[i + j] = static_cast<uint64_t>(value);
      carry = static_cast<uint64_t>(value >> 64);
    }
    int position = i + 3;
    while (carry) {
      const uint64_t old = t[position];
      t[position] += carry;
      carry = t[position] < old;
      ++position;
    }
  }
  for (int i = 0; i < 3; ++i) {
    const uint64_t multiplier = t[i] * N0_INVERSE;
    uint64_t carry = 0;
    for (int j = 0; j < 3; ++j) {
      const unsigned __int128 value =
        static_cast<unsigned __int128>(multiplier) * MOD[j] +
        t[i + j] + carry;
      t[i + j] = static_cast<uint64_t>(value);
      carry = static_cast<uint64_t>(value >> 64);
    }
    int position = i + 3;
    while (carry) {
      const uint64_t old = t[position];
      t[position] += carry;
      carry = t[position] < old;
      ++position;
    }
    assert(t[i] == 0);
  }
  assert(t[6] == 0);
  Fp out{{t[3], t[4], t[5]}};
  if (geq(out, MOD)) out = subtract_raw(out, MOD);
  return out;
}

Fp subtract(const Fp& a, const Fp& b) {
  if (geq(a, b.limb)) return subtract_raw(a, b.limb);
  Fp out = subtract_raw(a, b.limb);
  uint64_t carry = 0;
  for (int i = 0; i < 3; ++i) {
    const unsigned __int128 value =
      static_cast<unsigned __int128>(out.limb[i]) + MOD[i] + carry;
    out.limb[i] = static_cast<uint64_t>(value);
    carry = static_cast<uint64_t>(value >> 64);
  }
  // `out` initially represents 2^192+a-b, so adding P wraps once and
  // leaves the canonical positive representative P+a-b.
  assert(carry == 1);
  return out;
}

Fp encode(const std::array<uint64_t, 3>& raw) {
  return montgomery_mul(Fp{raw}, Fp{R2});
}

Fp decode(const Fp& value) {
  return montgomery_mul(value, Fp{{1, 0, 0}});
}

Fp one() { return Fp{MONT_ONE}; }
Fp zero() { return Fp{}; }

bool exponent_bit(const std::array<uint64_t, 3>& exponent, int bit) {
  return exponent[bit / 64] >> (bit & 63) & 1U;
}

Fp power(Fp base, const std::array<uint64_t, 3>& exponent) {
  Fp out = one();
  for (int bit = 158; bit >= 0; --bit) {
    out = montgomery_mul(out, out);
    if (exponent_bit(exponent, bit)) out = montgomery_mul(out, base);
  }
  return out;
}

Fp inverse(const Fp& value) {
  assert(value != zero());
  return power(value, P_MINUS_TWO);
}

struct PrefixSet {
  uint64_t mask;
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
          out.push_back({ma | mb | mc | md, {a, b, c, d}});
        }
      }
    }
  }
  std::sort(out.begin(), out.end(),
    [](const PrefixSet& lhs, const PrefixSet& rhs) {
      return lhs.mask < rhs.mask;
    });
  for (size_t i = 1; i < out.size(); ++i)
    assert(out[i - 1].mask != out[i].mask);
  return out;
}

uint64_t translate(uint64_t mask, int shift) {
  if (shift == 0) return mask;
  return (mask << shift) | (mask >> (ORDER - shift));
}

std::vector<uint64_t> translation_representatives(
    const std::vector<PrefixSet>& sets) {
  std::unordered_set<uint64_t> unseen;
  unseen.reserve(sets.size() * 2);
  for (const PrefixSet& set : sets) unseen.insert(set.mask);
  std::vector<uint64_t> representatives;
  while (!unseen.empty()) {
    const uint64_t seed = *unseen.begin();
    representatives.push_back(seed);
    for (int shift = 0; shift < ORDER; ++shift)
      unseen.erase(translate(seed, shift));
  }
  std::sort(representatives.begin(), representatives.end());
  return representatives;
}

std::array<Fp, ORDER> roots_of_unity() {
  Fp generator = encode(DOMAIN_GENERATOR);
  // The existing P1 certificate generator has order 2^30.  Raising it to
  // 2^24 gives a primitive 64th root.
  for (int j = 0; j < 24; ++j)
    generator = montgomery_mul(generator, generator);
  assert(decode(generator).limb == MU64_GENERATOR);
  std::array<Fp, ORDER> mu{};
  mu[0] = one();
  for (int e = 1; e < ORDER; ++e)
    mu[e] = montgomery_mul(mu[e - 1], generator);
  assert(mu[32] == subtract(zero(), one()));
  assert(montgomery_mul(mu[63], generator) == one());
  return mu;
}

std::vector<Fp> evaluation_table(const std::vector<PrefixSet>& sets,
                                 const std::array<Fp, ORDER>& mu,
                                 int workers) {
  std::vector<Fp> table(sets.size() * ORDER);
  std::atomic<size_t> next{0};
  std::vector<std::thread> threads;
  for (int worker = 0; worker < workers; ++worker) {
    threads.emplace_back([&] {
      while (true) {
        const size_t i = next.fetch_add(1);
        if (i >= sets.size()) break;
        const PrefixSet& set = sets[i];
        for (int point = 0; point < ORDER; ++point) {
          Fp value = one();
          constexpr std::array<int, 4> sizes = {8, 4, 2, 1};
          for (int factor = 0; factor < 4; ++factor) {
            const Fp difference = subtract(
              mu[sizes[factor] * point & 63],
              mu[sizes[factor] * set.residue[factor] & 63]);
            value = montgomery_mul(value, difference);
          }
          table[i * ORDER + point] = value;
        }
      }
    });
  }
  for (auto& thread : threads) thread.join();
  return table;
}

uint64_t hash_fp(const Fp& value) {
  uint64_t x = value.limb[0] ^
    (value.limb[1] << 17 | value.limb[1] >> 47) ^
    (value.limb[2] << 39 | value.limb[2] >> 25);
  x ^= x >> 30;
  x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 27;
  x *= 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}

struct HashSlot {
  uint32_t generation = 0;
  Fp key{};
  uint64_t roots = 0;
  uint8_t count = 0;
};

struct Hit {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  Fp ratio;
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

void print_fp(const Fp& value) {
  std::cout << "[" << value.limb[0] << "," << value.limb[1] << ","
            << value.limb[2] << "]_Mont";
}

}  // namespace

int main(int argc, char** argv) {
  const int workers = argc > 1 ? std::atoi(argv[1]) : 4;
  if (workers < 1) return 2;

  // Montgomery smoke tests, including encode/decode behavior.
  const Fp encoded_one = encode({1, 0, 0});
  assert(encoded_one == one());
  const Fp encoded_two = encode({2, 0, 0});
  assert(montgomery_mul(encoded_two, encoded_two) == encode({4, 0, 0}));
  assert(montgomery_mul(encoded_two, inverse(encoded_two)) == one());

  const auto sets = structured_sets();
  if (sets.size() != 145600) return 3;
  const auto representatives = translation_representatives(sets);
  const auto mu = roots_of_unity();
  std::cout << "precompute structured_sets=" << sets.size()
            << " translation_orbits=" << representatives.size()
            << " workers=" << workers << "\n";
  const auto table = evaluation_table(sets, mu, workers);
  std::unordered_map<uint64_t, size_t> index;
  index.reserve(sets.size() * 2);
  for (size_t i = 0; i < sets.size(); ++i) index[sets[i].mask] = i;

  std::atomic<size_t> next{0};
  std::atomic<uint64_t> tested{0};
  std::atomic<uint64_t> hits{0};
  std::mutex output_mutex;
  std::vector<std::thread> threads;
  for (int worker = 0; worker < workers; ++worker) {
    threads.emplace_back([&] {
      std::array<HashSlot, 128> slots{};
      uint32_t generation = 0;
      while (true) {
        const size_t orbit = next.fetch_add(1);
        if (orbit >= representatives.size()) break;
        const uint64_t c_mask = representatives[orbit];
        const Fp* cv = &table[index.at(c_mask) * ORDER];
        std::array<Fp, ORDER> c_inverse{};
        std::array<Fp, ORDER> prefix{};
        Fp product = one();
        for (int point = 0; point < ORDER; ++point) {
          if (c_mask >> point & 1U) continue;
          prefix[point] = product;
          product = montgomery_mul(product, cv[point]);
        }
        Fp suffix_inverse = inverse(product);
        for (int point = ORDER - 1; point >= 0; --point) {
          if (c_mask >> point & 1U) continue;
          c_inverse[point] = montgomery_mul(suffix_inverse, prefix[point]);
          suffix_inverse = montgomery_mul(suffix_inverse, cv[point]);
        }
        assert(suffix_inverse == one());

        uint64_t local_tested = 0;
        std::vector<Hit> local_hits;
        for (size_t ai = 0; ai < sets.size(); ++ai) {
          const uint64_t a_mask = sets[ai].mask;
          if (a_mask & c_mask) continue;
          ++local_tested;
          if (++generation == 0) {
            for (HashSlot& slot : slots) slot.generation = 0;
            generation = 1;
          }
          const Fp* av = &table[ai * ORDER];
          const uint64_t forbidden = a_mask | c_mask;
          for (int point = 0; point < ORDER; ++point) {
            if (forbidden >> point & 1U) continue;
            const Fp ratio = montgomery_mul(av[point], c_inverse[point]);
            size_t position = hash_fp(ratio) & (slots.size() - 1);
            while (slots[position].generation == generation &&
                   slots[position].key != ratio)
              position = (position + 1) & (slots.size() - 1);
            HashSlot& slot = slots[position];
            if (slot.generation != generation) {
              slot.generation = generation;
              slot.key = ratio;
              slot.roots = uint64_t{1} << point;
              slot.count = 1;
            } else {
              slot.roots |= uint64_t{1} << point;
              if (++slot.count == DEGREE) {
                // P_A/P_C=1 at fifteen points would make P_A-P_C, of degree
                // at most fourteen, vanish identically.  The endpoints are
                // distinct, so this cannot occur; keep the assertion as an
                // independent implementation check.
                assert(ratio != one());
                local_hits.push_back(
                  {a_mask, slot.roots, c_mask, ratio});
              }
            }
          }
        }
        tested.fetch_add(local_tested);
        hits.fetch_add(local_hits.size());
        if (!local_hits.empty() || orbit % 64 == 0) {
          std::lock_guard<std::mutex> lock(output_mutex);
          for (const Hit& hit : local_hits) {
            std::cout << "P1_HIT ratio=";
            print_fp(hit.ratio);
            std::cout << " A=";
            print_set(hit.a);
            std::cout << " B=";
            print_set(hit.b);
            std::cout << " C=";
            print_set(hit.c);
            std::cout << " orbit=" << orbit << "\n";
          }
          std::cout << "progress=" << orbit << "/" << representatives.size()
                    << " tested=" << tested.load()
                    << " hits=" << hits.load() << "\n";
        }
      }
    });
  }
  for (auto& thread : threads) thread.join();

  std::cout << "DONE structured_sets=" << sets.size()
            << " translation_orbits=" << representatives.size()
            << " disjoint_structured_pairs_tested=" << tested.load()
            << " p1_hits=" << hits.load() << "\n";
  return 0;
}
