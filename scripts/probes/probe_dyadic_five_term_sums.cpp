// Verify antipodal cancellation for every signed relation of length at most ten.
#include "sponsor_phi_field.hpp"

#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <vector>

namespace {
constexpr unsigned max_size = 5;

Word choose(unsigned n, unsigned k) {
    Word result = 1;
    for (unsigned i = 1; i <= k; ++i)
        result = result * (n - i + 1) / i;
    return result;
}

Word orbit_count(unsigned order, unsigned size) {
    Word total = 0;
    for (unsigned pairs = 1; pairs <= size; ++pairs)
        total += choose(order / 2, pairs) * (Word(1) << pairs) * choose(size - 1, pairs - 1);
    require(total % order == 0, "nonintegral orbit count");
    return total / order;
}

std::array<Word, max_size> verify_orbits(const Field &field, unsigned order) {
    require(field.n % order == 0, "subgroup does not fit");
    mpz_class generator = power(field.g, field.n / order, field.p);
    require(power(generator, order / 2, field.p) == field.p - 1, "wrong dyadic subgroup");
    std::vector<mpz_class> roots(order);
    roots[0] = 1;
    for (unsigned j = 1; j < order; ++j)
        roots[j] = roots[j - 1] * generator % field.p;
    std::array<Word, max_size> counts{};
    Word expected = 0;
    for (unsigned size = 1; size <= max_size; ++size)
        expected += orbit_count(order, size);
    std::vector<Word> keys;
    keys.reserve(expected);
    std::array<unsigned, max_size> sites{};
    mpz_class sum, key;
    for (unsigned size = 1; size <= max_size; ++size) {
        unsigned stabilizer = std::gcd(order, size);
        auto opposite_appears = [&](unsigned site, unsigned used) {
            unsigned opposite = (site + order / 2) % order;
            return std::find(sites.begin(), sites.begin() + used, opposite) != sites.begin() + used;
        };
        auto canonical = [&]() {
            // These are exactly the rotations preserving the normalized product.
            for (unsigned i = 1; i < stabilizer; ++i) {
                std::array<unsigned, max_size> rotated{};
                for (unsigned j = 0; j < size; ++j)
                    rotated[j] = (sites[j] + i * (order / stabilizer)) % order;
                std::sort(rotated.begin(), rotated.begin() + size);
                if (std::lexicographical_compare(rotated.begin(), rotated.begin() + size,
                                                  sites.begin(), sites.begin() + size))
                    return false;
            }
            return true;
        };
        auto enumerate = [&](auto &self, unsigned used, unsigned exponent_sum, unsigned least) -> void {
            if (used + 1 < size) {
                for (unsigned site = least; site < order; ++site) {
                    if (opposite_appears(site, used))
                        continue;
                    sites[used] = site;
                    self(self, used + 1, exponent_sum + site, site);
                }
                return;
            }
            // Normalize the product exponent to [0, gcd(order,size)). The prefix
            // then determines the final site. Repeated roots are allowed.
            for (unsigned product = 0; product < stabilizer; ++product) {
                unsigned last = (product + order - exponent_sum % order) % order;
                if (last < least || opposite_appears(last, used))
                    continue;
                sites[used] = last;
                if (!canonical())
                    continue;
                sum = 0;
                for (unsigned i = 0; i < size; ++i)
                    sum += roots[sites[i]];
                mpz_powm_ui(key.get_mpz_t(), sum.get_mpz_t(), order, field.p.get_mpz_t());
                if (key == 0)
                    throw std::runtime_error("a nonempty reduced sum vanished");
                // Equality of field keys implies equality of this deterministic fingerprint.
                Word fingerprint = 0x9e3779b97f4a7c15ULL;
                for (size_t j = 0; j < mpz_size(key.get_mpz_t()); ++j) {
                    fingerprint ^= Word(mpz_getlimbn(key.get_mpz_t(), j));
                    fingerprint ^= fingerprint >> 30;
                    fingerprint *= 0xbf58476d1ce4e5b9ULL;
                    fingerprint ^= fingerprint >> 27;
                    fingerprint *= 0x94d049bb133111ebULL;
                    fingerprint ^= fingerprint >> 31;
                }
                keys.push_back(fingerprint);
                ++counts[size - 1];
            }
        };
        enumerate(enumerate, 0, 0, 0);
        require(counts[size - 1] == orbit_count(order, size), "incomplete orbit census");
    }
    std::sort(keys.begin(), keys.end());
    require(std::adjacent_find(keys.begin(), keys.end()) == keys.end(), "duplicate orbit fingerprint");
    return counts;
}

void small_control() {
    const mpz_class p = 998244353;
    Field field{p, power(3, (p.get_ui() - 1) / 16, p), 16};
    verify_orbits(field, 16);
    std::array<Word, 16> roots{};
    for (unsigned i = 0; i < roots.size(); ++i)
        roots[i] = power(field.g, i, field.p).get_ui();
    // Use every multiset directly, without product normalization or orbit keys.
    std::map<Word, std::array<int, 8>> by_sum;
    std::array<int, 8> reduced{};
    const Word modulus = p.get_ui();
    auto enumerate = [&](auto &self, unsigned least, unsigned size, Word sum) -> void {
        auto [entry, inserted] = by_sum.emplace(sum, reduced);
        require(inserted || entry->second == reduced, "small-domain sum collision");
        if (size == max_size)
            return;
        for (unsigned i = least; i < roots.size(); ++i) {
            int sign = i < 8 ? 1 : -1;
            reduced[i % 8] += sign;
            self(self, i, size + 1, (sum + roots[i]) % modulus);
            reduced[i % 8] -= sign;
        }
    };
    enumerate(enumerate, 0, 0, 0);
}
} // namespace

int main() {
    small_control();
    for (const std::string name : {"first", "second"}) {
        auto counts = verify_orbits(sponsor_field(name), 256);
        const std::array<Word, max_size> expected{1, 128, 10923, 699136, 35802317};
        require(counts == expected, "incorrect production orbit populations");
        std::cout << name << " disjoint nonzero sum orbits by size";
        for (Word count : counts)
            std::cout << ' ' << count;
        std::cout << '\n';
    }
}
