// Count exact (product, nonzero locator value) signatures on the normalized roots.
// Build with C++17 and GMP, as documented in antipodal-locator-fresh-energy.md.
#include "sponsor_phi_field.hpp"

#include <algorithm>
#include <array>
#include <iostream>
#include <map>
#include <vector>

namespace {
struct Counts {
    Word subsets = 0;
    Word energy = 0;
    Word largest = 0;
    // Per product exponent, histogram[m] counts values of multiplicity m.
    std::vector<std::vector<Word>> histograms;
};

Word choose(unsigned n, unsigned k) {
    Word result = 1;
    for (unsigned i = 1; i <= k; ++i)
        result = result * (n - i + 1) / i;
    return result;
}

std::vector<mpz_class> locator_factors(const Field &field, unsigned order) {
    require(field.n % order == 0, "subgroup order must divide the domain length");
    mpz_class generator = power(field.g, field.n / order, field.p);
    require(power(generator, order / 2, field.p) == field.p - 1, "wrong dyadic subgroup");
    std::vector<mpz_class> factors(order);
    mpz_class root = 1;
    for (unsigned exponent = 0; exponent < order; ++exponent) {
        factors[exponent] = (field.p + 1 - root) % field.p;
        root = (root * generator) % field.p;
    }
    return factors;
}

Counts signature_counts(const Field &field, const std::vector<mpz_class> &factors,
                        unsigned size) {
    const unsigned order = factors.size();
    Counts counts;
    counts.histograms.resize(order);
    // For a prescribed product, the exponents of the prefix determine the final one.
    // Strict increase excludes both the anchor exponent zero and repeated roots.
    for (unsigned product = 0; product < order; ++product) {
        std::vector<mpz_class> values;
        values.reserve(choose(order - 1, size) / order + 100);
        auto collect = [&](auto &self, unsigned last, unsigned left, unsigned sum,
                           const mpz_class &value) -> void {
            if (left == 1) {
                unsigned final = (product + order - sum % order) % order;
                if (final > last)
                    values.emplace_back((value * factors[final]) % field.p);
                return;
            }
            for (unsigned next = last + 1; next + left <= order; ++next)
                self(self, next, left - 1, sum + next, (value * factors[next]) % field.p);
        };
        collect(collect, 0, size, 0, 1);
        std::sort(values.begin(), values.end());
        counts.subsets += values.size();
        for (auto begin = values.begin(); begin != values.end();) {
            auto end = std::find_if(begin + 1, values.end(), [&](const mpz_class &x) {
                return x != *begin;
            });
            Word multiplicity = end - begin;
            counts.energy += multiplicity * multiplicity;
            counts.largest = std::max(counts.largest, multiplicity);
            auto &histogram = counts.histograms[product];
            if (histogram.size() <= multiplicity)
                histogram.resize(multiplicity + 1);
            ++histogram[multiplicity];
            begin = end;
        }
    }
    require(counts.subsets == choose(order - 1, size), "incomplete subset census");
    return counts;
}

// Exact integer square root. Census products passed here fit in a 64-bit word.
Word integer_sqrt(Word n) {
    Word low = 0, high = Word(1) << 32;
    while (high - low > 1) {
        Word mid = low + (high - low) / 2;
        if (mid <= n / mid)
            low = mid;
        else
            high = mid;
    }
    return low;
}

// A fixed target pairs distinct locator values bijectively. Pairing multiplicities
// from largest to smallest can only increase that product-conditioned count.
Word rearranged_dot(const std::vector<Word> &a, const std::vector<Word> &b) {
    size_t i = a.size(), j = b.size();
    Word left = 0, right = 0, total = 0;
    while (true) {
        while (!left && i)
            left = a[--i];
        while (!right && j)
            right = b[--j];
        if (!left || !right)
            return total;
        Word use = std::min(left, right);
        total += i * j * use;
        left -= use;
        right -= use;
    }
}

Word product_pairing(const Counts &left, const Counts &right) {
    const auto &a = left.histograms;
    const auto &b = right.histograms;
    Word largest = 0;
    for (size_t target = 0; target < a.size(); ++target) {
        Word possible = 0;
        for (size_t e = 0; e < a.size(); ++e)
            possible += rearranged_dot(a[e], b[(target + a.size() - e) % a.size()]);
        largest = std::max(largest, possible);
    }
    return largest;
}

std::array<Word, 10> population_caps(const std::array<Counts, 5> &counts, unsigned sites) {
    std::array<Word, 10> caps{1};
    for (unsigned size = 1; size <= 4; ++size)
        caps[size] = counts[size].largest;
    for (unsigned size = 5; size <= 9; ++size) {
        caps[size] = sites * caps[size - 1] / size;
        for (unsigned a = 1; a <= 4; ++a) {
            unsigned b = size - a;
            if (b <= 4) {
                Word energy_bound = integer_sqrt(counts[a].energy * counts[b].energy);
                caps[size] = std::min(caps[size], energy_bound / choose(size, a));
                caps[size] = std::min(caps[size], product_pairing(counts[a], counts[b])
                    / choose(size, a));
            }
            Word deletion_bound = choose(sites, b) * caps[a] / choose(size, a);
            caps[size] = std::min(caps[size], deletion_bound);
        }
    }
    return caps;
}

// Independent small control. Enumerate each subset by a bit mask and compare full
// signatures, including the nine-subset multiplicity against the derived cap.
void small_control() {
    Field field = sponsor_field("primitive-control");
    auto factors = locator_factors(field, 16);
    std::array<std::map<std::pair<unsigned, Word>, Word>, 10> signatures;
    for (unsigned mask = 0; mask < (1U << 15); ++mask) {
        unsigned sum = 0, size = 0;
        Word value = 1;
        for (unsigned j = 1; j < 16; ++j) {
            if (mask & (1U << (j - 1))) {
                ++size;
                sum += j;
                value = value * factors[j].get_ui() % field.p.get_ui();
            }
        }
        if (size <= 9)
            ++signatures[size][{sum % 16, value}];
    }
    std::array<Counts, 5> counts{};
    for (unsigned k = 1; k <= 4; ++k) {
        counts[k] = signature_counts(field, factors, k);
        Word energy = 0, largest = 0;
        for (const auto &entry : signatures[k]) {
            energy += entry.second * entry.second;
            largest = std::max(largest, entry.second);
        }
        require(counts[k].energy == energy && counts[k].largest == largest, "small energy");
    }
    auto caps = population_caps(counts, 15);
    for (unsigned k = 0; k <= 9; ++k)
        for (const auto &entry : signatures[k])
            require(entry.second <= caps[k], "small population bound");
}
} // namespace

int main() {
    small_control();
    for (const std::string name : {"first", "second"}) {
        Field field = sponsor_field(name);
        auto factors = locator_factors(field, 128);
        std::array<Counts, 5> counts{};
        for (unsigned k = 1; k <= 4; ++k) {
            counts[k] = signature_counts(field, factors, k);
            std::cout << name << " size " << k << " subsets " << counts[k].subsets
                      << " energy " << counts[k].energy << " largest " << counts[k].largest << '\n';
        }
        require(counts[4].energy == 11202567 && counts[4].largest == 6, "production energy");
        auto caps = population_caps(counts, 127);
        std::cout << "caps";
        for (Word cap : caps)
            std::cout << ' ' << cap;
        std::cout << '\n';
        const std::array<Word, 10> expected{1, 1, 1, 2, 6, 98, 1746, 19022, 160036, 2258285};
        require(caps == expected && 255 * caps[9] == 575862675, "production cap");
        Word orientations = (choose(256, 2) - 128) / choose(6, 2);
        Word six_cap = orientations * caps[6] + caps[7];
        require(orientations == 2167 && six_cap == 3802604 && 255 * six_cap == 969664020,
                "six-singleton cap");
        Word h = field.n / 256;
        Word budget = name == "first" ? (Word(1) << 30) : (Word(1) << 31);
        Word agreement_bound = 19 * h - 1 + (255 * h + 1) * caps[9] / (budget + 1);
        Word floor = name == "first" ? 991800586 : 992925318;
        require(field.n - agreement_bound == floor, "restricted radius");
        Word six_agreement_bound = 19 * h - 1 + (255 * h + 1) * six_cap / (budget + 1);
        require(field.n - six_agreement_bound == (name == "first" ? 990262299U : 992156174U),
                "six-singleton restricted radius");
    }
}
