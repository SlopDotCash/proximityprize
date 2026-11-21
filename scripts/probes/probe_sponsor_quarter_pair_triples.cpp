// Exact projective comparison of triples containing a pair in one mu_4 coset.
// A production run stores 2n-5 low limbs in memory (16 GiB at n=2^30).
#include "sponsor_phi_field.hpp"
#include <algorithm>
#include <array>
#include <future>
#include <iostream>
#include <set>
#include <vector>

struct Arm {
    mpz_class constant;
    std::vector<Word> omitted;
    Word offset;

    Word index(Word exponent) const {
        auto before = std::lower_bound(omitted.begin(), omitted.end(), exponent) - omitted.begin();
        return offset + exponent - before;
    }
};

struct TripleScan {
    Field f;
    std::array<Arm, 2> arms;

    explicit TripleScan(Field field)
        : f(field),
          arms{Arm{2, {f.n / 2}, 0},
               Arm{1 + power(f.g, f.n / 4, f.p), {0, f.n / 4, f.n / 2, 3 * f.n / 4}, f.n - 1}} {
        require(f.n % 4 == 0 && power(f.g, f.n, f.p) == 1 && power(f.g, f.n / 2, f.p) == f.p - 1,
                "incorrect group order");
    }

    template <typename Callback>
    void visit(const Arm &arm, Word lo, Word hi, Callback callback) const {
        mpz_class x = power(f.g, lo, f.p), base, signature;
        Word index = arm.index(lo);
        auto next = std::lower_bound(arm.omitted.begin(), arm.omitted.end(), lo);
        for (Word exponent = lo; exponent < hi; ++exponent) {
            if (next != arm.omitted.end() && *next == exponent) {
                ++next;
            } else {
                mpz_add(base.get_mpz_t(), arm.constant.get_mpz_t(), x.get_mpz_t());
                mpz_powm_ui(signature.get_mpz_t(), base.get_mpz_t(), f.n, f.p.get_mpz_t());
                callback(index++, exponent, signature);
            }
            mpz_mul(x.get_mpz_t(), x.get_mpz_t(), f.g.get_mpz_t());
            mpz_mod(x.get_mpz_t(), x.get_mpz_t(), f.p.get_mpz_t());
        }
        require(index == arm.index(hi) && x == power(f.g, hi, f.p), "incomplete scan shard");
    }
};

using Iter = std::vector<Word>::iterator;
using Range = std::pair<Iter, Iter>;

// Partition by the high bits, then sort each disjoint interval in parallel.
void sort_tags(std::vector<Word> &tags, unsigned workers) {
    std::vector<Range> ranges{{tags.begin(), tags.end()}};
    for (unsigned bits = 0; ranges.size() * 2 <= workers; ++bits) {
        const Word mask = Word(1) << (63 - bits);
        std::vector<std::future<Iter>> splits;
        for (Range range : ranges) {
            splits.push_back(std::async(std::launch::async, [range, mask] {
                const auto [lo, hi] = range;
                return std::partition(lo, hi, [mask](Word x) { return (x & mask) == 0; });
            }));
        }
        std::vector<Range> halves;
        for (std::size_t j = 0; j < ranges.size(); ++j) {
            auto mid = splits[j].get();
            halves.emplace_back(ranges[j].first, mid);
            halves.emplace_back(mid, ranges[j].second);
        }
        ranges = std::move(halves);
    }
    std::vector<std::future<void>> sorts;
    for (Range range : ranges)
        sorts.push_back(std::async(std::launch::async, [range] { std::sort(range.first, range.second); }));
    for (auto &sort : sorts)
        sort.get();
}

int main(int argc, char **argv) try {
    require(argc == 3, "usage: quarter-pairs first|second|sextic-control workers");
    const unsigned workers = std::stoul(argv[2]);
    require(workers >= 1 && workers <= 16, "worker count out of range");
    const TripleScan scan(sponsor_field(argv[1]));
    const Word n = scan.f.n;
    std::vector<Word> tags(2 * n - 5);
    std::vector<std::future<std::array<Word, 2>>> jobs;
    for (unsigned w = 0; w < workers; ++w) {
        jobs.push_back(std::async(std::launch::async, [&, w] {
            std::array<Word, 2> exceptional{};
            for (const auto &arm : scan.arms) {
                scan.visit(arm, n * w / workers, n * (w + 1) / workers,
                           [&](Word index, Word, const mpz_class &v) {
                               tags[index] = v.get_ui();
                               exceptional[0] += (v == 0);
                               exceptional[1] += (v == 1);
                           });
            }
            return exceptional;
        }));
    }
    Word zeros = 0, ones = 0;
    for (auto &job : jobs) {
        auto counts = job.get();
        zeros += counts[0];
        ones += counts[1];
    }
    sort_tags(tags, workers);
    std::set<Word> repeated;
    for (std::size_t i = 1; i < tags.size(); ++i) {
        require(tags[i - 1] <= tags[i], "invalid partition sort");
        if (tags[i - 1] == tags[i])
            repeated.insert(tags[i]);
    }
    const Word checked = tags.size();
    std::vector<Word>().swap(tags);
    Word excess = 0;
    if (!repeated.empty()) {
        std::map<mpz_class, Word> occurrences;
        for (const auto &arm : scan.arms) {
            scan.visit(arm, 0, n, [&](Word, Word, const mpz_class &v) {
                if (repeated.count(v.get_ui()) && occurrences[v]++ > 0)
                    ++excess;
            });
        }
    }
    std::cout << "field=" << argv[1] << " n=" << n << " checked=" << checked
              << " duplicate_tags=" << repeated.size() << " excess_field_values=" << excess
              << " zeros=" << zeros << " ones=" << ones << '\n';
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
