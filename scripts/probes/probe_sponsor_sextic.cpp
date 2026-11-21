// Compare the nonzero H-H cosets to 2(H-H) and to 3H-H at n=2^30.
// c++ -O3 -std=c++17 probe_sponsor_sextic.cpp -lgmpxx -lgmp -o sextic
// sextic first|second|sextic-control [workers]
#include "sponsor_phi_field.hpp"
#include <algorithm>
#include <array>
#include <atomic>
#include <future>
#include <iostream>
#include <memory>
#include <set>
#include <vector>

enum class Family { difference, doubled, triple };

template <class Visit> void visit(const Field &f, Family family, Word lo, Word hi, Visit fn) {
    mpz_class x = power(f.g, lo, f.p), base, signature;
    const mpz_class two_power = power(2, f.n, f.p);
    for (Word i = lo; i < hi; ++i) {
        if (family == Family::triple)
            mpz_ui_sub(base.get_mpz_t(), 3, x.get_mpz_t());
        else
            mpz_sub_ui(base.get_mpz_t(), x.get_mpz_t(), 1);
        mpz_powm_ui(signature.get_mpz_t(), base.get_mpz_t(), f.n, f.p.get_mpz_t());
        if (family == Family::doubled) {
            mpz_mul(signature.get_mpz_t(), signature.get_mpz_t(), two_power.get_mpz_t());
            mpz_mod(signature.get_mpz_t(), signature.get_mpz_t(), f.p.get_mpz_t());
        }
        fn(i, signature);
        mpz_mul(x.get_mpz_t(), x.get_mpz_t(), f.g.get_mpz_t());
        mpz_mod(x.get_mpz_t(), x.get_mpz_t(), f.p.get_mpz_t());
    }
    require(x == power(f.g, hi, f.p), "incorrect endpoint");
}

Word length(const Field &f, Family family) {
    // Triple: omit x=1 because 3-1 is the known value 2. The remaining
    // ratios are directed and have no inversion reduction.
    return family == Family::triple ? f.n - 1 : f.n / 2;
}

template <class Visit> void sweep(const Field &f, Family family, unsigned workers, Visit fn) {
    const Word count = length(f, family);
    std::vector<std::future<void>> tasks;
    for (unsigned w = 0; w < workers; ++w) {
        const Word lo = 1 + count * w / workers, hi = 1 + count * (w + 1) / workers;
        tasks.push_back(std::async(std::launch::async, [&, w, lo, hi] {
            visit(f, family, lo, hi, [&](Word i, const mpz_class &v) { fn(w, i, v); });
        }));
    }
    for (auto &t : tasks)
        t.get();
}

// Equality in F_p forces equality of the index and all four selected bits.
// Positive filter answers are only a speed optimization and receive exact checks.
class Filter {
    const Word size;
    std::unique_ptr<std::atomic<Word>[]> words;
    std::pair<Word, Word> address(const mpz_class &v) const {
        const Word idx = v.get_ui() & (size - 1);
        const Word upper = mpz_getlimbn(v.get_mpz_t(), 1);
        Word mask = 0;
        for (unsigned shift : {0u, 8u, 16u, 24u})
            mask |= Word(1) << ((upper >> shift) & 63);
        return {idx, mask};
    }

  public:
    explicit Filter(Word s) : size(s), words(new std::atomic<Word>[s]) {
        for (Word i = 0; i < s; ++i)
            words[i].store(0, std::memory_order_relaxed);
    }
    void add(const mpz_class &v) {
        auto [i, m] = address(v);
        words[i].fetch_or(m, std::memory_order_relaxed);
    }
    bool possible(const mpz_class &v) const {
        auto [i, m] = address(v);
        return (words[i].load(std::memory_order_relaxed) & m) == m;
    }
};

struct Screen {
    std::vector<Word> tags;
    // A smaller secondary bitset avoids a binary search on most base values.
    std::vector<Word> index;
    explicit Screen(Word words) : index(words) {}
    void prepare(std::vector<std::vector<Word>> &local) {
        for (const auto &part : local)
            tags.insert(tags.end(), part.begin(), part.end());
        std::sort(tags.begin(), tags.end());
        tags.erase(std::unique(tags.begin(), tags.end()), tags.end());
        for (auto tag : tags)
            index[(tag >> 6) & (index.size() - 1)] |= Word(1) << (tag & 63);
    }
    bool has(Word tag) const {
        if (!(index[(tag >> 6) & (index.size() - 1)] & (Word(1) << (tag & 63))))
            return false;
        return std::binary_search(tags.begin(), tags.end(), tag);
    }
};

int main(int argc, char **argv) try {
    require(argc == 2 || argc == 3, "usage: sextic first|second|sextic-control [workers]");
    const Field f = sponsor_field(argv[1]);
    const unsigned workers = argc == 3 ? std::stoul(argv[2]) : 4;
    require(workers >= 1 && workers <= 16, "invalid worker count");
    require(power(f.g, f.n, f.p) == 1 && power(f.g, f.n / 2, f.p) == f.p - 1, "incorrect order");
    const bool small = f.n < 1024;
    const std::array<Family, 2> foreign{Family::doubled, Family::triple};
    std::array<Screen, 2> screen{Screen(small ? 16 : 1UL << 21), Screen(small ? 16 : 1UL << 21)};
    {
        Filter filter(small ? 16 : 1UL << 27);
        sweep(f, Family::difference, workers,
              [&](unsigned, Word, const mpz_class &v) { filter.add(v); });
        for (unsigned j = 0; j < 2; ++j) {
            std::vector<std::vector<Word>> local(workers);
            sweep(f, foreign[j], workers, [&](unsigned w, Word, const mpz_class &v) {
                if (filter.possible(v))
                    local[w].push_back(v.get_ui());
            });
            screen[j].prepare(local);
            std::cerr << "screened " << length(f, foreign[j]) << " field values; retained "
                      << screen[j].tags.size() << " low limbs\n";
        }
    }
    using Witness = std::pair<mpz_class, Word>;
    std::vector<std::array<std::vector<Witness>, 2>> candidates(workers);
    sweep(f, Family::difference, workers, [&](unsigned w, Word i, const mpz_class &v) {
        for (unsigned j = 0; j < 2; ++j)
            if (screen[j].has(v.get_ui()))
                candidates[w][j].emplace_back(v, i);
    });
    for (unsigned j = 0; j < 2; ++j) {
        std::multimap<mpz_class, Word> exact;
        for (const auto &part : candidates)
            exact.insert(part[j].begin(), part[j].end());
        Word hits = 0;
        if (!exact.empty()) {
            visit(f, foreign[j], 1, 1 + length(f, foreign[j]), [&](Word i, const mpz_class &v) {
                auto [it, end] = exact.equal_range(v);
                for (; it != end; ++it) {
                    ++hits;
                    std::cout << "hit family=" << j << " base=" << it->second << " other=" << i
                              << '\n';
                }
            });
        }
        std::cout << "field=" << argv[1] << " family=" << (j == 0 ? "doubled" : "triple")
                  << " base=" << f.n / 2 << " other=" << length(f, foreign[j])
                  << " common_low_limb_entries=" << exact.size() << " exact_pairs=" << hits << '\n';
    }
    std::cout << "three_in_H=" << (power(3, f.n, f.p) == 1 ? "true" : "false") << '\n';
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
