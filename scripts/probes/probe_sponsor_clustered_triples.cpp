// Compare non-antipodal triples in small subgroup cosets, up to FULL subgroup scaling.
// Build with C++17 and GMP. The order-65536 test uses about 5.4 GiB of memory.
#include "sponsor_phi_field.hpp"

#include <algorithm>
#include <atomic>
#include <future>
#include <iostream>
#include <map>
#include <set>
#include <vector>

struct TripleTable {
    Field field;
    Word m;
    std::vector<mpz_class> roots;

    TripleTable(Field f, Word order) : field(f), m(order), roots(m) {
        require(m >= 2 && m <= 65536 && (m & (m - 1)) == 0 && field.n % m == 0, "invalid order");
        require(power(field.g, field.n, field.p) == 1 &&
                    power(field.g, field.n / 2, field.p) == field.p - 1,
                "incorrect ambient order");
        const mpz_class step = power(field.g, field.n / m, field.p);
        roots[0] = 1;
        for (Word i = 1; i < m; ++i)
            roots[i] = (roots[i - 1] * step) % field.p;
        require(roots[m / 2] == field.p - 1 && (roots[m - 1] * step) % field.p == 1,
                "incorrect suborder");
    }

    // Gaps a,b,c=m-a-b are in positive cyclic order; zero denotes a repeated vertex.
    // The least rotation has a <= b,c. If c==a<b the rotation c,a,b precedes it.
    // A gap equal to half the order is exactly an antipodal pair.
    template <typename Visit> void row(Word a, Visit visit) const {
        for (Word b = a; b <= m - 2 * a; ++b) {
            const Word c = m - a - b;
            if ((c == a && a < b) || a == m / 2 || b == m / 2 || c == m / 2)
                continue;
            visit(b);
        }
    }

    void evaluate(Word a, Word b, mpz_class &base, mpz_class &v) const {
        base = 1 + roots[a] + roots[a + b];
        mpz_powm_ui(v.get_mpz_t(), base.get_mpz_t(), field.n, field.p.get_mpz_t());
    }
};

int main(int argc, char **argv) try {
    require(argc == 4, "usage: clustered first|second|sextic-control suborder workers");
    const Word m = std::stoull(argv[2]);
    require(m >= 2 && m <= 65536, "suborder out of range");
    const unsigned workers = std::stoul(argv[3]);
    require(workers >= 1 && workers <= 16, "worker count out of range");
    const TripleTable t(sponsor_field(argv[1]), m);
    const Word expected = (m * m + 2) / 6;
    std::vector<Word> tags(expected);
    std::atomic<Word> next{0}, zeros{0}, ones{0};
    std::vector<std::future<void>> tasks;
    for (unsigned w = 0; w < workers; ++w) {
        tasks.push_back(std::async(std::launch::async, [&, w] {
            mpz_class base, v;
            Word z = 0, o = 0;
            for (Word a = w; a <= m / 3; a += workers) {
                Word count = 0;
                t.row(a, [&](Word) { ++count; });
                Word pos = next.fetch_add(count, std::memory_order_relaxed), end = pos + count;
                require(end <= expected, "enumerated too many triples");
                t.row(a, [&](Word b) {
                    t.evaluate(a, b, base, v);
                    tags[pos++] = v.get_ui();
                    z += (v == 0);
                    o += (v == 1);
                });
                require(pos == end, "incomplete row");
            }
            zeros.fetch_add(z, std::memory_order_relaxed);
            ones.fetch_add(o, std::memory_order_relaxed);
        }));
    }
    for (auto &task : tasks)
        task.get();
    require(next == expected, "incomplete cyclic enumeration");
    std::sort(tags.begin(), tags.end());
    std::set<Word> repeated;
    for (Word i = 1; i < expected; ++i)
        if (tags[i - 1] == tags[i])
            repeated.insert(tags[i]);
    Word excess = 0;
    if (!repeated.empty()) {
        std::map<mpz_class, Word> exact;
        mpz_class base, v;
        for (Word a = 0; a <= m / 3; ++a)
            t.row(a, [&](Word b) {
                t.evaluate(a, b, base, v);
                if (repeated.count(v.get_ui()) && exact[v]++ > 0)
                    ++excess;
            });
    }
    std::cout << "field=" << argv[1] << " ambient=" << t.field.n << " suborder=" << m
              << " necklaces=" << expected << " repeated_low_limbs=" << repeated.size()
              << " repeated_field_values=" << excess << " zeros=" << zeros << " ones=" << ones
              << '\n';
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
