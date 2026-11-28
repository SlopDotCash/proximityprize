// Enumerate signed septic locator supports subject to six cyclotomic comparisons.
// The companion Python verifier specializes every surviving pair at both named primes.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace {
using Mask = std::uint64_t;
using Wide = __uint128_t;

// A vector in F_3^96. The masks record coordinates equal to +1 or -1.
struct Row {
    Wide positive{}, negative{};
};

Row negate(Row row) { return {row.negative, row.positive}; }

Row add(Row a, Row b) {
    Wide za = ~(a.positive | a.negative), zb = ~(b.positive | b.negative);
    return {(a.positive & zb) | (b.positive & za) | (a.negative & b.negative),
            (a.negative & zb) | (b.negative & za) | (a.positive & b.positive)};
}

int entry(Row row, int j) {
    if ((row.positive >> j) & 1) return 1;
    if ((row.negative >> j) & 1) return 2;
    return 0;
}

void insert(Row &row, int j, int value) {
    if (value % 3 == 1) row.positive |= Wide{1} << j;
    if (value % 3 == 2) row.negative |= Wide{1} << j;
}

int weight(Wide bits) {
    return __builtin_popcountll(static_cast<Mask>(bits)) +
           2 * __builtin_popcountll(static_cast<Mask>(bits >> 64));
}

std::array<std::array<Row, 32>, 128> values;
Row balance;
std::array<int, 2> orbit_counts{};
int survivors = 0;
bool reverse_pivots = false;

int phi(int r, int t) {
    int count = 0;
    for (int sign : {-1, 1})
        for (int j = 0; j < 7; ++j)
            count += ((sign * (1 << j) * r - t) % 128 == 0);
    return count;
}

std::vector<Row> kernel(std::vector<Row> rows) {
    std::vector<int> pivots, free_columns;
    for (int step = 0; step < 96; ++step) {
        int col = reverse_pivots ? 95 - step : step;
        int rank = static_cast<int>(pivots.size());
        int i = rank;
        while (i < static_cast<int>(rows.size()) && entry(rows[i], col) == 0) ++i;
        if (i == static_cast<int>(rows.size())) {
            free_columns.push_back(col);
            continue;
        }
        std::swap(rows[rank], rows[i]);
        if (entry(rows[rank], col) == 2) rows[rank] = negate(rows[rank]);
        for (int j = rank + 1; j < static_cast<int>(rows.size()); ++j) {
            int v = entry(rows[j], col);
            if (v) rows[j] = add(rows[j], v == 1 ? negate(rows[rank]) : rows[rank]);
        }
        pivots.push_back(col);
    }
    for (int i = static_cast<int>(pivots.size()) - 1; i >= 0; --i)
        for (int j = 0; j < i; ++j) {
            int v = entry(rows[j], pivots[i]);
            if (v) rows[j] = add(rows[j], v == 1 ? negate(rows[i]) : rows[i]);
        }
    std::vector<Row> basis;
    for (int col : free_columns) {
        Row vector;
        insert(vector, col, 1);
        for (int i = 0; i < static_cast<int>(pivots.size()); ++i)
            insert(vector, pivots[i], 3 - entry(rows[i], col));
        basis.push_back(vector);
    }
    return basis;
}

void visit(Mask even_sites, bool odd_pair) {
    ++orbit_counts[odd_pair];
    std::vector<int> sites;
    for (int i = 0; i < 64; ++i)
        if ((even_sites >> i) & 1) sites.push_back(2 * i);
    if (odd_pair) {
        sites.push_back(1);
        sites.push_back(65);
    }
    std::vector<Row> rows{balance};
    for (int x : sites) {
        Row forbidden;
        insert(forbidden, (x % 2 == 0) ? x / 2 : 64 + (x % 64) / 2, 1);
        rows.push_back(forbidden);
    }
    for (int j = 1; j < 6; ++j)
        for (int r = 0; r < 32; ++r)
            rows.push_back(add(values[sites[j]][r], negate(values[sites[0]][r])));
    auto basis = kernel(rows);
    int dim = static_cast<int>(basis.size());

    // This permutation changes only the order of the ternary search. Prefer
    // the next vector whose removal leaves the smallest remaining support.
    for (int i = 0; i < dim; ++i) {
        int best = i, best_weight = 129;
        for (int j = i; j < dim; ++j) {
            Wide others = 0;
            for (int k = i; k < dim; ++k)
                if (k != j) others |= basis[k].positive | basis[k].negative;
            if (weight(others) < best_weight) {
                best = j;
                best_weight = weight(others);
            }
        }
        std::swap(basis[i], basis[best]);
    }
    std::vector<Wide> remaining(dim + 1);
    for (int i = dim - 1; i >= 0; --i)
        remaining[i] = remaining[i + 1] | basis[i].positive | basis[i].negative;

    auto search = [&](auto &self, int i, Row partial) -> void {
        Wide fixed = ~remaining[i];
        int a = weight(partial.positive & fixed), b = weight(partial.negative & fixed);
        if (a > 7 || b > 7) return;
        if (i == dim) {
            if (a == 7 && b == 7) {
                ++survivors;
                std::cout << odd_pair << ' ' << even_sites << ' '
                          << static_cast<Mask>(partial.positive) << ' '
                          << static_cast<Mask>(partial.positive >> 64) << ' '
                          << static_cast<Mask>(partial.negative) << ' '
                          << static_cast<Mask>(partial.negative >> 64) << '\n';
            }
            return;
        }
        self(self, i + 1, partial);
        self(self, i + 1, add(partial, basis[i]));
        self(self, i + 1, add(partial, negate(basis[i])));
    };
    search(search, 0, {});
}
} // namespace

int main(int argc, char **argv) {
    if (argc == 2 && std::string_view(argv[1]) == "--reverse-pivots") reverse_pivots = true;
    else if (argc != 1) return 2;
    for (int j = 0; j < 96; ++j) {
        insert(balance, j, j < 64 ? 1 : 2);
        int exponent = j < 64 ? 2 * j : 2 * (j - 64) + 1;
        for (int x = 0; x < 128; ++x)
            for (int r = 0; r < 32; ++r) {
                int count = phi(2 * r + 1, exponent - x);
                if (j >= 64) count += phi(2 * r + 1, exponent + 64 - x);
                insert(values[x][r], j, count);
            }
    }

    std::unordered_set<Mask> seen;
    for (int a = 0; a < 64; ++a)
        for (int b = 0; b < a; ++b)
            for (int c = 0; c < b; ++c)
                for (int d = 0; d < c; ++d) {
                    std::array<int, 4> points{a, b, c, d};
                    Mask mask = 0;
                    for (int x : points) mask |= Mask{1} << x;
                    if (seen.count(mask)) continue;
                    for (int u = 1; u < 128; u += 2)
                        for (int v : {(1 - u) / 2, (65 - u) / 2}) {
                            Mask image = 0;
                            for (int x : points) image |= Mask{1} << ((u * x + v) & 63);
                            seen.insert(image);
                        }
                    visit(mask, true);
                }

    seen.clear();
    for (int a = 1; a < 64; ++a)
        for (int b = 1; b < a; ++b)
            for (int c = 1; c < b; ++c)
                for (int d = 1; d < c; ++d)
                    for (int e = 1; e < d; ++e) {
                        std::array<int, 6> points{0, a, b, c, d, e};
                        Mask mask = 0;
                        for (int x : points) mask |= Mask{1} << x;
                        if (seen.count(mask)) continue;
                        for (int u = 1; u < 64; u += 2)
                            for (int v : points) {
                                Mask image = 0;
                                for (int x : points) image |= Mask{1} << ((u * (x - v)) & 63);
                                seen.insert(image);
                            }
                        visit(mask, false);
                    }
    std::cerr << "Six even orbits " << orbit_counts[0] << ", four even plus odd pair "
              << orbit_counts[1] << ", directed candidates " << survivors << '\n';
    return 0;
}
