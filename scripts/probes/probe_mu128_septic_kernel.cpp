// Enumerate signed septic locator supports subject to six cyclotomic comparisons.
// The companion Python verifier specializes every surviving pair at both named primes.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string_view>
#include <utility>
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
int support_size = 7;
int test_count = 6;
bool direct_search = false;

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

struct InformationSet {
    std::vector<Row> systematic;
    Wide mask{};
};

std::vector<InformationSet> pack(const std::vector<Row> &basis, unsigned seed) {
    std::array<int, 96> capacity{};
    for (int j = 0; j < 96; ++j) capacity[j] = 1 + (j >= 64);
    const int dim = static_cast<int>(basis.size());
    std::vector<InformationSet> result;
    while (static_cast<int>(result.size()+1)*dim <= 128) {
        std::array<int, 96> order{};
        for (int j = 0; j < 96; ++j) order[j] = j;
        for (int j = 95; j > 0; --j) {
            seed = seed*1664525u + 1013904223u;
            std::swap(order[j], order[seed % (j+1)]);
        }
        std::stable_sort(order.begin(), order.end(), [&](int j, int k) {
            return capacity[j] > capacity[k];
        });
        InformationSet next{basis};
        int rank = 0;
        for (int col : order) {
            if (capacity[col] == 0) continue;
            int pivot = rank;
            while (pivot < dim && !entry(next.systematic[pivot], col)) ++pivot;
            if (pivot == dim) continue;
            auto &rows = next.systematic;
            std::swap(rows[pivot], rows[rank]);
            if (entry(rows[rank], col) == 2) rows[rank] = negate(rows[rank]);
            for (int j = 0; j < dim; ++j) {
                int v = entry(rows[j], col);
                if (j != rank && v) rows[j] = add(rows[j], v == 1 ? negate(rows[rank]) : rows[rank]);
            }
            --capacity[col];
            next.mask |= Wide{1} << col;
            if (++rank == dim) break;
        }
        if (rank < dim) break;
        result.push_back(std::move(next));
    }
    return result;
}

int cardinality(Wide bits) {
    return __builtin_popcountll(static_cast<Mask>(bits)) +
            __builtin_popcountll(static_cast<Mask>(bits >> 64));
}

void emit(Row candidate, Mask even_sites, bool odd_pair) {
    ++survivors;
    std::cout << odd_pair << ' ' << even_sites << ' '
              << static_cast<Mask>(candidate.positive) << ' '
              << static_cast<Mask>(candidate.positive >> 64) << ' '
              << static_cast<Mask>(candidate.negative) << ' '
              << static_cast<Mask>(candidate.negative >> 64) << '\n';
}

void sparse_search(const std::vector<Row> &basis, Mask even_sites, bool odd_pair) {
    if (basis.empty()) return;
    std::vector<InformationSet> sets;
    for (unsigned seed = 0; seed < 8 && sets.size() < 4; ++seed) {
        auto candidate = pack(basis, 12345u+seed);
        if (candidate.size() > sets.size()) sets = std::move(candidate);
    }
    if (sets.empty()) throw std::logic_error("nonzero kernel lacks an information set");
    const int cutoff = 2*support_size / static_cast<int>(sets.size());
    for (std::size_t k = 0; k < sets.size(); ++k) {
        const auto &rows = sets[k].systematic;
        auto search = [&](auto &self, int first, int used, Row v) -> void {
            if (weight(v.positive) == support_size && weight(v.negative) == support_size) {
                bool first_set = true;
                for (std::size_t j = 0; j < k; ++j) {
                    if (cardinality((v.positive | v.negative) & sets[j].mask) <= cutoff)
                        first_set = false;
                }
                if (first_set) emit(v, even_sites, odd_pair);
            }
            if (used == cutoff) return;
            for (int j = first; j < static_cast<int>(rows.size()); ++j) {
                self(self, j+1, used+1, add(v, rows[j]));
                self(self, j+1, used+1, add(v, negate(rows[j])));
            }
        };
        search(search, 0, 0, {});
    }
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
    for (int j = 1; j < test_count; ++j)
        for (int r = 0; r < 32; ++r)
            rows.push_back(add(values[sites[j]][r], negate(values[sites[0]][r])));
    auto basis = kernel(rows);
    if (test_count == 5 && !direct_search) {
        sparse_search(basis, even_sites, odd_pair);
        return;
    }
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
        if (a > support_size || b > support_size) return;
        if (i == dim) {
            if (a == support_size && b == support_size) emit(partial, even_sites, odd_pair);
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
    for (int i = 1; i < argc; ++i) {
        std::string_view option(argv[i]);
        if (option == "--reverse-pivots") reverse_pivots = true;
        else if (option == "--six-roots") support_size = 6;
        else if (option == "--five-roots") support_size = 5;
        else if (option == "--five-tests") test_count = 5;
        else if (option == "--direct-search") direct_search = true;
        else return 2;
    }
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

    for (bool odd_pair : {true, false}) {
        std::unordered_set<Mask> seen;
        const int minimum = odd_pair ? 0 : 1;
        auto subsets = [&](auto &self, int upper, int left, Mask mask) -> void {
            if (left > 0) {
                for (int j = minimum+left-1; j < upper; ++j)
                    self(self, j, left-1, mask | (Mask{1} << j));
                return;
            }
            if (seen.count(mask)) return;
            std::vector<int> points;
            for (int j = 0; j < 64; ++j)
                if ((mask >> j) & 1) points.push_back(j);
            auto mark = [&](int u, int v) {
                Mask image = 0;
                for (int x : points) image |= Mask{1} << ((u*x+v) & 63);
                seen.insert(image);
            };
            if (odd_pair) {
                for (int u = 1; u < 128; u += 2) {
                    mark(u, (1-u)/2);
                    mark(u, (65-u)/2);
                }
            } else {
                for (int u = 1; u < 64; u += 2)
                    for (int v : points) mark(u, -u*v);
            }
            visit(mask, odd_pair);
        };
        subsets(subsets, 64, test_count-(odd_pair ? 2 : 1), odd_pair ? 0 : Mask{1});
    }
    const char *shape = test_count == 5 ? "Five even orbits " : "Six even orbits ";
    const char *mixed = test_count == 5 ? ", three even plus odd pair " : ", four even plus odd pair ";
    std::cerr << shape << orbit_counts[0] << mixed << orbit_counts[1]
              << ", directed candidates " << survivors << '\n';
    return 0;
}
