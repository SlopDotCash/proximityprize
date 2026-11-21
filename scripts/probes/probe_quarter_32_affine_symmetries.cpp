// Exhaust faithful order-four affine exponent symmetries of saturated 32-site quartets.
// Compile with c++ -O3 -std=c++17. Arithmetic is exact over F_65537.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <utility>
#include <vector>

namespace {
constexpr int prime = 65537;
using Affine = std::pair<int, int>;
using Group = std::array<Affine, 4>;
using Perm = std::array<int, 4>;
using Edge = std::pair<int, int>;
using Row = std::array<int, 24>;
constexpr Affine identity{1, 0};
constexpr Perm identity_perm{0, 1, 2, 3};
constexpr std::array<Edge, 6> edges{{{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}}};

Affine compose(Affine f, Affine g) {
    return {(f.first*g.first) % 32, (f.first*g.second+f.second) % 32};
}

Perm compose(Perm f, Perm g) {
    return {f[g[0]], f[g[1]], f[g[2]], f[g[3]]};
}

std::set<Group> subgroup_classes() {
    std::vector<Affine> group;
    for (int a = 1; a < 32; a += 2)
        for (int b = 0; b < 32; ++b) group.emplace_back(a, b);

    std::set<Group> all;
    for (auto f : group) {
        auto square = compose(f, f);
        if (square != identity && compose(square, square) == identity) {
            Group cyclic{identity, f, square, compose(f, square)};
            std::sort(cyclic.begin(), cyclic.end());
            all.insert(cyclic);
        }
        if (f == identity || square != identity) continue;
        for (auto g : group) {
            if (g <= f || g == identity || compose(g, g) != identity || compose(f, g) != compose(g, f))
                continue;
            Group klein{identity, f, g, compose(f, g)};
            std::sort(klein.begin(), klein.end());
            all.insert(klein);
        }
    }
    std::set<Group> classes;
    for (auto subgroup : all) {
        auto canonical = subgroup;
        for (auto g : group) {
            auto inverse = *std::find_if(group.begin(), group.end(),
                [&](Affine h) { return compose(g, h) == identity; });
            Group conjugate;
            for (int i = 0; i < 4; ++i) conjugate[i] = compose(compose(g, subgroup[i]), inverse);
            std::sort(conjugate.begin(), conjugate.end());
            canonical = std::min(canonical, conjugate);
        }
        classes.insert(canonical);
    }
    return classes;
}

int residue(int64_t value) {
    int r = static_cast<int>(value % prime);
    return r < 0 ? r + prime : r;
}

int power(int x, int n) {
    int y = 1;
    while (n) {
        if (n & 1) y = residue(int64_t(y)*x);
        x = residue(int64_t(x)*x);
        n /= 2;
    }
    return y;
}

struct Field {
    std::array<int, prime> inverse{};
    std::array<std::array<Row, 6>, 32> rows{};
    Field() {
        for (int i = 1; i < prime; ++i) inverse[i] = power(i, prime-2);
        int z = power(3, (prime-1)/32);
        assert(power(z, 16) == prime-1);
        for (int i = 0; i < 32; ++i)
            for (int e = 0; e < 6; ++e) {
                auto [a, b] = edges[e];
                for (int j = 0; j < 8; ++j) {
                    int value = power(z, (i*j) % 32);
                    if (a) rows[i][e][(a-1)*8+j] = value;
                    rows[i][e][(b-1)*8+j] = prime-value;
                }
            }
    }
};

struct Basis {
    std::array<Row, 24> rows{};
    std::array<int, 24> pivots{};
    int rank = 0;
    void add(Row w, const Field& field) {
        for (int t = 0; t < rank; ++t) {
            int j = pivots[t], factor = w[j];
            if (factor)
                for (int k = j; k < 24; ++k) w[k] = residue(w[k]-int64_t(factor)*rows[t][k]);
        }
        for (int j = 0; j < 24; ++j) {
            if (!w[j]) continue;
            int scale = field.inverse[w[j]];
            for (int k = j; k < 24; ++k) w[k] = residue(int64_t(w[k])*scale);
            rows[rank] = w;
            pivots[rank++] = j;
            return;
        }
    }
};

using Placement = std::vector<std::pair<int, int>>;  // (site, edge number)
struct Orbit {
    int size;
    std::vector<Placement> options;
};

std::vector<Orbit> domain_orbits(const Group& group, const std::array<Perm, 4>& perms) {
    std::array<bool, 32> seen{};
    std::vector<Orbit> orbits;
    for (int i = 0; i < 32; ++i) {
        if (seen[i]) continue;
        std::array<int, 4> site{};
        for (int j = 0; j < 4; ++j) {
            auto [a, b] = group[j];
            site[j] = (a*i+b) % 32;
            seen[site[j]] = true;
        }
        Orbit orbit{static_cast<int>(std::set<int>(site.begin(), site.end()).size()), {}};
        for (auto [h, k] : edges) {
            std::set<std::pair<int, int>> placement;
            for (int j = 0; j < 4; ++j) {
                Edge pair = std::minmax(perms[j][h], perms[j][k]);
                int e = static_cast<int>(std::find(edges.begin(), edges.end(), pair)-edges.begin());
                placement.emplace(site[j], e);
            }
            if (static_cast<int>(placement.size()) == orbit.size)
                orbit.options.emplace_back(placement.begin(), placement.end());
        }
        orbits.push_back(orbit);
    }
    return orbits;
}

int64_t count_survivors(const std::vector<Orbit>& ordinary, size_t i, const Basis& basis,
                        std::array<int, 6> counts, const Field& field) {
    if (i == ordinary.size())
        return counts[0] == counts[5] && counts[1] == counts[4] && counts[2] == counts[3];
    int64_t total = 0;
    for (const auto& placement : ordinary[i].options) {
        auto sizes = counts;
        for (auto [site, e] : placement) ++sizes[e];
        if (*std::max_element(sizes.begin(), sizes.end()) > 7) continue;
        auto updated = basis;
        for (auto [site, e] : placement) {
            updated.add(field.rows[site][e], field);
            if (updated.rank >= 23) break;
        }
        if (updated.rank < 23) total += count_survivors(ordinary, i+1, updated, sizes, field);
    }
    return total;
}

int64_t census(Group group, std::array<Perm, 4> perms, const Field& field) {
    auto orbits = domain_orbits(group, perms);
    int64_t total = 0;
    for (int mask = 1; mask < (1 << orbits.size()); ++mask) {
        int holes = 0;
        std::vector<Orbit> ordinary;
        for (size_t j = 0; j < orbits.size(); ++j) {
            if (mask >> j & 1) holes += orbits[j].size;
            else ordinary.push_back(orbits[j]);
        }
        if (holes != 4) continue;
        std::sort(ordinary.begin(), ordinary.end(), [](const Orbit& a, const Orbit& b) {
            return a.options.size() < b.options.size();
        });
        total += count_survivors(ordinary, 0, Basis{}, {}, field);
    }
    return total;
}
}  // namespace

int main() {
    Field field;
    int cyclic_classes = 0, klein_classes = 0;
    for (auto group : subgroup_classes()) {
        auto order_four = std::find_if(group.begin(), group.end(),
            [](Affine x) { return compose(x, x) != identity; });
        if (order_four != group.end()) {
            ++cyclic_classes;
            auto f = *order_four, square = compose(f, f);
            Perm r{1, 2, 3, 0};
            auto n = census({identity, f, square, compose(f, square)},
                            {identity_perm, r, compose(r, r), compose(r, compose(r, r))}, field);
            std::cout << "cyclic " << f.first << ' ' << f.second << " survivors " << n << '\n';
            if (n) return 1;
        } else {
            ++klein_classes;
            std::vector<Affine> generators;
            for (auto g : group) if (g != identity) generators.push_back(g);
            auto f = generators[0], g = generators[1];
            constexpr Perm single{1, 0, 2, 3}, dbl{2, 3, 0, 1};
            for (auto [t, r] : std::array<std::pair<Perm, Perm>, 4>{{
                     {dbl, {1, 0, 3, 2}}, {dbl, {2, 1, 0, 3}},
                     {single, {0, 1, 3, 2}}, {single, {1, 0, 3, 2}}}}) {
                auto n = census({identity, f, g, compose(f, g)},
                                {identity_perm, t, r, compose(t, r)}, field);
                std::cout << "Klein " << f.first << ' ' << f.second << ' '
                          << g.first << ' ' << g.second << " survivors " << n << '\n';
                if (n) return 1;
            }
        }
    }
    assert(cyclic_classes == 5 && klein_classes == 6);
}
