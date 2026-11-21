// Exhaust faithful order-four affine exponent symmetries of saturated 32-site quartets.
// Compile with c++ -O3 -std=c++17. Arithmetic is exact over F_65537.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <string>
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
    uint32_t sites;
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
        Orbit orbit{static_cast<int>(std::set<int>(site.begin(), site.end()).size()), 0, {}};
        for (int index : site) orbit.sites |= uint32_t(1) << index;
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
                        std::array<int, 6> counts, const Field& field,
                        std::array<uint32_t, 6> masks, bool emit,
                        const std::vector<std::array<int, 6>>& relabel, uint32_t stabilizer) {
    if (i == ordinary.size()) {
        if (counts[0] != counts[5] || counts[1] != counts[4] || counts[2] != counts[3]) return 0;
        if (emit) {
            std::cout << "layout";
            for (auto m : masks) std::cout << ' ' << m;
            std::cout << '\n';
        }
        return 1;
    }
    int64_t total = 0;
    for (const auto& placement : ordinary[i].options) {
        int first_edge = placement.front().second;
        bool canonical = true;
        uint32_t next_stabilizer = 0;
        for (size_t j = 0; j < relabel.size(); ++j) if (stabilizer >> j & 1) {
            int alternative = relabel[j][first_edge];
            if (alternative < first_edge) { canonical = false; break; }
            if (alternative == first_edge) next_stabilizer |= uint32_t(1) << j;
        }
        if (!canonical) continue;
        auto sizes = counts;
        for (auto [site, e] : placement) ++sizes[e];
        if (*std::max_element(sizes.begin(), sizes.end()) > 7) continue;
        int minimum = std::max(sizes[0], sizes[5]) + std::max(sizes[1], sizes[4]) + std::max(sizes[2], sizes[3]);
        if (minimum > 14) continue;
        auto updated = basis;
        for (auto [site, e] : placement) {
            updated.add(field.rows[site][e], field);
            if (updated.rank >= 23) break;
        }
        if (updated.rank < 23) {
            auto selected = masks;
            for (auto [site, e] : placement) selected[e] |= uint32_t(1) << site;
            total += count_survivors(ordinary, i+1, updated, sizes, field, selected, emit, relabel, next_stabilizer);
        }
    }
    return total;
}

int64_t census(Group group, std::array<Perm, 4> perms, const Field& field, bool emit = false) {
    auto orbits = domain_orbits(group, perms);
    std::vector<std::array<int, 6>> relabel;
    Perm perm = identity_perm;
    do {
        if (!std::all_of(perms.begin(), perms.end(), [&](Perm h) { return compose(perm, h) == compose(h, perm); }))
            continue;
        std::array<int, 6> label{};
        for (int e = 0; e < 6; ++e) {
            auto [a, b] = edges[e];
            Edge f = std::minmax(perm[a], perm[b]);
            label[e] = static_cast<int>(std::find(edges.begin(), edges.end(), f)-edges.begin());
        }
        relabel.push_back(label);
    } while (std::next_permutation(perm.begin(), perm.end()));
    std::vector<Affine> centralizer;
    for (int a = 1; a < 32; a += 2) for (int b = 0; b < 32; ++b) {
        Affine f{a, b};
        if (std::all_of(group.begin(), group.end(), [&](Affine h) { return compose(f, h) == compose(h, f); }))
            centralizer.push_back(f);
    }
    int64_t total = 0;
    for (int mask = 1; mask < (1 << orbits.size()); ++mask) {
        int holes = 0;
        uint32_t sites = 0;
        std::vector<Orbit> ordinary;
        for (size_t j = 0; j < orbits.size(); ++j) {
            if (mask >> j & 1) {
                holes += orbits[j].size;
                sites |= orbits[j].sites;
            }
            else ordinary.push_back(orbits[j]);
        }
        if (holes != 4) continue;
        bool canonical = true;
        for (auto [a, b] : centralizer) {
            uint32_t alternative = 0;
            for (int i = 0; i < 32; ++i)
                if (sites >> i & 1) alternative |= uint32_t(1) << ((a*i+b) % 32);
            if (alternative < sites) { canonical = false; break; }
        }
        if (!canonical) continue;
        std::sort(ordinary.begin(), ordinary.end(), [](const Orbit& a, const Orbit& b) {
            if (a.options.size() != b.options.size()) return a.options.size() < b.options.size();
            return a.size > b.size;
        });
        total += count_survivors(ordinary, 0, Basis{}, {}, field, {}, emit, relabel, (uint32_t(1) << relabel.size())-1);
    }
    return total;
}
bool geometric(Affine g) {
    return g.first == 1 || g.first == 31;
}
}  // namespace

int main(int argc, char** argv) {
    bool nonfaithful = argc == 2 && std::string(argv[1]) == "--nonfaithful";
    if (argc != 1 && !nonfaithful) return 2;
    Field field;
    int cyclic_classes = 0, klein_classes = 0;
    for (auto group : subgroup_classes()) {
        auto order_four = std::find_if(group.begin(), group.end(),
            [](Affine x) { return compose(x, x) != identity; });
        if (order_four != group.end()) {
            ++cyclic_classes;
            auto f = *order_four, square = compose(f, f);
            std::vector<Perm> actions{{1, 2, 3, 0}};
            if (nonfaithful) {
                if (geometric(square)) continue;
                actions = {identity_perm, {1, 0, 2, 3}, {1, 0, 3, 2}};
            }
            for (auto r : actions) {
                auto n = census({identity, f, square, compose(f, square)},
                                {identity_perm, r, compose(r, r), compose(r, compose(r, r))}, field, nonfaithful);
                std::cout << "cyclic " << f.first << ' ' << f.second << " survivors " << n << '\n';
                if (n && !nonfaithful) return 1;
            }
        } else {
            ++klein_classes;
            std::vector<Affine> generators;
            for (auto g : group) if (g != identity) generators.push_back(g);
            auto f = generators[0], g = generators[1];
            constexpr Perm single{1, 0, 2, 3}, dbl{2, 3, 0, 1};
            std::vector<std::pair<Perm, Perm>> actions{
                {dbl, {1, 0, 3, 2}}, {dbl, {2, 1, 0, 3}}, {single, {0, 1, 3, 2}}, {single, {1, 0, 3, 2}}};
            if (nonfaithful) {
                actions.clear();
                for (Perm swap : {single, dbl}) {
                    if (!geometric(f)) actions.emplace_back(identity_perm, swap);
                    if (!geometric(g)) actions.emplace_back(swap, identity_perm);
                    if (!geometric(compose(f, g))) actions.emplace_back(swap, swap);
                }
                // Each Klein class contains at least one geometric involution.
                assert(geometric(f) || geometric(g) || geometric(compose(f, g)));
            }
            for (auto [t, r] : actions) {
                auto n = census({identity, f, g, compose(f, g)},
                                {identity_perm, t, r, compose(t, r)}, field, nonfaithful);
                std::cout << "Klein " << f.first << ' ' << f.second << ' '
                          << g.first << ' ' << g.second << " survivors " << n << '\n';
                if (n && !nonfaithful) return 1;
            }
        }
    }
    assert(cyclic_classes == 5 && klein_classes == 6);
}
