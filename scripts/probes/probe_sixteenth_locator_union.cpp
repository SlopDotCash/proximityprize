// Count the union of locator signatures at several dyadic quotient fibers.
#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <fstream>
#include <future>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using Mask = __uint128_t;
using Word = std::uint64_t;
void require(bool ok, const char *reason) {
    if (!ok)
        throw std::runtime_error(reason);
}
struct MaskHash {
    std::size_t operator()(Mask x) const noexcept {
        Word h = Word(x) ^ Word(x >> 64) * 0x9e3779b97f4a7c15ULL;
        h ^= h >> 30;
        h *= 0xbf58476d1ce4e5b9ULL;
        h ^= h >> 27;
        h *= 0x94d049bb133111ebULL;
        return h ^ (h >> 31);
    }
};
int low_bit(Mask x) {
    return Word(x) ? __builtin_ctzll(Word(x)) : 64 + __builtin_ctzll(Word(x >> 64));
}

struct Label {
    Mask signature;
    unsigned score;
    std::array<unsigned char, 32> selected{};
};
struct Option {
    Mask sites;
    unsigned degree, sum;
};
struct Local {
    std::vector<Option> all;
    std::unordered_map<unsigned, std::vector<Mask>> by_degree_sum;
    unsigned minimum = 100;
};
struct Work {
    unsigned id, anchor, multiplicity, mode;
};
struct Population {
    Word total = 0;
    std::array<Word, 2> exclusive{};
};
struct Totals {
    std::array<Word, 2> weight{}, incidences{};
};

struct Census {
    unsigned order, degree, spare, step, per_tree, trees, lifts, leaves = 0;
    Word denominator = 1;
    std::array<Mask, 128> atom{}, correction{};
    std::array<Mask, 16> prefix{};
    std::array<int, 32> leaf_exponent{};
    std::array<int, 128> leaf_index{};
    std::array<std::array<int, 32>, 128> galois{};
    std::vector<Label> labels;
    std::unordered_map<Mask, unsigned, MaskHash> index;
    std::vector<std::unordered_map<unsigned, Local>> locals;

    Census(unsigned m, unsigned d, unsigned s, bool signed_modes)
        : order(m), degree(d), spare(s), step(m / s), per_tree(m / (2 * s)), trees(s / 2),
          lifts(signed_modes ? 2 : 1), locals(trees) {
        require(m >= 8 && m <= 128 && !(m & (m - 1)) && s >= 4 && s <= 16 && !(s & (s - 1)) &&
                    s < m && per_tree <= 4 && d > 0 && d <= 9,
                "unsupported quotient");
        walk(order / 4);
        for (unsigned u = 1; u < order; u += 2)
            for (unsigned i = 0; i < leaves; i++)
                galois[u][i] = leaf_index[(u * leaf_exponent[i]) % order];
        for (unsigned u = 1; u < order; u += 2)
            for (unsigned i = 0; i < leaves; i++)
                if ((u * leaf_exponent[i] / order + (u - 1) / 2) & 1)
                    correction[u] |= Mask(1) << (4 * i);
        for (unsigned d = 0; d < spare; d++)
            prefix[d] = (Mask(1) << (d * step)) - 1;
        for (unsigned k = 1; k < spare; k++)
            denominator = std::lcm(denominator, Word(k));
    }
    Mask walk(unsigned j) {
        Mask value;
        if (j % 2) {
            leaf_exponent[leaves] = j;
            leaf_index[j] = leaf_index[order - j] = leaves;
            value = Mask(1) << (4 * leaves++);
        } else {
            Mask left = walk(j / 2), right = walk((order - j) / 2);
            value = left + right;
        }
        return atom[j] = atom[order - j] = value;
    }
    Mask conjugate(Mask signature, unsigned u) const {
        Mask out = 0;
        for (unsigned i = 0; i < leaves; i++)
            out |= ((signature >> (4 * i)) & 15) << (4 * galois[u][i]);
        return out;
    }
    static unsigned parity(Mask x) { return __builtin_parityll(Word(x) ^ Word(x >> 64)); }
    unsigned slot(unsigned anchor, unsigned mode) const { return lifts * (anchor / step) + mode; }
    // Transport the high bit of the canonical exponent sum modulo 2*order.
    unsigned image_mode(Mask sig, unsigned a, unsigned mode, unsigned u) const {
        if (lifts == 1)
            return 0;
        unsigned e = (order - a * degree % order) % order + mode * order;
        unsigned adjust = parity(sig & correction[u]) ^ (((u - 1) / 2 * degree) & 1);
        return ((u * e + order * adjust) / order) & 1;
    }
    void read(const std::string &path) {
        std::ifstream f(path, std::ios::binary);
        require(bool(f), "cannot open signature pool");
        std::array<unsigned char, 20> record;
        while (f.read(reinterpret_cast<char *>(record.data()), record.size())) {
            Mask v = 0;
            for (unsigned j = 0; j < 16; j++)
                v |= Mask(record[j]) << (8 * j);
            unsigned score = 0;
            for (unsigned j = 16; j < 20; j++)
                score |= unsigned(record[j]) << (8 * (j - 16));
            labels.push_back({v, score});
        }
        require(f.eof() && !f.gcount(), "truncated signature pool");
        index.reserve(labels.size() * 2);
        for (unsigned id = 0; id < labels.size(); id++)
            require(index.emplace(labels[id].signature, id).second, "duplicate signature");
    }
    // At the second cutoff include whole tied Galois orbits in numeric order.
    void choose(unsigned cut_a, unsigned cut_b, unsigned cap) {
        unsigned used = 0;
        std::vector<Mask> tied;
        for (auto &label : labels) {
            if (label.score > cut_a)
                label.selected[0] |= 1;
            if (label.score > cut_b) {
                label.selected[0] |= 2;
                used++;
            }
            if (label.score == cut_b)
                tied.push_back(label.signature);
        }
        require(used <= cap, "strict second pool already exceeds cap");
        std::sort(tied.begin(), tied.end());
        std::vector<unsigned char> seen(labels.size());
        for (Mask sig : tied) {
            const unsigned id = index.at(sig);
            if (seen[id])
                continue;
            std::vector<unsigned> orbit;
            for (unsigned u = 1; u < order; u += 2) {
                unsigned x = index.at(conjugate(sig, u));
                require(labels[x].score == cut_b, "score changed under odd multiplier");
                if (!seen[x]) {
                    seen[x] = 1;
                    orbit.push_back(x);
                }
            }
            if (used + orbit.size() <= cap) {
                for (auto x : orbit)
                    labels[x].selected[0] |= 2;
                used += orbit.size();
            }
        }
        for (auto &label : labels)
            label.selected.fill(label.selected[0]);
    }
    // List root subsets in each binary tree, indexed by their four-bit leaf sums.
    void build_locals() {
        std::vector<std::vector<unsigned>> sites(trees);
        for (unsigned j = 1; j < order; j++)
            if (j % step)
                sites[low_bit(atom[j]) / (4 * per_tree)].push_back(j);
        for (unsigned t = 0; t < trees; t++) {
            require(sites[t].size() == 2 * (2 * per_tree - 1), "incorrect subtree");
            for (unsigned set = 0; set < (1U << sites[t].size()); set++) {
                unsigned n = __builtin_popcount(set);
                if (n > degree)
                    continue;
                Mask sig = 0, mask = 0;
                unsigned sum = 0;
                for (unsigned j = 0; j < sites[t].size(); j++)
                    if (set & (1U << j)) {
                        unsigned x = sites[t][j];
                        sig += atom[x];
                        mask |= Mask(1) << x;
                        sum += x;
                    }
                auto &v = locals[t][unsigned(sig >> (4 * per_tree * t))];
                v.minimum = std::min(v.minimum, n);
                v.all.push_back({mask, n, sum % (lifts * order)});
                v.by_degree_sum[n * lifts * order + sum % (lifts * order)].push_back(mask);
            }
        }
    }
    // First take orbits of anchors, then of signatures under the anchor stabilizer.
    std::vector<Work> jobs(bool include_unselected) const {
        std::vector<Work> work;
        for (unsigned a = step; a < order; a *= 2) {
            std::vector<unsigned char> seen(labels.size() * 2);
            for (unsigned i = 0; i < labels.size(); i++)
                for (unsigned mode = 0; mode < lifts; mode++) {
                    if (seen[2 * i + mode] ||
                        (!include_unselected && !labels[i].selected[slot(a, mode)]))
                        continue;
                    unsigned len = 0, rep = i, rep_mode = mode;
                    for (unsigned u = 1; u < order; u += 2)
                        if (u * a % order == a) {
                            auto sig = conjugate(labels[i].signature, u);
                            auto id = index.at(sig),
                                 sg = image_mode(labels[i].signature, a, mode, u);
                            require(labels[id].selected[slot(a, sg)] ==
                                        labels[i].selected[slot(a, mode)],
                                    "selection must be constant on each stabilizer orbit");
                            if (!seen[2 * id + sg]) {
                                seen[2 * id + sg] = 1;
                                len++;
                                if (sig < labels[rep].signature ||
                                    (sig == labels[rep].signature && sg < rep_mode)) {
                                    rep = id;
                                    rep_mode = sg;
                                }
                            }
                        }
                    work.push_back({rep, a, len * (order / (2 * a)), rep_mode});
                }
        }
        return work;
    }
    // Every chosen orbit occupies the same number of distinct bins at each related anchor.
    void choose_by_product(const std::vector<Work> &work,
                           const std::vector<std::array<Word, 2>> &scores,
                           const std::array<unsigned, 2> &caps, unsigned last_anchor) {
        for (auto &label : labels)
            if (last_anchor) {
                for (unsigned a = last_anchor; a < order; a += 2 * last_anchor)
                    for (unsigned k = 0; k < lifts; k++)
                        label.selected[slot(a, k)] = 0;
            } else
                label.selected.fill(0);
        for (unsigned a = (last_anchor ? last_anchor : step);
             a < (last_anchor ? 2 * last_anchor : order); a *= 2) {
            unsigned orbit = order / (2 * a);
            for (unsigned h = 0; h < 2; h++) {
                std::vector<unsigned> ranked;
                for (unsigned i = 0; i < work.size(); i++)
                    if (work[i].anchor == a && scores[i][h])
                        ranked.push_back(i);
                std::sort(ranked.begin(), ranked.end(), [&](unsigned i, unsigned j) {
                    if (scores[i][h] != scores[j][h])
                        return scores[i][h] > scores[j][h];
                    if (labels[work[i].id].signature != labels[work[j].id].signature)
                        return labels[work[i].id].signature < labels[work[j].id].signature;
                    return work[i].mode < work[j].mode;
                });
                unsigned used = 0;
                for (unsigned i : ranked) {
                    const Work &w = work[i];
                    unsigned size = w.multiplicity / orbit;
                    if (size > caps[h] - used)
                        continue;
                    used += size;
                    Mask sig = labels[w.id].signature;
                    for (unsigned u = 1; u < order; u += 2) {
                        auto id = index.at(conjugate(sig, u));
                        labels[id].selected[slot(u * a % order, image_mode(sig, a, w.mode, u))] |=
                            1U << h;
                    }
                }
            }
        }
    }
    std::array<unsigned, 2> hits(Mask sites, const Work &w) const {
        std::array<Mask, 16> signatures{};
        // Offset d here is measured relative to the current chart's anchor.
        for (Mask m = sites; m; m &= m - 1) {
            const unsigned j = low_bit(m);
            for (unsigned d = 0; d < spare; d++)
                signatures[d] += atom[(j + order - d * step) & (order - 1)];
        }
        require(signatures[0] == labels[w.id].signature, "incorrect local signature");
        std::array<unsigned, 2> hits{};
        unsigned e = (order - w.anchor * degree % order) % order + w.mode * order;
        for (unsigned d = 0; d < spare; d++)
            if ((w.anchor / step + d) % spare != 0) {
                auto it = index.find(signatures[d]);
                if (it == index.end())
                    continue;
                // Subtracting d*step adds order at exactly the sites below d*step.
                unsigned shifted = e + 2 * order * degree - d * step * degree;
                unsigned mode =
                    lifts == 1 ? 0 : ((shifted / order) + parity(sites & prefix[d])) % 2;
                unsigned bits =
                    labels[it->second].selected[slot(((w.anchor / step + d) % spare) * step, mode)];
                hits[0] += bits & 1;
                hits[1] += (bits >> 1) & 1;
            }
        return hits;
    }
    // The product-score pass counts the terminal lists without expanding their site masks.
    template <class Visit> void enumerate(const Work &w, Visit visit) const {
        const Mask v = labels[w.id].signature;
        std::array<const Local *, 8> choices{};
        unsigned mask = (1U << (4 * per_tree)) - 1;
        for (unsigned t = 0; t < trees; t++)
            choices[t] = &locals[t].at(unsigned(v >> (4 * per_tree * t)) & mask);
        std::sort(choices.begin(), choices.begin() + trees,
                  [](auto l, auto r) { return l->all.size() < r->all.size(); });
        std::array<unsigned, 9> mins{};
        for (unsigned t = trees; t-- > 0;)
            mins[t] = mins[t + 1] + choices[t]->minimum;
        const unsigned target = (order - w.anchor * degree % order) % order + w.mode * order;
        auto recur = [&](auto &self, unsigned t, unsigned remaining, unsigned residue,
                         Mask set) -> void {
            if (t + 1 == trees) {
                const auto &table = choices[t]->by_degree_sum;
                auto it = table.find(remaining * lifts * order + residue);
                if (it != table.end())
                    visit(set, it->second);
            } else
                for (const Option &o : choices[t]->all)
                    if (o.degree + mins[t + 1] <= remaining)
                        self(self, t + 1, remaining - o.degree,
                             (residue + lifts * order - o.sum) % (lifts * order), set | o.sites);
        };
        recur(recur, 0, degree, target, 0);
    }
    Population population(const Work &w, bool count_exclusive) const {
        Population result;
        unsigned own = labels[w.id].selected[slot(w.anchor, w.mode)];
        enumerate(w, [&](Mask prefix, const std::vector<Mask> &tails) {
            result.total += tails.size();
            if (!count_exclusive)
                return;
            for (Mask tail : tails) {
                auto at = hits(prefix | tail, w);
                for (unsigned h = 0; h < 2; h++)
                    if (at[h] == ((own >> h) & 1))
                        result.exclusive[h]++;
            }
        });
        return result;
    }
};

// Each job owns one output slot, so worker scheduling cannot affect either selection or the census.
template <class Visit> void parallel_jobs(unsigned workers, unsigned size, Visit visit) {
    std::atomic<unsigned> next{0};
    std::vector<std::future<void>> tasks;
    for (unsigned i = 0; i < workers; i++)
        tasks.push_back(std::async(std::launch::async, [&] {
            for (unsigned start; (start = next.fetch_add(32)) < size;)
                for (unsigned j = start; j < std::min(start + 32, size); j++)
                    visit(j);
        }));
    for (auto &task : tasks)
        task.get();
}
// Remove all reference words seen twice, then maximize the remaining incidence mass per anchor.
void gain_five_bound(const Census &c, const std::vector<Work> &work, unsigned workers,
                     unsigned sites) {
    struct Bin {
        Word remaining = 0, repeated_weight = 0;
    };
    std::vector<Bin> bins(work.size());
    parallel_jobs(workers, work.size(), [&](unsigned j) {
        const auto &w = work[j];
        bool active = c.labels[w.id].selected[c.slot(w.anchor, w.mode)] & 1;
        c.enumerate(w, [&](Mask prefix, const std::vector<Mask> &tails) {
            for (Mask tail : tails) {
                unsigned hits = c.hits(prefix | tail, w)[0];
                if (hits <= 1)
                    bins[j].remaining++;
                else if (active)
                    bins[j].repeated_weight += c.denominator / hits;
            }
        });
    });
    Word single = 0, repeated_weight = 0, incidences = 0;
    for (unsigned a = c.step; a < c.order; a *= 2) {
        unsigned anchor_orbit = c.order / (2 * a);
        std::vector<std::pair<Word, unsigned>> modes;
        for (unsigned j = 0; j < work.size(); j++)
            if (work[j].anchor == a) {
                const auto &w = work[j];
                modes.emplace_back(bins[j].remaining, w.multiplicity / anchor_orbit);
                repeated_weight += bins[j].repeated_weight * w.multiplicity;
                if (c.labels[w.id].selected[c.slot(a, w.mode)] & 1)
                    single += bins[j].remaining * w.multiplicity;
            }
        std::sort(modes.rbegin(), modes.rend());
        unsigned room = sites;
        Word full = 0, next = 0;
        for (auto [population, count] : modes) {
            const unsigned allocated = std::min(room, 5 * count);
            full += population * (allocated / 5);
            if (allocated % 5)
                next = population;
            room -= allocated;
            if (!room)
                break;
        }
        // Any unused sites after the final mode have zero incidence.
        incidences += anchor_orbit * (5 * full + (sites % 5) * next);
        std::cout << "anchor=" << a << " full=" << full << " next=" << next << "\n";
    }
    require(repeated_weight % c.denominator == 0, "integral number of multiply covered candidates");
    Word repeated = repeated_weight / c.denominator;
    std::cout << "single=" << single << " repeated=" << repeated
              << " upper=" << repeated + incidences / 5 << "\n";
}
int main(int argc, char **argv) try {
    bool cover_bound = argc == 8 && std::string(argv[1]) == "--gain-five-cap";
    bool signed_modes = cover_bound || (argc == 10 && std::string(argv[1]) == "--signed-scores");
    bool product_scores =
        signed_modes || (argc == 10 && std::string(argv[1]) == "--product-scores");
    if (product_scores) {
        argc--;
        argv++;
    }
    require(argc == (cover_bound ? 7 : 9),
            "usage: census POOL ORDER DEGREE SPARE CUTOFF1 CUTOFF2 CAP2 WORKERS "
            "or census {--product-scores|--signed-scores} POOL ORDER DEGREE SPARE CAP1 "
            "CAP2 ROUNDS WORKERS or census --gain-five-cap POOL ORDER DEGREE SPARE SITES WORKERS");
    auto param = [](const char *arg) {
        std::size_t n = 0;
        const auto value = std::stoul(arg, &n);
        require(arg[0] != '-' && arg[n] == '\0' && value <= std::numeric_limits<unsigned>::max(),
                "invalid unsigned argument");
        return static_cast<unsigned>(value);
    };
    unsigned order = param(argv[2]), degree = param(argv[3]), spare = param(argv[4]);
    require(spare >= 4 && spare <= 16, "spare subgroup must have order 4, 8 or 16");
    Census c(order, degree, spare, signed_modes);
    c.read(argv[1]);
    const unsigned workers = param(argv[argc - 1]);
    require(workers >= 1 && workers <= 3, "use 1 to 3 workers");
    if (!product_scores)
        c.choose(param(argv[5]), param(argv[6]), param(argv[7]));
    c.build_locals();
    auto work = c.jobs(product_scores);
    if (product_scores) {
        const std::array<unsigned, 2> caps =
            cover_bound ? std::array<unsigned, 2>{param(argv[5]) / 5, 0}
                        : std::array<unsigned, 2>{param(argv[5]), param(argv[6])};
        const unsigned rounds = cover_bound ? 0 : param(argv[7]);
        require(rounds <= (signed_modes ? 3u : 1u), "unsupported refinement count");
        std::vector<std::array<Word, 2>> scores(work.size());
        for (unsigned round = 0; round <= rounds; round++) {
            parallel_jobs(workers, work.size(), [&](unsigned j) {
                const Work &w = work[j];
                if (round >= 2 && w.anchor != order / (1U << (round - 1)))
                    return;
                auto local = c.population(w, round > 0);
                for (unsigned h = 0; h < 2; h++)
                    scores[j][h] = round >= 2
                                       ? local.exclusive[h]
                                       : local.total + (signed_modes ? 2 : 3) * local.exclusive[h];
            });
            c.choose_by_product(work, scores, caps, round >= 2 ? order / (1U << (round - 1)) : 0);
        }
    }
    if (cover_bound) {
        gain_five_bound(c, work, workers, param(argv[5]));
        return 0;
    }
    if (signed_modes) {
        // The final replacement changes just one actual anchor. Its signed modes are disjoint.
        const unsigned a = c.order / 4;
        std::vector<std::array<Word, 2>> margins(work.size());
        parallel_jobs(workers, work.size(), [&](unsigned j) {
            if (work[j].anchor == a)
                margins[j] = c.population(work[j], true).exclusive;
        });
        for (unsigned h = 0; h < 2; h++) {
            std::vector<std::pair<Word, unsigned>> classes;
            Word previous = 0, offered = 0;
            unsigned room = param(argv[5 + h]);
            if (!room)
                continue;
            for (unsigned j = 0; j < work.size(); j++)
                if (work[j].anchor == a) {
                    auto &w = work[j];
                    unsigned size = w.multiplicity / (c.order / (2 * a));
                    bool active = (c.labels[w.id].selected[c.slot(a, w.mode)] >> h) & 1;
                    if (active)
                        previous += margins[j][h] * size;
                    classes.emplace_back(margins[j][h], size);
                }
            std::sort(classes.rbegin(), classes.rend());
            for (auto [m, size] : classes) {
                size = std::min(room, size);
                offered += m * size;
                room -= size;
                if (!room)
                    break;
            }
            require(offered >= previous,
                    "single-anchor replacement cannot reduce its exclusive population");
            std::cout << "response_anchor=" << a << " pool=" << h << " previous=" << previous
                      << " offered=" << offered << " increase=" << offered - previous << "\n";
        }
    }
    std::vector<Totals> totals(work.size());
    parallel_jobs(workers, work.size(), [&](unsigned j) {
        const Work &w = work[j];
        unsigned own = c.labels[w.id].selected[c.slot(w.anchor, w.mode)];
        if (!own)
            return;
        c.enumerate(w, [&](Mask prefix, const std::vector<Mask> &tails) {
            for (Mask tail : tails) {
                auto hits = c.hits(prefix | tail, w);
                for (unsigned h = 0; h < 2; h++)
                    if (own & (1U << h)) {
                        require(hits[h] && c.denominator % hits[h] == 0,
                                "invalid chart multiplicity");
                        totals[j].weight[h] += (c.denominator / hits[h]) * w.multiplicity;
                        totals[j].incidences[h] += w.multiplicity;
                    }
            }
        });
    });
    Totals all;
    for (const auto &t : totals)
        for (unsigned h = 0; h < 2; h++) {
            all.weight[h] += t.weight[h];
            all.incidences[h] += t.incidences[h];
        }
    std::cout << "orbits=" << work.size() << " denominator=" << c.denominator << "\n";
    for (unsigned h = 0; h < 2; h++) {
        if (signed_modes && !param(argv[5 + h]))
            continue;
        unsigned bins = 0;
        for (unsigned a = 1; a < c.spare; a++) {
            unsigned used = 0;
            for (const auto &v : c.labels)
                for (unsigned mode = 0; mode < c.lifts; mode++)
                    used += (v.selected[c.slot(a * c.step, mode)] >> h) & 1;
            bins = std::max(bins, used);
        }
        require(all.weight[h] % c.denominator == 0, "nonintegral union");
        std::cout << "bins=" << bins << " incidences=" << all.incidences[h]
                  << " unique=" << all.weight[h] / c.denominator << "\n";
    }
} catch (std::exception &e) {
    std::cerr << e.what() << "\n";
    return 1;
}
