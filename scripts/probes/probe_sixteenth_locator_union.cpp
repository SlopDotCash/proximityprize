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
    unsigned flags = 0;
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
    unsigned id, anchor, multiplicity;
};
struct Totals {
    std::array<Word, 2> weight{}, incidences{};
};

struct Census {
    unsigned order, degree, spare, step, per_tree, trees, leaves = 0;
    Word denominator = 1;
    std::array<Mask, 128> atom{};
    std::array<int, 32> leaf_exponent{};
    std::array<int, 128> leaf_index{};
    std::array<std::array<int, 32>, 128> galois{};
    std::vector<Label> labels;
    std::unordered_map<Mask, unsigned, MaskHash> index;
    std::vector<std::unordered_map<unsigned, Local>> locals;

    Census(unsigned m, unsigned d, unsigned s)
        : order(m), degree(d), spare(s), step(m / s), per_tree(m / (2 * s)), trees(s / 2),
          locals(trees) {
        require(m >= 8 && m <= 128 && !(m & (m - 1)) && s >= 4 && s <= 16 && !(s & (s - 1)) &&
                    s < m && per_tree <= 4 && d > 0 && d <= 9,
                "unsupported quotient");
        walk(order / 4);
        for (unsigned u = 1; u < order; u += 2)
            for (unsigned i = 0; i < leaves; i++)
                galois[u][i] = leaf_index[(u * leaf_exponent[i]) % order];
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
                label.flags |= 1;
            if (label.score > cut_b) {
                label.flags |= 2;
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
                    labels[x].flags |= 2;
                used += orbit.size();
            }
        }
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
                v.all.push_back({mask, n, sum % order});
                v.by_degree_sum[n * order + sum % order].push_back(mask);
            }
        }
    }
    // First take orbits of anchors, then of signatures under the anchor stabilizer.
    std::vector<Work> jobs() const {
        std::vector<Work> work;
        for (unsigned a = step; a < order; a *= 2) {
            std::vector<unsigned char> seen(labels.size());
            const unsigned orbit_size = order / (2 * a);
            for (unsigned i = 0; i < labels.size(); i++) {
                if (seen[i] || !labels[i].flags)
                    continue;
                unsigned len = 0;
                for (unsigned u = 1; u < order; u += 2)
                    if (u * a % order == a) {
                        const auto id = index.at(conjugate(labels[i].signature, u));
                        require(labels[id].flags == labels[i].flags,
                                "label selection breaks anchor symmetry");
                        if (!seen[id]) {
                            seen[id] = 1;
                            len++;
                        }
                    }
                work.push_back({i, a, len * orbit_size});
            }
        }
        return work;
    }
    unsigned flags(Mask sig) const {
        auto it = index.find(sig);
        return it == index.end() ? 0 : labels[it->second].flags;
    }
    // A root set appearing at q anchors receives weight 1/q at each incidence.
    void record(Mask sites, const Work &w, Totals &totals) const {
        std::array<Mask, 16> signatures{};
        // Offset d here is measured relative to the current chart's anchor.
        for (Mask m = sites; m; m &= m - 1) {
            const unsigned j = low_bit(m);
            for (unsigned d = 0; d < spare; d++)
                signatures[d] += atom[(j + order - d * step) & (order - 1)];
        }
        require(signatures[0] == labels[w.id].signature, "incorrect local signature");
        std::array<unsigned, 2> hits{};
        for (unsigned d = 0; d < spare; d++)
            if ((w.anchor / step + d) % spare != 0) {
                unsigned bits = flags(signatures[d]);
                hits[0] += bits & 1;
                hits[1] += (bits >> 1) & 1;
            }
        for (unsigned h = 0; h < 2; h++)
            if (labels[w.id].flags & (1U << h)) {
                require(hits[h] && denominator % hits[h] == 0, "invalid chart multiplicity");
                totals.weight[h] += (denominator / hits[h]) * w.multiplicity;
                totals.incidences[h] += w.multiplicity;
            }
    }
    void enumerate(const Work &w, Totals &totals) const {
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
        const unsigned target = (order - w.anchor * degree % order) % order;
        auto recur = [&](auto &self, unsigned t, unsigned remaining, unsigned residue,
                         Mask set) -> void {
            if (t + 1 == trees) {
                const auto &table = choices[t]->by_degree_sum;
                auto it = table.find(remaining * order + residue);
                if (it != table.end())
                    for (Mask last : it->second)
                        record(set | last, w, totals);
            } else
                for (const Option &o : choices[t]->all)
                    if (o.degree + mins[t + 1] <= remaining)
                        self(self, t + 1, remaining - o.degree, (residue + order - o.sum) % order,
                             set | o.sites);
        };
        recur(recur, 0, degree, target, 0);
    }
};

int main(int argc, char **argv) try {
    require(argc == 9, "usage: census POOL ORDER DEGREE SPARE CUTOFF1 CUTOFF2 CAP2 WORKERS");
    auto param = [](const char *arg) {
        std::size_t n = 0;
        const auto value = std::stoul(arg, &n);
        require(arg[0] != '-' && arg[n] == '\0' && value <= std::numeric_limits<unsigned>::max(),
                "invalid unsigned argument");
        return static_cast<unsigned>(value);
    };
    unsigned order = param(argv[2]), degree = param(argv[3]), spare = param(argv[4]);
    require(spare >= 4 && spare <= 16, "spare subgroup must have order 4, 8 or 16");
    Census c(order, degree, spare);
    c.read(argv[1]);
    c.choose(param(argv[5]), param(argv[6]), param(argv[7]));
    c.build_locals();
    auto work = c.jobs();
    unsigned workers = param(argv[8]);
    require(workers >= 1 && workers <= 3, "use 1 to 3 workers");
    std::atomic<unsigned> next{0};
    std::vector<std::future<Totals>> tasks;
    for (unsigned i = 0; i < workers; i++)
        tasks.push_back(std::async(std::launch::async, [&] {
            Totals totals;
            for (unsigned start; (start = next.fetch_add(32)) < work.size();)
                for (unsigned j = start; j < std::min<unsigned>(start + 32, work.size()); j++)
                    c.enumerate(work[j], totals);
            return totals;
        }));
    Totals all;
    for (auto &task : tasks) {
        auto t = task.get();
        for (unsigned h = 0; h < 2; h++) {
            all.weight[h] += t.weight[h];
            all.incidences[h] += t.incidences[h];
        }
    }
    std::cout << "orbits=" << work.size() << " denominator=" << c.denominator << "\n";
    for (unsigned h = 0; h < 2; h++) {
        unsigned bins = 0;
        for (auto &v : c.labels)
            bins += (v.flags >> h) & 1;
        require(all.weight[h] % c.denominator == 0, "nonintegral union");
        std::cout << "bins=" << bins << " incidences=" << all.incidences[h]
                  << " unique=" << all.weight[h] / c.denominator << "\n";
    }
} catch (std::exception &e) {
    std::cerr << e.what() << "\n";
    return 1;
}
