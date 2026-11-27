// Count intersections of signed locator modes at two arbitrary reserved anchors.
// The Python driver supplies one palette per anchor and checks the field construction.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {
using Count = std::uint64_t;
using Signature = std::vector<int>;
using Palette = std::map<Signature, unsigned>;

struct Occupancy {
    Count present;
    Count doubled;
    int size;
};

class NormTree {
    int order_, size_, step_;
    std::map<std::pair<int, Signature>, std::vector<Occupancy>> cache_;

    const std::vector<Occupancy>& visit(int node, const Signature& signature) {
        auto [entry, inserted] = cache_.try_emplace({node, signature});
        auto& out = entry->second;
        if (!inserted) return out;
        const int maximum = node % step_ ? std::min(2, *std::min_element(signature.begin(), signature.end())) : 0;
        const Count bit = Count{1} << (node - 1);
        for (int used = 0; used <= maximum; ++used) {
            const Occupancy current{used ? bit : 0, used == 2 ? bit : 0, used};
            if (signature.size() == 1) {
                if (signature.front() == used) out.push_back(current);
                continue;
            }
            const auto middle = signature.begin() + signature.size() / 2;
            Signature left(signature.begin(), middle), right(middle, signature.end());
            for (auto& x : left) x -= used;
            for (auto& x : right) x -= used;
            const auto& lhs = visit(node / 2, left);
            const auto& rhs = visit((order_ - node) / 2, right);
            for (const auto& a : lhs) {
                for (const auto& b : rhs) {
                    const int weight = used + a.size + b.size;
                    if (weight > size_ || (node == order_ / 4 && weight != size_)) continue;
                    out.push_back({current.present | a.present | b.present,
                                   current.doubled | a.doubled | b.doubled, weight});
                }
            }
        }
        return out;
    }

public:
    NormTree(int order, int size, int step) : order_(order), size_(size), step_(step) {}
    const std::vector<Occupancy>& choices(const Signature& signature) {
        return visit(order_ / 4, signature);
    }
};

struct Exponents {
    int left;
    int right;
};

struct Orbit {
    std::array<std::vector<int>, 2> edges;
    int states{1};
    std::vector<int> sizes;
    std::vector<std::vector<Exponents>> solutions;

    Orbit(const std::set<int>& orbit, int order, int delta) {
        // Edge occupancies 0, 1 and 2 are digits of a ternary index.
        std::array<std::vector<int>, 2> powers;
        for (int side = 0; side < 2; ++side) {
            for (int j : orbit) {
                const int x = (j + order - side * delta) % order;
                const int edge = std::min(x, order - x);
                auto it = std::find(edges[side].begin(), edges[side].end(), edge);
                int power = 1;
                for (auto k = edges[side].begin(); k != it; ++k) power *= 3;
                if (it == edges[side].end()) edges[side].push_back(edge);
                powers[side].push_back(power);
            }
        }
        for (std::size_t i = 0; i < orbit.size() / 2; ++i) states *= 3;
        sizes.resize(states);
        solutions.resize(states * states);
        for (unsigned mask = 0; mask < (1u << orbit.size()); ++mask) {
            int code[2]{};
            Exponents sum{};
            unsigned index = 0;
            for (int j : orbit) {
                if (mask & (1u << index)) {
                    code[0] += powers[0][index];
                    code[1] += powers[1][index];
                    sum.left += j;
                    sum.right += (j + order - delta) % order;
                }
                ++index;
            }
            sizes[code[0]] = sizes[code[1]] = std::popcount(mask);
            auto& cell = solutions[code[0] * states + code[1]];
            cell.push_back({sum.left % (2 * order), sum.right % (2 * order)});
            if (cell.size() > 2) throw std::logic_error("edge sums did not propagate around the cycle");
        }
    }

    int encode(const Occupancy& choice, int side) const {
        int code = 0;
        for (auto it = edges[side].rbegin(); it != edges[side].rend(); ++it) {
            const int bit = *it - 1;
            code = 3 * code + int((choice.present >> bit) & 1) + int((choice.doubled >> bit) & 1);
        }
        return code;
    }
};

struct Record {
    std::array<std::uint8_t, 64> local{};
    unsigned signs{};
};
using Bins = std::unordered_map<Count, std::vector<Record>>;

class Reflections {
    int order_;
    std::vector<Orbit> orbits_;

    static bool accepted(int value, int residue, unsigned signs, int order) {
        const unsigned e = unsigned(value) & unsigned(2 * order - 1);
        return (e == unsigned(residue) && (signs & 1)) ||
               (e == unsigned(residue + order) && (signs & 2));
    }

    Count completions(const Record& a, const Record& b, int left, int right) const {
        Exponents sum{};
        std::array<Exponents, 64> differences{};
        unsigned flexible = 0;
        for (std::size_t i = 0; i < orbits_.size(); ++i) {
            const auto& orbit = orbits_[i];
            const auto& sol = orbit.solutions[a.local[i] * orbit.states + b.local[i]];
            if (sol.empty()) return 0;
            sum.left += sol[0].left;
            sum.right += sol[0].right;
            if (sol.size() == 2) {
                differences[flexible++] = {sol[1].left - sol[0].left, sol[1].right - sol[0].right};
            }
        }
        if (flexible >= 63) throw std::overflow_error("too many independent cycle orientations");
        Count count = 0, previous = 0;
        for (Count i = 0; i < (Count{1} << flexible); ++i) {
            const Count gray = i ^ (i >> 1);
            if (i != 0) {
                const Count change = gray ^ previous;
                const int sign = (change & gray) ? 1 : -1;
                const auto diff = differences[std::countr_zero(change)];
                sum.left += sign * diff.left;
                sum.right += sign * diff.right;
            }
            count += accepted(sum.left, left, a.signs, order_) &&
                     accepted(sum.right, right, b.signs, order_);
            previous = gray;
        }
        return count;
    }

public:
    Reflections(int order, int step, int delta) : order_(order) {
        std::set<int> unseen;
        for (int j = 0; j < order; ++j) if (j % step) unseen.insert(j);
        while (!unseen.empty()) {
            std::vector<int> queue{*unseen.begin()};
            std::set<int> orbit{queue.front()};
            for (std::size_t i = 0; i < queue.size(); ++i) {
                const int j = queue[i];
                for (int x : {(order - j) % order, (2 * delta + order - j) % order}) {
                    if (orbit.insert(x).second) queue.push_back(x);
                }
            }
            for (int j : orbit) unseen.erase(j);
            if (orbit.size() > 8) throw std::invalid_argument("reflection orbit exceeds eight");
            orbits_.emplace_back(orbit, order, delta);
        }
    }

    Bins group(const Palette& palette, NormTree& tree, int side) const {
        Bins bins;
        for (const auto& [signature, signs] : palette) {
            const int total = std::accumulate(signature.begin(), signature.end(), 0);
            for (const auto& occ : tree.choices(signature)) {
                Record record;
                record.signs = signs;
                Count key = total;
                for (std::size_t i = 0; i < orbits_.size(); ++i) {
                    const auto& orbit = orbits_[i];
                    record.local[i] = std::uint8_t(orbit.encode(occ, side));
                    key = key * 1315423911u + orbit.sizes[record.local[i]] + 1;
                }
                // Hash collisions only send extra pairs to the full local compatibility test.
                bins[key].push_back(record);
            }
        }
        return bins;
    }

    Count count(const Bins& first, const Bins& second, int left, int right) const {
        Count result = 0;
        for (const auto& [key, aa] : first) {
            const auto it = second.find(key);
            if (it == second.end()) continue;
            for (const auto& a : aa) for (const auto& b : it->second) {
                const auto added = completions(a, b, left, right);
                if (added > std::numeric_limits<Count>::max() - result) throw std::overflow_error("pair count");
                result += added;
            }
        }
        return result;
    }
};
} // namespace

int main() {
    int order, reserved, size, product;
    if (!(std::cin >> order >> reserved >> size >> product) ||
        order < 8 || order > 128 || !std::has_single_bit(unsigned(order)) ||
        reserved < 2 || reserved > 8 || !std::has_single_bit(unsigned(reserved)) ||
        reserved >= order || size < 1 || size > order - reserved || product < 0 || product >= order) {
        throw std::invalid_argument("invalid quotient board");
    }
    const int step = order / reserved;
    const auto residue = [&](int anchor) {
        return (product + order - (size * step * anchor) % order) % order;
    };
    std::vector<Palette> palettes(reserved);
    int anchor, exponent;
    while (std::cin >> anchor >> exponent) {
        if (anchor < 0 || anchor >= reserved || exponent < 0 || exponent >= 2 * order ||
            exponent % order != residue(anchor)) throw std::invalid_argument("wrong signed exponent");
        Signature signature(order / 4);
        for (auto& x : signature) if (!(std::cin >> x) || x < 0) throw std::invalid_argument("incomplete signature");
        const unsigned bit = 1u << (exponent / order);
        auto& signs = palettes[anchor][signature];
        if (signs & bit) throw std::invalid_argument("duplicate signed mode");
        signs |= bit;
    }
    NormTree tree(order, size, step);
    for (int gap = 1; gap < reserved; ++gap) {
        Reflections pair(order, step, gap * step);
        for (int a = 0, b = gap; b < reserved; ++a, ++b) {
            const auto first = pair.group(palettes[a], tree, 0);
            const auto second = pair.group(palettes[b], tree, 1);
            std::cout << a << ' ' << b << ' ' << pair.count(first, second, residue(a), residue(b)) << '\n';
        }
    }
}
