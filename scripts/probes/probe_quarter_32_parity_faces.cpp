// Exact final modular ratio checks for probe_quarter_32_parity_tree.py.
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

namespace {
using Word = uint64_t;
using Log = uint16_t;
constexpr int prime = 65537;
std::array<std::array<std::array<Log, 65536>, 32>, 2> subset_log{};
int sign[6][6]{};

void initialize() {
    std::array<int, prime> log{};
    int x = 1;
    for (int k = 0; k < prime-1; ++k) {
        if (k == (prime-1)/2) assert(x == prime-1);
        log[x] = k;
        x = (3*x) % prime;
    }
    assert(x == 1);
    std::array<int, 32> roots{};
    for (int value = 1; value < prime; ++value)
        if (log[value] % 2048 == 0) roots[log[value]/2048] = value;
    for (int parity = 0; parity < 2; ++parity)
        for (int i = 0; i < 32; ++i) {
            std::array<int, 16> at{};
            for (int j = 0; j < 16; ++j)
                at[j] = log[(roots[i]+prime-roots[2*j+parity]) % prime];
            auto& sums = subset_log[parity][i];
            for (int mask = 1; mask < 65536; ++mask)
                sums[mask] = static_cast<Log>(sums[mask & (mask-1)] + at[__builtin_ctz(mask)]);
        }
    constexpr int base[2][6]{{0, 0, 1, -1, -1, 1}, {0, 0, 1, -1, 1, -1}};
    for (int c = 0; c < 6; ++c)
        for (int j = 0; j < 6; ++j) sign[c][j] = base[c%2][(j+6-2*(c/2)) % 6];
}

struct Layout {
    std::array<Log, 7> sites{};
    std::array<Log, 6> positive{}, negative{};
    explicit Layout(Word packed) {
        for (int j = 0; j < 16; ++j) {
            auto color = (packed >> (4*j)) & 15;
            assert(color < sites.size());
            sites[color] |= 1 << j;
        }
        for (int c = 0; c < 6; ++c)
            for (int j = 0; j < 6; ++j) {
                if (sign[c][j] == 1) positive[c] |= sites[j];
                if (sign[c][j] == -1) negative[c] |= sites[j];
            }
    }
    Log value(int parity, int c, int i) const {
        const auto& sums = subset_log[parity][i];
        return static_cast<Log>(sums[positive[c]]-sums[negative[c]]);
    }
};

struct Block {
    std::vector<Layout> layouts;
    int raw = 0;
};

std::vector<Block> read_blocks(const std::string& name, std::ifstream& meta, bool canonical) {
    int count;
    meta >> count;
    std::vector<Block> out(count);
    std::ifstream input(name, std::ios::binary);
    assert(input);
    for (auto& block : out) {
        meta >> block.raw;
        std::unordered_set<Word> seen;
        for (int t = 0; t < block.raw; ++t) {
            Word packed;
            input.read(reinterpret_cast<char*>(&packed), sizeof(packed));
            assert(input);
            if (canonical && seen.count(packed)) continue;
            block.layouts.emplace_back(packed);
            if (!canonical) continue;
            for (int a = 1; a < 16; a += 2)
                for (int b = 0; b < 16; ++b) {
                    Word image = 0;
                    for (int j = 0; j < 16; ++j)
                        image |= ((packed >> (4*j)) & 15) << (4*((a*j+b) % 16));
                    seen.insert(image);
                }
        }
    }
    return out;
}

bool constant_on_each_edge(const Layout& even, const Layout& odd) {
    for (int c = 0; c < 6; ++c) {
        int first = -1;
        for (int parity = 0; parity < 2; ++parity) {
            int sites = parity ? odd.sites[c] : even.sites[c];
            while (sites) {
                int i = 2*__builtin_ctz(sites)+parity;
                sites &= sites-1;
                int value = static_cast<Log>(even.value(0, c, i)+odd.value(1, c, i));
                if (first < 0) first = value;
                else if (first != value) return false;
            }
        }
    }
    return true;
}

struct Counts {
    Word raw = 0, canonical = 0, first_pair = 0, all = 0;
};

void check_case(const std::string& prefix, Counts& counts) {
    std::ifstream meta(prefix+".txt");
    assert(meta);
    auto left = read_blocks(prefix+"-L.bin", meta, true);
    auto right = read_blocks(prefix+"-R.bin", meta, false);
    int a, b;
    while (meta >> a >> b) {
        counts.raw += Word(left[a].raw)*right[b].raw;
        for (const auto& even : left[a].layouts) {
            int c = 0;
            while (c < 6 && __builtin_popcount(even.sites[c]) < 2) ++c;
            assert(c < 6);
            int sites = even.sites[c];
            int i = 2*__builtin_ctz(sites);
            int j = 2*__builtin_ctz(sites & (sites-1));
            Log target = static_cast<Log>(even.value(0, c, j)-even.value(0, c, i));
            for (const auto& odd : right[b].layouts) {
                ++counts.canonical;
                if (static_cast<Log>(odd.value(1, c, i)-odd.value(1, c, j)) != target) continue;
                ++counts.first_pair;
                if (constant_on_each_edge(even, odd)) ++counts.all;
            }
        }
    }
}
}  // namespace

int main(int argc, char** argv) {
    initialize();
    Counts counts;
    for (int i = 1; i < argc; ++i) check_case(argv[i], counts);
    std::cout << counts.raw << " ordered layouts, " << counts.canonical << " representatives, "
              << counts.first_pair << " pass the first two sites, " << counts.all << " pass all edges.\n";
    assert(counts.raw == 6490722304ULL && counts.canonical == 73967616 && counts.all == 0);
}
