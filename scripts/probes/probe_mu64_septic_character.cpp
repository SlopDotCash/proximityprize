// Enumerate every seven-site root support outside one three-point anchor.
// Input rows contain the site and its two normalized 2-adic character values.
#include <algorithm>
#include <array>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <unordered_map>
#include <vector>

using Word = std::uint64_t;
constexpr unsigned available = 61;
constexpr std::size_t support_count = 436270780; // binomial(61,7)
constexpr Word mask30 = (Word{1} << 30) - 1;
constexpr Word keep = mask30 | (mask30 << 32);
struct Site {
    Word character;
    Word bit;
};
using Sites = std::array<Site, available>;

// The two 30-bit lanes never carry into each other during an addition.
template<unsigned left, class Visit>
void enumerate(const Sites& sites, unsigned first, Word character, Word support, Visit& visit) {
    for (unsigned i = first; i <= available - left; ++i) {
        const Word next = (character + sites[i].character) & keep;
        const Word mask = support | sites[i].bit;
        if constexpr (left == 1) {
            visit(next, mask);
        } else {
            enumerate<left-1>(sites, i+1, next, mask, visit);
        }
    }
}

int main() {
    Sites sites;
    Word used = 0;
    for (auto& entry : sites) {
        unsigned site, x, y;
        if (std::scanf("%u %u %u", &site, &x, &y) != 3 ||
            site >= 64 || x > mask30 || y > mask30 || (used & (Word{1} << site))) {
            std::fprintf(stderr, "Expected 61 distinct sites with two 30-bit characters each.\n");
            return 2;
        }
        entry = {Word{x} | (Word{y} << 32), Word{1} << site};
        used |= entry.bit;
    }

    std::vector<Word> keys;
    keys.reserve(support_count);
    auto save_key = [&](Word key, Word) { keys.push_back(key); };
    enumerate<7>(sites, 0, 0, 0, save_key);
    if (keys.size() != support_count) return 3;
    std::sort(keys.begin(), keys.end());

    std::unordered_map<Word, std::vector<Word>> repeated;
    for (std::size_t i = 1; i < keys.size(); ++i) {
        if (keys[i] == keys[i-1]) repeated.try_emplace(keys[i]);
    }
    std::vector<Word>().swap(keys);
    auto recover = [&](Word key, Word mask) {
        auto it = repeated.find(key);
        if (it != repeated.end()) it->second.push_back(mask);
    };
    enumerate<7>(sites, 0, 0, 0, recover);
    for (const auto& group : repeated) {
        const auto& masks = group.second;
        for (std::size_t i = 0; i < masks.size(); ++i) {
            for (std::size_t j = 0; j < i; ++j) {
                if (!(masks[i] & masks[j])) {
                    std::printf("%016" PRIx64 " %016" PRIx64 "\n", masks[i], masks[j]);
                }
            }
        }
    }
}
