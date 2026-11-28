// Count all prefix palettes of odd-product modes under an anchor-transitive affine group.
#define SIXTEENTH_LOCATOR_CENSUS_LIBRARY
#include "probe_sixteenth_locator_union.cpp"

namespace {
struct Entry {
    Mask signature{};
    std::array<unsigned, 2> rank{};
};

class RankedModes {
    std::vector<Entry> entries;
    std::size_t mask;

public:
    explicit RankedModes(unsigned count) {
        std::size_t capacity = 1;
        while (capacity < 2 * std::size_t(count)) capacity *= 2;
        entries.resize(capacity);
        mask = capacity - 1;
    }

    std::size_t position(Mask signature) const {
        std::size_t i = MaskHash{}(signature) & mask;
        while (entries[i].signature && entries[i].signature != signature) i = (i + 1) & mask;
        return i;
    }

    void insert(Mask signature, unsigned bit, unsigned rank) {
        require(signature && rank, "positive signature and one-based rank");
        auto &cell = entries[position(signature)];
        cell.signature = signature;
        require(!cell.rank[bit], "duplicate pool mode");
        cell.rank[bit] = rank;
    }

    unsigned lookup(Mask signature, unsigned bit) const {
        return entries[position(signature)].rank[bit];
    }
};

unsigned reciprocal(unsigned x, unsigned m) {
    for (unsigned i = 1; i < m; i += 2) if ((x*i) % m == 1) return i;
    throw std::logic_error("expected a unit");
}

struct Chart {
    std::array<Mask, 128> contribution{};
    std::array<unsigned, 128> coordinate{};
};

std::vector<Chart> normalized_charts(const Census &board) {
    std::vector<Chart> result(board.spare);
    for (unsigned u = 1; u < board.order; u += board.step) {
        const unsigned anchor = ((1-u)*reciprocal(board.degree, board.order)) & (board.order-1);
        require(anchor % board.step == 0, "reserved anchor");
        const unsigned inverse = reciprocal(u, board.order);
        Chart &chart = result[anchor / board.step];
        for (unsigned j = 0; j < board.order; j++) {
            const unsigned x = (inverse*(j-anchor)) & (board.order-1);
            chart.coordinate[j] = x;
            chart.contribution[j] = board.atom[x];
        }
    }
    return result;
}

void run_census(const std::string &pool, unsigned order, unsigned degree, unsigned spare,
                unsigned workers, std::vector<unsigned> cutoffs) {
    Census board(order, degree, spare, true);
    require(degree % 2 && workers > 0 && !cutoffs.empty(), "odd degree and nonempty census");
    board.read(pool, false);
    board.build_locals();
    const unsigned modes = 2*board.labels.size();
    std::vector<unsigned> frequencies(modes), ranked(modes);
    std::iota(ranked.begin(), ranked.end(), 0);
    parallel_jobs(workers, modes, [&](unsigned id) {
        board.enumerate_at_sum(id/2, 1+(id%2)*order, [&](Mask, const std::vector<Mask> &tails) {
            frequencies[id] += tails.size();
        });
    });
    const auto higher = [&](unsigned i, unsigned j) {
        if (frequencies[i] != frequencies[j]) return frequencies[i] > frequencies[j];
        Mask v = board.labels[i/2].signature, w = board.labels[j/2].signature;
        return v != w ? v < w : i%2 < j%2;
    };
    const unsigned cap = *std::max_element(cutoffs.begin(), cutoffs.end());
    require(cap > 0 && cap <= modes, "requested palette exceeds the dictionary");
    std::partial_sort(ranked.begin(), ranked.begin()+cap, ranked.end(), higher);
    RankedModes palette(cap);
    for (unsigned r = 0; r < cap; r++) {
        unsigned id = ranked[r];
        palette.insert(board.labels[id/2].signature, id%2, r+1);
    }
    auto charts = normalized_charts(board);
    Word denominator = 1;
    for (unsigned i = 1; i <= spare; i++) denominator = std::lcm(denominator, Word(i));
    std::vector<Word> weights(cap);
    parallel_jobs(workers, cap, [&](unsigned r) {
        const unsigned id = ranked[r];
        board.enumerate_at_sum(id/2, 1+(id%2)*order,
            [&](Mask prefix, const std::vector<Mask> &tails) {
                for (Mask tail : tails) {
                    const Mask sites = prefix | tail;
                    unsigned ties = 1;
                    bool first = true;
                    for (unsigned i = 1; i < spare; i++) {
                        Mask sig = 0;
                        unsigned sum = 0;
                        for (Mask bits = sites; bits; bits &= bits-1) {
                            const int j = low_bit(bits);
                            sig += charts[i].contribution[j];
                            sum += charts[i].coordinate[j];
                        }
                        require(sum % order == 1, "normalized product");
                        const unsigned other = palette.lookup(sig, (sum/order)%2);
                        if (other && other < r+1) { first = false; break; }
                        ties += other == r+1;
                    }
                    if (first) weights[r] += denominator/ties;
                }
            });
    });
    // Every represented root set has exactly one least rank, including tied anchor visits.
    // Choosing any ranks retains every set owned by one of those ranks.
    auto largest = weights;
    std::sort(largest.begin(), largest.end(), std::greater<Word>());
    std::sort(cutoffs.begin(), cutoffs.end());
    unsigned previous = 0;
    Word incidences = 0, weighted = 0, disjoint = 0;
    for (unsigned cutoff : cutoffs) {
        for (; previous < cutoff; previous++) {
            incidences += frequencies[ranked[previous]];
            weighted += weights[previous];
            disjoint += largest[previous];
        }
        const Word scale = denominator/spare;
        require(weighted % scale == 0 && disjoint % scale == 0, "nonintegral affine orbit census");
        std::cout << cutoff << ' ' << spare*incidences << ' ' << weighted/scale << ' ' << disjoint/scale << '\n';
    }
}
} // namespace

int main(int argc, char **argv) try {
    require(argc >= 7, "usage: census POOL ORDER DEGREE SPARE WORKERS PALETTE_SIZE...");
    auto number = [](const char *s) { return static_cast<unsigned>(std::stoul(s)); };
    std::vector<unsigned> cutoffs;
    for (int i = 6; i < argc; i++) cutoffs.push_back(number(argv[i]));
    run_census(argv[1], number(argv[2]), number(argv[3]), number(argv[4]), number(argv[5]), cutoffs);
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
