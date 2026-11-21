// Exact half-size Paley rectangle sums at Fourier phases, using the certified sign file.
// Usage: half_rectangles FIELD SIGN_FILE FREQUENCY [ORDER].
#include "sponsor_phi_field.hpp"

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <numeric>
#include <vector>

using Integer = std::int64_t;

struct Bin {
    Integer count = 0;
    Integer offsets = 0;
};

int main(int argc, char **argv) try {
    require(argc == 4 || argc == 5, "usage: half_rectangles FIELD SIGN_FILE FREQUENCY [ORDER]");
    const Field field = sponsor_field(argv[1]);
    const Word n = argc == 5 ? std::stoull(argv[4]) : field.n;
    const Word k = std::stoull(argv[3]);
    require(n >= 4 && n <= field.n && field.n % n == 0 && k > 0 && k < n, "invalid input");
    const Word copies = std::gcd(k, n), period = n / copies;
    require(period % 4 == 0, "the character phases must have order divisible by four");
    const Word grid = std::min<Word>(256, period), step = period / grid;
    const Word mask = period - 1, reduced = k / copies;
    const auto g = power(field.g, field.n / n, field.p);
    const int generator_sign = mpz_legendre(g.get_mpz_t(), field.p.get_mpz_t());

    std::vector<Word> bits((n + 63) / 64);
    std::ifstream input(argv[2], std::ios::binary);
    input.read(reinterpret_cast<char*>(bits.data()), sizeof(Word) * bits.size());
    require(bool(input) && input.peek() == EOF && !(bits[0] & 1), "invalid sign file");
    std::vector<Bin> bins(grid);
    Integer row_sum = 0;
    for (Word j = 1; j < n; ++j) {
        const Integer sign = (bits[j / 64] >> (j % 64)) & 1 ? -1 : 1;
        const Word phase = (reduced * j) & mask;
        auto &bin = bins[phase / step];
        bin.count += sign;
        bin.offsets += sign * static_cast<Integer>(phase % step);
        row_sum += sign;
    }

    const Word output_frequency = (k + (generator_sign == -1 ? n / 2 : 0)) % n;
    const Integer offset = generator_sign == 1 ? static_cast<Integer>(n / 4) * row_sum : 0;
    // At small orders compare every phase with an independent direct character matrix.
    std::vector<mpz_class> sites;
    if (n <= 64) {
        for (Word i = 0; i < n; ++i) sites.push_back(power(g, i, field.p));
    }
    Integer best_raw = 0, best_centered = 0;
    Word best_phase = 0;
    for (Word shift = 0; shift < grid; ++shift) {
        Integer total = 0;
        for (Word b = 0; b < grid; ++b) {
            const Word start = ((b + shift) % grid) * step;
            const Integer triangle = static_cast<Integer>(period) -
                4 * static_cast<Integer>(std::min(start, period - start));
            const Integer slope = start < period / 2 ? -4 : 4;
            total += bins[b].count * triangle + slope * bins[b].offsets;
        }
        const Integer numerator = total * static_cast<Integer>(copies);
        require(numerator % 4 == 0, "nonintegral rectangle");
        const Integer centered = numerator / 4, raw = centered + offset;
        if (!sites.empty()) {
            Integer direct = 0;
            for (Word i = 0; i < n; ++i) {
                const Word phase = ((output_frequency / copies) * i - shift * step) & mask;
                if (phase >= period / 2) continue;
                for (Word j = 0; j < n; ++j) {
                    if (((reduced * j) & mask) >= period / 2) continue;
                    mpz_class difference = sites[i] - sites[j];
                    direct += mpz_legendre(difference.get_mpz_t(), field.p.get_mpz_t());
                }
            }
            require(direct == raw, "phase sum differs from direct matrix");
        }
        if (shift == 0 || std::abs(raw) > std::abs(best_raw)) {
            best_raw = raw;
            best_centered = centered;
            best_phase = shift * step;
        }
    }
    // Directly count overlap on each row displacement, without the grid aggregation.
    Integer check = 0;
    for (Word j = 1; j < n; ++j) {
        const Integer sign = (bits[j / 64] >> (j % 64)) & 1 ? -1 : 1;
        const Word phase = (reduced * j + best_phase) & mask;
        const Integer distance = static_cast<Integer>(std::min(phase, period - phase));
        const Integer baseline = static_cast<Integer>(period / (generator_sign == 1 ? 2 : 4));
        check += sign * static_cast<Integer>(copies) * (baseline - distance);
    }
    require(check == best_raw, "displacement-overlap check failed");
    std::cout << "field=" << argv[1] << " n=" << n << " input_k=" << k
              << " output_k=" << output_frequency << " period=" << period
              << " phase=" << best_phase << " grid=" << grid << " row=" << row_sum
              << " offset=" << offset << " centered=" << best_centered
              << " rectangle=" << best_raw << '\n';
    return 0;
} catch (const std::exception &error) {
    std::cerr << error.what() << '\n';
    return 1;
}
