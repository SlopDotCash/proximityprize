// Certify seven-center antipodality for equal-degree monic locator ratios on mu_64.
// Build with c++ -O3 -std=c++20 probe_mu64_seven_centers.cpp -o /tmp/mu64seven.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <vector>

using Centers = std::array<int, 5>;
using Weights = std::array<int, 48>;
using Key = std::array<int, 16>;
using Mask = std::uint32_t;

class Census {
    static constexpr int order = 64;
    int prime;
    bool reverse;
    std::array<int, 103> inverse{};
    std::array<Key, order> units{};
    std::array<std::array<Key, 48>, order> evaluations{};
    std::set<Mask> normalized;
    int representatives = 0;
    int asymmetric_kernels = 0;
    int max_dimension = 0;
    int solutions = 0;
    int max_matches = 0;

    // Even-site singleton, or odd-site antipodal pair, containing a given site.
    static int orbit(int site) {
        return site % 2 == 0 ? site / 2 : 32 + (site / 2) % 16;
    }

    static Mask mask_for(const Centers& centers, int shift, int multiplier) {
        Mask mask = 0;
        for (int x : centers) {
            int residue = ((x - shift + 32) * multiplier) % 32;
            mask |= Mask(1) << residue;
        }
        return mask;
    }

    int residue(int a) const { return (a % prime + prime) % prime; }

    void test_vector(const Weights& candidate) {
        Weights w{};
        for (int j = 0; j < 48; ++j) {
            int value = residue(candidate[j]);
            if (value > 1 && value != prime - 1) return;
            w[j] = value == prime - 1 ? -1 : value;
        }
        if (std::equal(w.begin(), w.begin() + 16, w.begin() + 16)) return;

        ++solutions;
        std::map<Key, int> fibers;
        for (int x = 0; x < order; ++x) {
            if (w[orbit(x)] != 0) continue;
            Key signature{};
            for (int j = 0; j < 48; ++j) {
                for (int r = 0; r < 16; ++r) signature[r] += w[j] * evaluations[x][j][r];
            }
            max_matches = std::max(max_matches, ++fibers[signature]);
        }
        assert(max_matches <= 6);
    }

    void enumerate(const std::vector<Weights>& basis, std::size_t index,
                   Weights& vector, bool signed_yet) {
        if (index == basis.size()) {
            test_vector(vector);
            return;
        }
        enumerate(basis, index + 1, vector, signed_yet);
        for (int j = 0; j < 48; ++j) vector[j] += basis[index][j];
        enumerate(basis, index + 1, vector, true);
        for (int j = 0; j < 48; ++j) vector[j] -= basis[index][j];
        if (signed_yet) {
            for (int j = 0; j < 48; ++j) vector[j] -= basis[index][j];
            enumerate(basis, index + 1, vector, true);
            for (int j = 0; j < 48; ++j) vector[j] += basis[index][j];
        }
    }

    void check(const Centers& centers) {
        Mask mask = mask_for(centers, 0, 1);
        if (normalized.contains(mask)) return;
        for (int x : centers) {
            for (int u = 1; u < 32; u += 2) normalized.insert(mask_for(centers, x, u));
        }
        ++representatives;

        std::vector<int> columns;
        for (int j = 0; j < 48; ++j) {
            if (j >= 32 || ((mask >> j) & 1) == 0) columns.push_back(j);
        }
        if (reverse) std::reverse(columns.begin(), columns.end());
        const int width = static_cast<int>(columns.size());
        constexpr int height = 1 + 4 * 16;
        std::array<std::array<int, 43>, height> matrix{};
        for (int j = 0; j < width; ++j) {
            const int original = columns[j];
            matrix[0][j] = original < 32 ? 1 : 2;
            for (int i = 1; i < 5; ++i) {
                for (int r = 0; r < 16; ++r) {
                    matrix[1 + (i - 1) * 16 + r][j] = residue(
                        evaluations[2 * centers[i]][original][r] -
                        evaluations[2 * centers[0]][original][r]);
                }
            }
        }
        std::vector<int> pivot(width, -1), free;
        int rank = 0;
        for (int col = 0; col < width; ++col) {
            int i = rank;
            while (i < height && !matrix[i][col]) ++i;
            if (i == height) {
                free.push_back(col);
                continue;
            }
            std::swap(matrix[i], matrix[rank]);
            int unit = inverse[matrix[rank][col]];
            for (int k = col; k < width; ++k)
                matrix[rank][k] = matrix[rank][k] * unit % prime;
            for (int row = 0; row < height; ++row) {
                if (row == rank || !matrix[row][col]) continue;
                int multiple = prime - matrix[row][col];
                for (int k = col; k < width; ++k)
                    matrix[row][k] = (matrix[row][k] + multiple * matrix[rank][k]) % prime;
            }
            pivot[col] = rank++;
        }
        std::vector<Weights> basis;
        bool allows_asymmetry = false;
        for (int f : free) {
            Weights v{};
            v[columns[f]] = 1;
            for (int j = 0; j < width; ++j) {
                if (pivot[j] >= 0) v[columns[j]] = residue(-matrix[pivot[j]][f]);
            }
            if (!std::equal(v.begin(), v.begin() + 16, v.begin() + 16)) allows_asymmetry = true;
            basis.push_back(v);
        }
        if (!allows_asymmetry) return;
        ++asymmetric_kernels;
        max_dimension = std::max(max_dimension, static_cast<int>(basis.size()));
        Weights vector{};
        enumerate(basis, 0, vector, false);
    }

public:
    Census(int modulus, bool reverse_columns) : prime(modulus), reverse(reverse_columns) {
        for (int a = 1; a < prime; ++a) {
            for (int b = 1; b < prime; ++b) if (a * b % prime == 1) inverse[a] = b;
            assert(inverse[a] != 0);
        }
        for (int k = 1; k < order; ++k) {
            int power_two = k & -k;
            for (int h = 0; h < power_two; ++h) {
                int i = (k / power_two + h * order / power_two) % order;
                ++units[k][(std::min(i, order - i) - 1) / 2];
            }
        }
        for (int x = 0; x < order; ++x) {
            for (int y = 0; y < order; ++y) {
                for (int r = 0; r < 16; ++r)
                    evaluations[x][orbit(y)][r] += units[(x - y + order) % order][r];
            }
        }
    }

    void run() {
        for (int a = 1; a < 32; ++a)
            for (int b = a + 1; b < 32; ++b)
                for (int c = b + 1; c < 32; ++c)
                    for (int d = c + 1; d < 32; ++d) check({0, a, b, c, d});
        assert(normalized.size() == 31465 && representatives == 454);
        assert(max_matches == 6);
        std::cout << "modulus " << prime << ", representatives " << representatives
                  << ", asymmetric kernels " << asymmetric_kernels
                  << ", largest nullity " << max_dimension << ", signed solutions up to sign "
                  << solutions << ", maximum equal signatures " << max_matches << '\n';
    }
};

int main() {
    Census(101, false).run();
    Census(103, true).run();
}
