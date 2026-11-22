// Enumerate a fixed-point enclosure of a Gram ellipsoid. The caller verifies
// arithmetic bounds before invoking this helper and checks every leaf exactly.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string_view>
#include <vector>

using Integer = std::int64_t;

class Enclosure {
    Integer scale;
    std::vector<std::vector<Integer>> coefficients;
    std::vector<Integer> weights;
    std::vector<Integer> coordinates;
    std::vector<Integer> shifts;
    int target = -1;

    static Integer floor_div(Integer value, Integer positive) {
        return value >= 0 ? value / positive : -((-value + positive - 1) / positive);
    }

    static Integer integer_sqrt(Integer value) {
        auto root = static_cast<Integer>(std::sqrt(static_cast<double>(value)));
        while (static_cast<__int128>(root + 1) * (root + 1) <= value) ++root;
        while (static_cast<__int128>(root) * root > value) --root;
        return root;
    }

public:
    Enclosure(int dimension, Integer scale_value) :
        scale(scale_value), coefficients(dimension), weights(dimension),
        coordinates(dimension), shifts(dimension) {}

    bool read() {
        for (std::size_t i = 0; i < weights.size(); ++i) {
            coefficients[i].resize(i);
            if (!(std::cin >> weights[i]) || weights[i] <= 0) return false;
            for (Integer &entry : coefficients[i]) {
                if (!(std::cin >> entry)) return false;
            }
        }
        return true;
    }

    bool read_target(int index) {
        target = index;
        for (Integer &entry : shifts) {
            if (!(std::cin >> entry)) return false;
        }
        return true;
    }

    void visit(int i, Integer error, Integer remaining) {
        if (i < 0) {
            if (target >= 0) std::cout << target << ' ';
            for (Integer value : coordinates) std::cout << value << ' ';
            std::cout << '\n';
            return;
        }
        Integer center_offset = shifts[i];
        Integer reach = integer_sqrt(remaining / weights[i]) + error;
        Integer lower = -floor_div(reach + center_offset, scale);
        Integer upper = floor_div(reach - center_offset, scale);
        for (Integer value = lower; value <= upper; ++value) {
            coordinates[i] = value;
            for (int j = 0; j < i; ++j) shifts[j] += value * coefficients[i][j];
            Integer residual = std::max<Integer>(0, std::abs(scale * value + center_offset) - error);
            visit(i - 1, error + std::abs(value), remaining - weights[i] * residual * residual);
            for (int j = 0; j < i; ++j) shifts[j] -= value * coefficients[i][j];
        }
    }
};

int main(int argc, char **argv) {
    std::ios::sync_with_stdio(false);
    int dimension;
    Integer scale, budget;
    if (!(std::cin >> dimension >> scale >> budget) || dimension < 1 ||
        dimension > 100 || scale <= 0 || budget < 0) return 1;
    Enclosure enclosure(dimension, scale);
    if (!enclosure.read()) return 1;
    if (argc == 1) {
        enclosure.visit(dimension - 1, 0, budget);
    } else {
        if (argc != 2 || std::string_view(argv[1]) != "--affine") return 1;
        int count;
        Integer error;
        if (!(std::cin >> count >> error) || count < 0 || error < 0) return 1;
        for (int i = 0; i < count; ++i) {
            if (!enclosure.read_target(i)) return 1;
            enclosure.visit(dimension - 1, error, budget);
        }
    }
}
