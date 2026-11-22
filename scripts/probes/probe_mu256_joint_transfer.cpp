// Exhaust the integral outer approximation supplied by the exact rational verifier.
// Input is on stdin. Only the half with positive last nonzero coordinate is needed.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>

namespace {
using Integer = std::int64_t;
constexpr int max_dimension = 128;
int dimension;
Integer unit;
std::array<Integer, max_dimension> weights{}, caps{}, sums{};
std::array<std::array<Integer, max_dimension>, max_dimension> coefficients{};
std::uint64_t nodes = 0;

Integer floor_div(Integer a, Integer b) {
    return a >= 0 ? a / b : -((-a + b - 1) / b);
}

Integer integer_sqrt(Integer a) {
    Integer x = static_cast<Integer>(std::sqrt(static_cast<long double>(a)));
    while ((x + 1) * (x + 1) <= a) ++x;
    while (x * x > a) --x;
    return x;
}

bool has_nonzero(int i, Integer remaining, Integer error, bool active) {
    ++nodes;
    if (i < 0) return active;
    const Integer centre = sums[i];
    const Integer width = integer_sqrt(remaining / weights[i]) + error;
    Integer lo = std::max(-caps[i], -floor_div(centre + width, unit));
    const Integer hi = std::min(caps[i], floor_div(-centre + width, unit));
    if (!active) lo = std::max<Integer>(0, lo);
    for (Integer z = lo; z <= hi; ++z) {
        const Integer distance = std::max<Integer>(0, std::abs(unit * z + centre) - error);
        const Integer cost = weights[i] * distance * distance;
        if (z) for (int j = 0; j < i; ++j) sums[j] += z * coefficients[i][j];
        if (has_nonzero(i - 1, remaining - cost, error + std::abs(z), active || z != 0))
            return true;
        if (z) for (int j = 0; j < i; ++j) sums[j] -= z * coefficients[i][j];
    }
    return false;
}
}

int main() {
    Integer budget;
    if (!(std::cin >> dimension >> budget >> unit) || dimension < 1 || dimension > max_dimension ||
        budget < 0 || budget > (Integer{1} << 46) || unit < 1 || unit > (Integer{1} << 18))
        return 2;
    for (int i = 0; i < dimension; ++i)
        if (!(std::cin >> weights[i]) || weights[i] < 1) return 2;
    for (int i = 0; i < dimension; ++i)
        if (!(std::cin >> caps[i]) || caps[i] < 0 || caps[i] > (Integer{1} << 16)) return 2;
    for (int i = 0; i < dimension; ++i)
        for (int j = 0; j < dimension; ++j)
            if (!(std::cin >> coefficients[i][j]) ||
                coefficients[i][j] < -(Integer{1} << 22) || coefficients[i][j] > (Integer{1} << 22))
                return 2;
    // The input limits keep every centre at most 2^45 and error at most 2^23.
    // By the closed coordinate interval, 0 <= cost <= remaining <= 2^46.
    const bool hit = has_nonzero(dimension - 1, budget, 0, false);
    std::cout << nodes << ' ' << hit << '\n';
    return 0;
}
