// Certify the cyclic interval covers used for primitive quotients from 512 through 4096.
// Compile with c++ -std=c++17 -O2 probe_monomial_pair_sum_widths.cpp -o /tmp/pairwidth.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdio>
#include <numeric>
#include <set>
#include <vector>

using Quad = std::array<int, 4>;

static std::set<Quad> exceptional_spectrum() {
    std::set<Quad> orbit;
    const Quad initial{0, 1, 77, 163};
    for (int multiplier = 1; multiplier < 512; multiplier += 2) {
        for (int start : initial) {
            Quad image;
            std::transform(initial.begin(), initial.end(), image.begin(),
                [&](int x) { return (multiplier * (x - start + 512)) % 512; });
            std::sort(image.begin(), image.end());
            if (image[1] == 1) orbit.insert(image);
        }
    }
    return orbit;
}

static bool two_pairs_mod_sixteen(const Quad& exponents) {
    std::array<int, 16> counts{};
    for (int x : exponents) ++counts[x % 16];
    return std::count(counts.begin(), counts.end(), 2) == 2;
}

static bool narrow_pair_sums(int n, int a, int b) {
    const int mask = n - 1;
    // Opposite sums are the only overlaps when the four exponents are distinct.
    int overlaps = ((1-a-b) % n == 0) + ((a-1-b) % n == 0) + ((b-1-a) % n == 0);
    if (overlaps >= 2) return false;
    const std::array<int, 6> sums{1, a, b, 1+a, 1+b, a+b};
    for (int h = 1; h < n/2; h += 2) {
        std::array<int, 6> sites;
        std::transform(sums.begin(), sums.end(), sites.begin(),
                       [&](int x) { return (h*x) & mask; });
        std::sort(sites.begin(), sites.end());
        int gap = n-sites.back()+sites.front();
        for (int i = 1; i < 6; ++i) gap = std::max(gap, sites[i]-sites[i-1]);
        if (16*(n-gap) <= 3*n) return true;
    }
    return false;
}

int main() {
    const auto exceptional = exceptional_spectrum();
    std::vector<bool> previous;
    for (int n = 8; n <= 4096; n *= 2) {
        int half = n/2, paired = 0, six = 0;
        std::vector<bool> covered(n*n, false);
        for (int a = 2; a < n; ++a) {
            for (int b = a+1; b < n; ++b) {
                const bool inherited = !previous.empty() && previous[(a%half)*half+b%half];
                if (inherited || narrow_pair_sums(n, a, b)) {
                    covered[a*n+b] = covered[b*n+a] = true;
                    continue;
                }
                if (n < 512) continue;
                const int gap = std::max({std::gcd(n,a), std::gcd(n,b), std::gcd(n,b-a),
                                          std::gcd(n,a-1), std::gcd(n,b-1)});
                if (gap >= 32) continue;
                const Quad exponents{0, 1, a, b};
                if (n == 512 && gap == 16 && two_pairs_mod_sixteen(exponents)) ++paired;
                else if (n == 512 && exceptional.count(exponents)) ++six;
                else {
                    std::fprintf(stderr, "Uncovered tuple %d %d %d\n", n, a, b);
                    return 1;
                }
            }
        }
        if (n >= 512) {
            assert(paired == (n == 512 ? 64 : 0) && six == (n == 512 ? 6 : 0));
            std::printf("%d sites: %d paired configurations, %d exceptional configurations\n",
                        n, paired, six);
        }
        previous.swap(covered);
    }
}
