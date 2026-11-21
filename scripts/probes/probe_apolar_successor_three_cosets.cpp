// Exhaustive exact-error-support check for the first successor at RS(32,16).
// Build with c++ -O3 -std=c++17; no external libraries.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>

namespace {
constexpr int p = 97, h = 8, n = 4 * h;
using Coeff = std::array<int, h>;
std::array<int, n> domain;
std::array<int, p> inverse;
std::array<bool, p> neighbors{};
Coeff target{};
std::uint64_t supports = 0;

int mod(int x) { return (x % p + p) % p; }
int power(int x, int n) {
    int a = 1;
    for (; n; n >>= 1, x = x*x%p) if (n & 1) a = a*x%p;
    return a;
}

// Test whether (Y-t)G_E and G_D are proportional modulo Y^h. Constant
// terms determine the scaling, so each remaining coefficient is linear in t.
void inspect(const Coeff& g) {
    ++supports;
    const int ratio = g[0] * inverse[target[0]] % p;
    int t = -1;
    for (int j = 1; j < h; ++j) {
        const int b = mod(g[j] - ratio*target[j]);
        if (!b) {
            if (g[j-1]) return;
        } else {
            const int candidate = g[j-1]*inverse[b]%p;
            if (candidate != t && t >= 0) return;
            t = candidate;
        }
    }
    if (t <= 0) throw std::runtime_error("unexpected zero or deficient condition");
    neighbors[t] = true;
}

void subsets(int pos, int need, const Coeff& g) {
    if (!need) { inspect(g); return; }
    for (int i = pos; i <= n-need; ++i) {
        Coeff next;
        next[0] = mod(-domain[i]*g[0]);
        for (int j = 1; j < h; ++j) next[j] = mod(g[j-1]-domain[i]*g[j]);
        subsets(i+1, need-1, next);
    }
}
}  // namespace

int main() {
    for (int i = 1; i < p; ++i) inverse[i] = power(i, p-2);
    const int g = power(5, (p-1)/n);
    for (int i = 0; i < n; ++i) domain[i] = power(g, i);
    if (power(g, n/2) != p-1) throw std::runtime_error("invalid generator");
    const int d1 = domain[3], d2 = domain[7];
    target[0] = d1*d2%p; target[1] = mod(-d1-d2); target[2] = 1;
    Coeff initial{}; initial[0] = 1;
    subsets(0, h+1, initial);
    std::set<int> predicted, actual;
    for (int i = 0; i < n; ++i)
        if (i % 4 != 3 || domain[i] == d1 || domain[i] == d2) predicted.insert(domain[i]);
    for (int t = 0; t < p; ++t) if (neighbors[t]) actual.insert(t);
    if (supports != 28048800 || actual != predicted || actual.size() != 3*h+2)
        throw std::runtime_error("bad set disagrees with the classification");
    // Directly check each folded neighbor on the original received rows and
    // the fresh failure of the row direction on its agreement witness.
    for (int t : actual) {
        int coset = 0;
        while (coset < 3 && t != d1 && t != d2 && power(t,h) != power(domain[coset],h)) ++coset;
        if (coset == 3) throw std::runtime_error("missing coset");
        int errors = 0, joint_core = 0;
        const int alpha = power(domain[coset], h);
        for (int y : domain) {
            int V1 = 1, Vi = 1;
            for (int a : domain) {
                if (a==d1 || a==d2) continue;
                if (power(a,h)!=1) V1=V1*mod(y-a)%p;
                if (power(a,h)!=alpha) Vi=Vi*mod(y-a)%p;
            }
            const int den = inverse[power(y,h)];
            const int Li = mod(V1-alpha*Vi)*den%p;
            const int u = y*V1%p*den%p, v=mod(-V1*den);
            const bool agr = mod(u+t*v)==mod((y-t)*Li);
            errors += !agr;
            joint_core += agr && v==mod(-Li);
            if (y==t && (!agr || v==mod(-Li))) throw std::runtime_error("joint fresh site");
        }
        if (errors!=h+1 || joint_core!=3*h-2) throw std::runtime_error("wrong witness");
    }
    std::cout << "F97 RS(32,16): " << supports << " error supports, "
              << actual.size() << " bad parameters, 9 errors; all 97 scalar decisions agree\n";
}
