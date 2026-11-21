#pragma once

#include "sponsor_phi_field.hpp"
#include <algorithm>
#include <cmath>
#include <vector>

using Integer = std::int64_t;
using Wide = __int128_t;
constexpr long root_scale = 1L << 40;
constexpr Integer data_scale = Integer{1} << 30;

struct Pair {
    Integer re, im;
};

// Inputs are fixed point, the second factor has denominator root_scale.
// The integer quotients introduce Euclidean error <2 output units.
inline Pair scaled_rotate(Pair z, Pair w, Integer scale) {
    return {static_cast<Integer>((Wide(z.re) * w.re - Wide(z.im) * w.im) / scale),
            static_cast<Integer>((Wide(z.im) * w.re + Wide(z.re) * w.im) / scale)};
}

inline Pair rotate(Pair z, Pair w) { return scaled_rotate(z,w,root_scale); }

inline mpz_class floor_sqrt(const mpz_class &x) {
    mpz_class y;
    mpz_sqrt(y.get_mpz_t(), x.get_mpz_t());
    return y;
}

// Store the roots for a radix-2 butterfly of width 2h at indices h..2h-1.
// All root certificates are exact integers. Starting at cos(pi/2)=0, compute
// enclosing intervals for sqrt((1 +/- cos(theta))/2), with denominator Q.
// The two rounded anchor coordinates each have error <=2/root_scale.
inline std::vector<Pair> stage_anchors(Word length, long scale = root_scale) {
    const unsigned log_n = __builtin_ctzll(length);
    std::vector<Pair> anchors(log_n);
    if (length > 2) anchors[1] = {0, scale};
    const mpz_class Q = mpz_class(1) << 192;
    mpz_class cos_lo = 0, cos_hi = 0;
    auto round_anchor = [&](const mpz_class &lo, const mpz_class &hi) {
        const mpz_class digit = lo * scale / Q;
        require(0 <= digit && digit <= scale && hi * scale <= (digit + 2) * Q,
                "root certificate too wide");
        return static_cast<Integer>(digit.get_si());
    };
    for (Word half = 4; half < length; half *= 2) {
        const mpz_class sin_lo = floor_sqrt(Q * (Q - cos_hi) / 2);
        const mpz_class sin_hi = floor_sqrt(Q * (Q - cos_lo) / 2) + 1;
        const mpz_class next_lo = floor_sqrt(Q * (Q + cos_lo) / 2);
        const mpz_class next_hi = floor_sqrt(Q * (Q + cos_hi) / 2) + 1;
        const Pair anchor{round_anchor(next_lo, next_hi), round_anchor(sin_lo, sin_hi)};
        cos_lo = next_lo;
        cos_hi = next_hi;
        anchors[__builtin_ctzll(half)] = anchor;
    }
    return anchors;
}

inline std::vector<Pair> make_roots(Word length) {
    std::vector<Pair> roots(length);
    roots[1] = {root_scale, 0};
    if (length == 2)
        return roots;
    roots[2] = roots[1];
    roots[3] = {0, root_scale};
    const auto anchors = stage_anchors(length);
    for (Word half = 4; half < length; half *= 2) {
        const Pair anchor = anchors[__builtin_ctzll(half)];
        for (Word i = half / 2; i < half; ++i) {
            roots[2 * i] = roots[i];
            roots[2 * i + 1] = rotate(roots[i], anchor);
        }
    }
    return roots;
}

inline void transform(std::vector<Pair> &v, const std::vector<Pair> &roots) {
    const Word length = v.size();
    for (Word i = 1, j = 0; i < length; ++i) {
        Word bit = length / 2;
        for (; j & bit; bit >>= 1)
            j ^= bit;
        j ^= bit;
        if (i < j)
            std::swap(v[i], v[j]);
    }
    for (Word h = 1; h < length; h *= 2) {
        for (Word i = 0; i < length; i += 2 * h) {
            for (Word j = 0; j < h; ++j) {
                const Pair a = v[i+j], b = rotate(v[i+j+h], roots[h+j]);
                v[i+j] = {a.re + b.re, a.im + b.im};
                v[i+j+h] = {a.re - b.re, a.im - b.im};
            }
        }
    }
}

// Root error after j products is <=7j/T, T=root_scale. Indeed an anchor has
// Euclidean error <=4/T and norm <=1+4/T. The next error is at most
// (1+4/T)*7j/T + 6/T <= 7(j+1)/T for j<=30. Thus epsilon=210/T suffices.
// At a butterfly whose two exact inputs have norm <=B, let the current
// absolute error bound be B*e. The output error divided by 2B is at most
// e + epsilon*(1+e)/2 + 1/(B*data_scale). Since B>=1 and e<=1, each
// stage adds <=epsilon+1/data_scale. Even at depth 30 this sum is <1.
// Coefficients fit int64 (absolute value <2*length*data_scale <=2^61);
// rotate uses two products <2^103 each. Magnitude squares fit signed int128.
inline Word fft_error(Word length) {
    Word stages = 0;
    for (Word i = length; i > 1; i /= 2)
        ++stages;
    return (length * stages * (210 + root_scale/data_scale) + root_scale-1) / root_scale;
}

// The floating-point guess affects speed only. The two integer comparisons
// certify ceil(sqrt(re^2+im^2)/data_scale) including equality at squares.
inline Word magnitude_ceil(Pair z) {
    const Wide square = Wide(z.re)*z.re + Wide(z.im)*z.im;
    Word a = static_cast<Word>(std::sqrt(static_cast<double>(square)) / data_scale);
    auto square_at = [](Word t) { return Wide(t)*t*data_scale*data_scale; };
    while (square_at(a) < square)
        ++a;
    while (a && square_at(a-1) >= square)
        --a;
    return a;
}
