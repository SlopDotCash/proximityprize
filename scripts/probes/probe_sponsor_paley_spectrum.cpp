// Bound every singular value of the quadratic-character matrix on a dyadic subgroup.
// c++ -O3 -std=c++17 probe_sponsor_paley_spectrum.cpp -lgmpxx -lgmp -o spectrum
// spectrum first 128 4          (optional fourth argument: smaller subgroup order)
//
// The matrix at (g^i,g^j) is chi(g)^i a[j-i], with a[i]=chi(1-g^i).
// Its singular values are the magnitudes of the length-n DFT of a. For M residue
// classes and L=n/M the triangle inequality bounds the k-th magnitude by
// sum_r |DFT_L(a[r+Mj])[k mod L]|. Reflection i -> -i pairs rows r and M-r
// with equal Fourier magnitudes because chi(-1)=1, M is even and chi(g)=+/-1.
// The final maximum retains the common frequency in all the row bounds.
#include "sponsor_phi_field.hpp"

#include <algorithm>
#include <atomic>
#include <cmath>
#include <future>
#include <iostream>
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
Pair rotate(Pair z, Pair w) {
    return {static_cast<Integer>((Wide(z.re) * w.re - Wide(z.im) * w.im) / root_scale),
            static_cast<Integer>((Wide(z.im) * w.re + Wide(z.re) * w.im) / root_scale)};
}

mpz_class floor_sqrt(const mpz_class &x) {
    mpz_class y;
    mpz_sqrt(y.get_mpz_t(), x.get_mpz_t());
    return y;
}

// Store the roots for a radix-2 butterfly of width 2h at indices h..2h-1.
// All root certificates are exact integers. Starting at cos(pi/2)=0, compute
// enclosing intervals for sqrt((1 +/- cos(theta))/2), with denominator Q.
// The two rounded anchor coordinates each have error <=2/root_scale.
std::vector<Pair> make_roots(Word length) {
    std::vector<Pair> roots(length);
    roots[1] = {root_scale, 0};
    if (length == 2)
        return roots;
    roots[2] = roots[1];
    roots[3] = {0, root_scale};
    const mpz_class Q = mpz_class(1) << 192;
    mpz_class cos_lo = 0, cos_hi = 0;
    auto round_anchor = [&](const mpz_class &lo, const mpz_class &hi) {
        const mpz_class digit = lo * root_scale / Q;
        require(0 <= digit && digit <= root_scale && hi * root_scale <= (digit + 2) * Q,
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
        for (Word i = half / 2; i < half; ++i) {
            roots[2 * i] = roots[i];
            roots[2 * i + 1] = rotate(roots[i], anchor);
        }
    }
    return roots;
}

void transform(std::vector<Pair> &v, const std::vector<Pair> &roots) {
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
Word fft_error(Word length) {
    Word stages = 0;
    for (Word i = length; i > 1; i /= 2)
        ++stages;
    return (length * stages * (210 + root_scale/data_scale) + root_scale-1) / root_scale;
}

// The floating-point guess affects speed only. The two integer comparisons
// certify ceil(sqrt(re^2+im^2)/data_scale) including equality at squares.
Word magnitude_ceil(Pair z) {
    const Wide square = Wide(z.re)*z.re + Wide(z.im)*z.im;
    Word a = static_cast<Word>(std::sqrt(static_cast<double>(square)) / data_scale);
    auto square_at = [](Word t) { return Wide(t)*t*data_scale*data_scale; };
    while (square_at(a) < square)
        ++a;
    while (a && square_at(a-1) >= square)
        --a;
    return a;
}

struct Partial {
    std::vector<Word> envelope;
    Integer dc;
    Word completed;
};

Partial rows(const Field &f, Word blocks, const std::vector<Pair> &roots,
             int gen_sign, std::atomic<Word> &next) {
    const Word length = f.n/blocks, error = fft_error(length);
    const mpz_class step = power(f.g, blocks, f.p);
    std::vector<Pair> v(length);
    Partial out{std::vector<Word>(length/2 + 1), 0, 0};
    for (;;) {
        const Word r = next.fetch_add(1);
        if (r > blocks/2)
            break;
        const bool paired = r != 0 && 2*r != blocks;
        const mpz_class start = power(f.g, r, f.p);
        mpz_class x = start, diff;
        Integer dc = 0, alternating = 0;
        Word zeros = 0;
        for (Word j = 0; j < length; ++j) {
            mpz_ui_sub(diff.get_mpz_t(), 1, x.get_mpz_t());
            const int s = mpz_legendre(diff.get_mpz_t(), f.p.get_mpz_t());
            dc += s;
            alternating += (j & 1) ? -s : s;
            zeros += (s == 0);
            v[j] = {s * data_scale, 0};
            mpz_mul(x.get_mpz_t(), x.get_mpz_t(), step.get_mpz_t());
            mpz_mod(x.get_mpz_t(), x.get_mpz_t(), f.p.get_mpz_t());
        }
        require(x == start && zeros == (r == 0), "incorrect orbit");
        transform(v, roots);
        require(v[0].re == dc*data_scale && v[0].im == 0 &&
                v[length/2].re == alternating*data_scale && v[length/2].im == 0,
                "DC or Nyquist check failed");
        const Word multiplicity = paired ? 2 : 1;
        for (Word k = 0; k <= length/2; ++k) {
            const Word roundoff = k == 0 || 2*k == length ? 0 : error;
            out.envelope[k] += multiplicity * (magnitude_ceil(v[k]) + roundoff);
        }
        const int inverse_sign = gen_sign == -1 && (r & 1) ? -1 : 1;
        out.dc += paired ? dc*(1+inverse_sign) : dc;
        out.completed += multiplicity;
    }
    return out;
}

int main(int argc, char **argv) try {
    require(argc == 4 || argc == 5, "usage: spectrum FIELD BLOCKS WORKERS [ORDER]");
    Field f = sponsor_field(argv[1]);
    const Word blocks = std::stoull(argv[2]), workers = std::stoull(argv[3]);
    const Word order = argc == 5 ? std::stoull(argv[4]) : f.n;
    require(order >= 4 && order <= (Word{1} << 30) && f.n % order == 0 &&
            !(order & (order-1)), "invalid dyadic subgroup");
    require(blocks >= 2 && blocks <= order/2 && !(blocks & (blocks-1)), "invalid block count");
    require(workers >= 1 && workers <= 4, "expected one to four workers");
    f.g = power(f.g, f.n / order, f.p);
    f.n = order;
    require(f.p % 4 == 1 && power(f.g, f.n/2, f.p) == f.p-1, "wrong field or generator");
    const int gen_sign = mpz_legendre(f.g.get_mpz_t(), f.p.get_mpz_t());
    const Word length = order/blocks;
    const Word bytes = length*sizeof(Pair)*(workers+1) + (length/2+1)*sizeof(Word)*(workers+1);
    require(bytes < 950000000, "working arrays exceed 950 MB; increase blocks or reduce workers");
    const auto roots = make_roots(length);
    std::atomic<Word> next{0};
    std::vector<std::future<Partial>> tasks;
    for (Word i = 0; i < workers; ++i)
        tasks.push_back(std::async(std::launch::async, rows, std::cref(f), blocks,
                                   std::cref(roots), gen_sign, std::ref(next)));
    Partial total{std::vector<Word>(length/2+1), 0, 0};
    for (auto &task : tasks) {
        auto part = task.get();
        for (Word k = 0; k <= length/2; ++k)
            total.envelope[k] += part.envelope[k];
        total.dc += part.dc;
        total.completed += part.completed;
    }
    require(total.completed == blocks, "incomplete residue coverage");
    const auto largest = std::max_element(total.envelope.begin(), total.envelope.end());
    std::cout << "field=" << argv[1] << " order=" << order << " blocks=" << blocks
              << " row_length=" << length << " workers=" << workers
              << " generator_sign=" << gen_sign << " row_sum=" << total.dc
              << " fft_error_per_row=" << fft_error(length)
              << " maximizing_residue=" << (largest-total.envelope.begin())
              << " singular_value_upper=" << *largest << '\n';
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
