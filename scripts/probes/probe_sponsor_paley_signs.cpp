// Store the exact sign row chi(1-g^i) on a dyadic subgroup for a Fourier calculation.
// Output consists of native uint64 words; bit i is one for a negative character.
// Position zero has its own zero symbol, and its stored bit is always zero.
#include "sponsor_phi_field.hpp"
#include <fstream>
#include <future>
#include <iostream>
#include <vector>

int main(int argc, char **argv) try {
    require(argc == 4 || argc == 5, "usage: signs FIELD OUTPUT WORKERS [ORDER]");
    Field f = sponsor_field(argv[1]);
    const Word n = argc == 5 ? std::stoull(argv[4]) : f.n;
    const unsigned workers = std::stoul(argv[3]);
    require(n >= 4 && n <= f.n && !(n & (n-1)) && f.n % n == 0, "invalid dyadic order");
    require(workers >= 1 && workers <= 4, "expected one to four workers");
    f.g = power(f.g, f.n / n, f.p);
    require(f.p % 4 == 1 && power(f.g, n/2, f.p) == f.p-1, "invalid field or generator");
    const int generator_sign = mpz_legendre(f.g.get_mpz_t(), f.p.get_mpz_t());
    const Word half = n / 2, half_words = (half + 63) / 64;
    std::vector<Word> bits((n + 63) / 64);
    std::vector<std::future<void>> tasks;
    for (unsigned shard = 0; shard < workers; ++shard) {
        const Word first = std::min(half, 64 * (shard * half_words / workers));
        const Word end = std::min(half, 64 * ((shard+1) * half_words / workers));
        tasks.push_back(std::async(std::launch::async, [&, first, end]() {
            mpz_class x = power(f.g, first, f.p), v;
            for (Word i = first; i < end; ++i) {
                mpz_ui_sub(v.get_mpz_t(), 1, x.get_mpz_t());
                const int s = mpz_jacobi(v.get_mpz_t(), f.p.get_mpz_t());
                require((s == 0) == (i == 0), "wrong number of zeros");
                if (s < 0) bits[i/64] |= Word{1} << (i % 64);
                mpz_mul(x.get_mpz_t(), x.get_mpz_t(), f.g.get_mpz_t());
                mpz_mod(x.get_mpz_t(), x.get_mpz_t(), f.p.get_mpz_t());
            }
            require(x == power(f.g, end, f.p), "incorrect shard endpoint");
        }));
    }
    for (auto &task : tasks) task.get();
    // For p = 1 mod 4 the reflection contributes chi(g)^i.
    for (Word i = 1; i < half; ++i) {
        bool neg = (bits[i/64] >> (i % 64)) & 1;
        if (generator_sign < 0 && (i & 1)) neg = !neg;
        if (neg) bits[(n-i)/64] |= Word{1} << ((n-i) % 64);
    }
    mpz_class two = 2;
    if (mpz_legendre(two.get_mpz_t(), f.p.get_mpz_t()) < 0)
        bits[half/64] |= Word{1} << (half % 64);
    Word negatives = 0;
    for (Word w : bits) negatives += __builtin_popcountll(w);
    const std::int64_t row = std::int64_t(n-1) - 2*std::int64_t(negatives);
    std::ofstream file(argv[2], std::ios::binary);
    file.write(reinterpret_cast<const char*>(bits.data()), bits.size() * sizeof(Word));
    file.close();
    require(bool(file), "could not write sign vector");
    std::cout << "field=" << argv[1] << " n=" << n << " generator_sign=" << generator_sign
              << " negatives=" << negatives << " row=" << row << '\n';
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n'; return 1;
}
