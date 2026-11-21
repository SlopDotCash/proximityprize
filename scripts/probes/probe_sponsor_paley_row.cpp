// Exact classical Paley character sums on the dyadic subgroups of a prize field.
// Build with C++17, GMP and GMPXX. Usage: probe FIELD [workers].
#include "sponsor_phi_field.hpp"

#include <functional>
#include <future>
#include <iostream>
#include <vector>

using Counts = std::vector<long>;

// Pair exponent i with -i. For the quadratic character their contributions differ
// by the factor chi(-g^i). Bucket by the exact order of g^i.
Counts count_interval(const Field &field, Word begin, Word end, int log_order,
                      int generator_sign, int minus_one_sign) {
    Counts sums(log_order + 1);
    mpz_class element = power(field.g, begin, field.p), numerator;
    for (Word i = begin; i < end; ++i) {
        const int pair_weight = 1 + minus_one_sign * (i % 2 ? generator_sign : 1);
        if (pair_weight != 0) {
            mpz_ui_sub(numerator.get_mpz_t(), 1, element.get_mpz_t());
            const int sign = mpz_jacobi(numerator.get_mpz_t(), field.p.get_mpz_t());
            if (!sign) throw std::runtime_error("unexpected identity inside scan");
            sums[log_order - __builtin_ctzll(i)] += pair_weight * sign;
        }
        element *= field.g;
        element %= field.p;
    }
    require(element == power(field.g, end, field.p), "worker endpoint");
    return sums;
}

void run(const Field &field, unsigned workers) {
    require(workers >= 1 && workers <= 64, "worker count must lie in [1,64]");
    require(field.n >= 2 && (field.n & (field.n - 1)) == 0, "dyadic order");
    require(mpz_probab_prime_p(field.p.get_mpz_t(), 25) != 0, "composite modulus");
    // The production moduli have separate Lean Lucas certificates.
    require(power(field.g, field.n / 2, field.p) == field.p - 1, "half-order check");
    const int log_order = __builtin_ctzll(field.n);
    const int generator_sign = mpz_jacobi(field.g.get_mpz_t(), field.p.get_mpz_t());
    const int minus_one_sign = field.p % 4 == 1 ? 1 : -1;
    const Word half = field.n / 2;
    std::vector<std::future<Counts>> jobs;
    for (unsigned i = 0; i < workers; ++i) {
        Word begin = 1 + (half - 1) * i / workers;
        Word end = 1 + (half - 1) * (i + 1) / workers;
        jobs.push_back(std::async(std::launch::async, count_interval, std::cref(field),
                                 begin, end, log_order, generator_sign, minus_one_sign));
    }
    Counts sums(log_order + 1);
    // The identity contributes zero and the unique order-two element contributes chi(2).
    const mpz_class two = 2;
    sums[1] = mpz_jacobi(two.get_mpz_t(), field.p.get_mpz_t());
    for (auto &job : jobs) {
        Counts part = job.get();
        for (int d = 1; d <= log_order; ++d)
            sums[d] += part[d];
    }
    long row = 0;
    for (int d = 1; d <= log_order; ++d) {
        row += sums[d];
        const Word order = Word{1} << d;
        const bool all_squares = d < log_order || generator_sign == 1;
        mpz_class double_sum = all_squares ? mpz_class(row) * static_cast<unsigned long>(order) : mpz_class(0);
        std::cout << order << " " << row << " " << double_sum << "\n";
    }
}

int main(int argc, char **argv) {
    try {
        require(argc == 2 || argc == 3, "usage: probe FIELD [workers]");
        run(sponsor_field(argv[1]), argc == 3 ? std::stoul(argv[2]) : 1);
        return 0;
    } catch (const std::exception &error) {
        std::cerr << error.what() << "\n";
        return 1;
    }
}
