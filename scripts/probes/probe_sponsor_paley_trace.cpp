// Exact Paley discrepancy on the inversion quotient {x+1/x : x in <g>}.
// Run as probe FIELD [workers]. FIELD can also be either small control below.
#include "sponsor_phi_field.hpp"

#include <array>
#include <functional>
#include <future>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>

using Classes = std::array<long, 4>;

int chi(const mpz_class &x, const mpz_class &p) {
    return mpz_jacobi(x.get_mpz_t(), p.get_mpz_t());
}

Classes count_range(const Field &field, Word begin, Word end, int epsilon) {
    Classes classes{};
    mpz_class x = power(field.g, begin, field.p), delta;
    for (Word j = begin; j < end; ++j) {
        delta = x - 1;
        const int h = chi(delta, field.p);
        require(h != 0, "unexpected identity in scan");
        classes[j % 4] += h;
        classes[(4 - j % 4) % 4] += (j % 2 ? epsilon : 1) * h;
        x *= field.g;
        x %= field.p;
    }
    require(x == power(field.g, end, field.p), "scan endpoint");
    return classes;
}

void run(const Field &field, unsigned workers) {
    const Word n = field.n, half = n / 2;
    require(n >= 4 && (n & (n - 1)) == 0 && n <= (1UL << 30), "dyadic order");
    require(field.p % 4 == 1 && mpz_probab_prime_p(field.p.get_mpz_t(), 25), "field check");
    require(power(field.g, half, field.p) == field.p - 1, "half-order check");
    require(workers >= 1 && workers <= 64, "worker count");
    const int epsilon = chi(field.g, field.p);
    std::vector<std::future<Classes>> jobs;
    for (unsigned j = 0; j < workers; ++j) {
        const Word begin = 1 + (half - 1) * j / workers;
        const Word end = 1 + (half - 1) * (j + 1) / workers;
        jobs.push_back(std::async(std::launch::async, count_range, std::cref(field),
                                  begin, end, epsilon));
    }
    Classes classes{};
    classes[half % 4] = chi(-2, field.p);
    for (auto &job : jobs) {
        const auto part = job.get();
        for (int j = 0; j < 4; ++j) classes[j] += part[j];
    }
    const long even = classes[0] + epsilon * classes[2];
    const long odd = classes[1] + epsilon * classes[3];
    const long multi = 2 * (even * even + epsilon * odd * odd);
    const long four_sum = multi + (epsilon == 1 ? 4 * static_cast<long>(n) : 0L) - 2;
    require(four_sum % 4 == 0, "endpoint correction");
    const long sum = four_sum / 4;
    const long odd_sum = even * odd;
    if (n <= 64) {
        std::vector<mpz_class> pows(n);
        std::vector<long> h(n);
        for (Word i = 0; i < n; ++i) {
            pows[i] = power(field.g, i, field.p);
            h[i] = chi(pows[i] - 1, field.p);
        }
        for (Word a = 0; a < n; ++a) {
            std::set<mpz_class> trace;
            for (Word i = 0; i < n; ++i)
                trace.insert((pows[i] + pows[(n + a - i) % n]) % field.p);
            require(trace.size() == half + 1 - a % 2, "trace size");
            long direct = 0;
            for (const auto &x : trace)
                for (const auto &y : trace) direct += chi(x - y, field.p);
            const long dilation_sign = (a / 2) % 2 ? epsilon : 1;
            require(direct == dilation_sign * (a % 2 ? odd_sum : sum), "trace discrepancy");
        }
        // The two-dimensional character expansion is integral in a primitive
        // n-th root. Check every coefficient reduced in the small control field.
        const auto index = [order = static_cast<long>(n)](long r) {
            return static_cast<Word>((r % order + order) % order);
        };
        std::vector<mpz_class> hat(n);
        for (Word a = 0; a < n; ++a)
            for (Word j = 0; j < n; ++j) hat[a] += h[j] * pows[a * j % n];
        for (long twist : {0, 1}) {
            std::vector<mpz_class> kernel(n*n), rows(n*n);
            for (Word i = 0; i < n; ++i) {
                for (Word j = 0; j < n; ++j) {
                    const mpz_class ti = pows[i] + pows[index(twist - static_cast<long>(i))];
                    const mpz_class tj = pows[j] + pows[index(twist - static_cast<long>(j))];
                    kernel[i*n+j] = chi(ti-tj, field.p);
                }
                for (Word b = 0; b < n; ++b)
                    for (Word j = 0; j < n; ++j) rows[i*n+b] += pows[b*j % n] * kernel[i*n+j];
            }
            for (Word a = 0; a < n; ++a) {
                for (Word b = 0; b < n; ++b) {
                    mpz_class actual, predicted;
                    for (Word i = 0; i < n; ++i) actual += pows[a*i % n] * rows[i*n+b];
                    const long frequency = a + (epsilon == -1 ? half : 0);
                    if (frequency % 2 == static_cast<long>(b % 2)) {
                        const Word u = index((frequency-static_cast<long>(b))/2);
                        const Word v = index((frequency+static_cast<long>(b))/2);
                        predicted = pows[v*twist % n] * hat[u] * hat[v]
                            + pows[(v+half)*twist % n] * hat[(u+half)%n] * hat[(v+half)%n];
                        if (twist) predicted *= epsilon;
                    }
                    require((actual-predicted) % field.p == 0, "Fourier identity");
                }
            }
        }
    }
    std::cout << "generator character " << epsilon << "\nresidue classes";
    for (long count : classes) std::cout << " " << count;
    std::cout << "\nrow sum " << std::accumulate(classes.begin(), classes.end(), 0L)
              << "\nmultiset sum " << multi << "\ntrace size " << half + 1
              << "\neven trace sum " << sum << "\nodd trace sum " << odd_sum << "\n";
}

int main(int argc, char **argv) {
    try {
        require(argc == 2 || argc == 3, "usage: probe FIELD [workers]");
        const std::string name = argv[1];
        const Field field = name == "nonsquare-control" ? Field{17, 3, 16} : sponsor_field(name);
        run(field, argc == 3 ? std::stoul(argv[2]) : 1);
    } catch (const std::exception &err) {
        std::cerr << err.what() << "\n";
        return 1;
    }
}
