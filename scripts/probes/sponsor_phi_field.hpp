#pragma once

#include <cstdint>
#include <gmpxx.h>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>

using Word = std::uint64_t;
static_assert(std::numeric_limits<unsigned long>::digits == 64,
              "requires 64-bit GMP unsigned long");

struct Field {
    mpz_class p, g;
    Word n;
};

inline void require(bool condition, const std::string &message) {
    if (!condition)
        throw std::runtime_error(message);
}

inline mpz_class power(const mpz_class &x, Word r, const mpz_class &p) {
    mpz_class y;
    mpz_powm_ui(y.get_mpz_t(), x.get_mpz_t(), r, p.get_mpz_t());
    return y;
}

inline Field sponsor_field(const std::string &name) {
    const std::map<std::string, Field> fields{
        {"first",
         {mpz_class("365375409332725729550921208179070755120141565953"),
          mpz_class("303645430271030343624574566109998498685964493478"), 1UL << 30}},
        {"second",
         {mpz_class("730750818665451459101842416358141509841924915201"),
          mpz_class("192152681249815148642741928588691886362054863855"), 1UL << 30}},
        {"positive-control", {17318209, power(7, (17318209 - 1) / 64, 17318209), 64}},
        {"primitive-control", {17, 3, 16}},
        {"sextic-control", {97, 8, 16}}};
    return fields.at(name);
}
