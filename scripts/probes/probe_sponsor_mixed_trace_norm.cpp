// Certify a spectral norm using signed bits, integer Gram products and row sums.
// Compile with C++17, GMP and GMPXX. Run as probe FIELD order block workers.
#include "sponsor_phi_field.hpp"

#include <algorithm>
#include <cstdlib>
#include <future>
#include <iostream>
#include <set>
#include <vector>

using Integer = std::int64_t;

Integer ceil_sqrt(Integer value) {
    mpz_class input(static_cast<long>(value)), root;
    mpz_sqrt(root.get_mpz_t(), input.get_mpz_t());
    const Integer floor = root.get_si();
    return floor + (floor * floor < value);
}

// All input entries are bounded by 65536, and size <= 1024. Thus each dot
// product fits in a signed 64-bit integer, including all partial sums.
Integer norm_bound(const std::vector<int> &matrix, int size, int depth) {
    Integer direct = 0;
    for (int i = 0; i < size; ++i) {
        Integer row = 0;
        for (int j = 0; j < size; ++j) row += std::abs(matrix[i*size+j]);
        direct = std::max(direct, row);
    }
    if (!depth || direct == 0) return direct;
    std::vector<Integer> square(size * size);
    Integer maximum = 0;
    for (int i = 0; i < size; ++i) {
        for (int j = 0; j <= i; ++j) {
            Integer entry = 0;
            for (int k = 0; k < size; ++k)
                entry += static_cast<Integer>(matrix[i*size+k]) * matrix[j*size+k];
            square[i*size+j] = square[j*size+i] = entry;
            maximum = std::max(maximum, std::abs(entry));
        }
    }
    const Integer scale = std::max<Integer>(1, (maximum + 65535) / 65536);
    Integer error = 0;
    std::vector<int> rounded(size * size);
    for (int i = 0; i < size; ++i) {
        Integer row = 0;
        for (int j = 0; j < size; ++j) {
            const Integer x = square[i*size+j];
            const Integer q = (x + (x >= 0 ? scale/2 : -(scale/2))) / scale;
            rounded[i*size+j] = static_cast<int>(q);
            row += std::abs(x - scale*q);
        }
        error = std::max(error, row);
    }
    return std::min(direct, ceil_sqrt(scale * norm_bound(rounded, size, depth-1) + error));
}

struct Block {
    Integer norm_squared, sum;
};

// Each production pair has nonzero difference. The explicit zero-position
// correction also handles small control fields in which the two sets intersect.
Block check_block(const Field &field, const std::vector<mpz_class> &a,
                  const std::vector<mpz_class> &b, int start, int count) {
    const int cols = static_cast<int>(b.size()), words = (cols+63)/64;
    std::vector<Word> negatives(count * words);
    std::vector<int> zeros(count, -1);
    Integer total = 0;
    mpz_class delta;
    for (int i = 0; i < count; ++i) {
        for (int j = 0; j < cols; ++j) {
            mpz_sub(delta.get_mpz_t(), a[start+i].get_mpz_t(), b[j].get_mpz_t());
            const int sign = mpz_jacobi(delta.get_mpz_t(), field.p.get_mpz_t());
            total += sign;
            if (sign < 0) negatives[i*words+j/64] |= Word{1} << (j%64);
            if (sign == 0) zeros[i] = j;
        }
    }
    const auto encoded_sign = [&](int i, int j) {
        return 1 - 2 * static_cast<int>((negatives[i*words+j/64] >> (j%64)) & 1);
    };
    std::vector<int> gram(count * count);
    for (int i = 0; i < count; ++i) {
        for (int j = 0; j <= i; ++j) {
            int mismatches = 0;
            for (int w = 0; w < words; ++w)
                mismatches += __builtin_popcountll(negatives[i*words+w] ^ negatives[j*words+w]);
            int entry = cols - 2*mismatches;
            if (zeros[i] >= 0) entry -= encoded_sign(j, zeros[i]);
            if (zeros[j] >= 0) entry -= encoded_sign(i, zeros[j]);
            if (zeros[i] >= 0 && zeros[i] == zeros[j]) ++entry;
            gram[i*count+j] = gram[j*count+i] = entry;
        }
    }
    return {norm_bound(gram, count, 3), total};
}

// Independently check the small controls by ordinary field subtraction and
// exact rational elimination on the claimed positive-semidefinite matrix.
void check_control(const Field &field, const std::vector<mpz_class> &a,
                   const std::vector<mpz_class> &b, const Block &result) {
    const int rows = a.size(), cols = b.size();
    std::vector<int> signs(rows*cols);
    Integer total = 0;
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            const mpz_class value = (a[i]-b[j]+field.p) % field.p;
            const mpz_class symbol = power(value, (field.p.get_ui()-1)/2, field.p);
            const int sign = symbol == 0 ? 0 : symbol == 1 ? 1 : -1;
            require(sign != -1 || symbol == field.p-1, "small-field Euler criterion");
            signs[i*cols+j] = sign;
            total += sign;
        }
    }
    require(total == result.sum, "direct signed sum");
    std::vector<mpq_class> residual(rows*rows);
    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < rows; ++j) {
            long entry = i == j ? result.norm_squared : 0;
            for (int k = 0; k < cols; ++k) entry -= signs[i*cols+k]*signs[j*cols+k];
            residual[i*rows+j] = entry;
        }
    }
    for (int k = 0; k < rows; ++k) {
        const auto pivot = residual[k*rows+k];
        require(pivot >= 0, "negative Gram certificate pivot");
        for (int i = k+1; i < rows; ++i) {
            if (pivot == 0) {
                require(residual[i*rows+k] == 0, "nonzero column at zero pivot");
                continue;
            }
            const mpq_class factor = residual[i*rows+k]/pivot;
            for (int j = k+1; j < rows; ++j) residual[i*rows+j] -= factor*residual[k*rows+j];
        }
    }
}

void run(const Field &field, Word order, int block, int workers) {
    require(order >= 4 && order <= 65536 && (order & (order-1)) == 0
        && field.n % order == 0 && order < field.n, "proper dyadic subgroup order");
    require(block > 0 && block <= 1024 && workers > 0 && workers <= 64, "block and workers");
    require(field.p % 4 == 1 && mpz_probab_prime_p(field.p.get_mpz_t(), 25), "field check");
    require(power(field.g, field.n/2, field.p) == field.p-1, "generator order");
    const mpz_class step = power(field.g, field.n/order, field.p);
    std::vector<mpz_class> powers(order), a, b;
    powers[0] = 1;
    for (Word i = 1; i < order; ++i) powers[i] = powers[i-1]*step % field.p;
    for (Word i = 0; i < order; ++i) {
        const auto &inverse = powers[(order-i)%order];
        if (i <= order/2) a.push_back((powers[i]+inverse) % field.p);
        b.push_back((powers[i]+field.g*inverse) % field.p);
    }
    require(std::set<mpz_class>(a.begin(), a.end()).size() == a.size(), "row injectivity");
    require(std::set<mpz_class>(b.begin(), b.end()).size() == b.size(), "column injectivity");
    std::vector<std::future<Block>> jobs;
    for (int worker = 0; worker < workers; ++worker) {
        jobs.push_back(std::async(std::launch::async, [&,worker] {
            Block combined{};
            const int rows = static_cast<int>(a.size());
            for (int start = worker*block; start < rows; start += workers*block) {
                const Block part = check_block(field, a, b, start, std::min(block, rows-start));
                combined.norm_squared += part.norm_squared;
                combined.sum += part.sum;
            }
            return combined;
        }));
    }
    Block all{};
    for (auto &job : jobs) {
        const Block part = job.get();
        all.norm_squared += part.norm_squared;
        all.sum += part.sum;
    }
    if (order <= 64 && field.p.fits_ulong_p()) check_control(field, a, b, all);
    std::cout << "dimensions " << a.size() << " " << b.size()
              << "\nsigned sum " << all.sum
              << "\nsquared norm upper bound " << all.norm_squared
              << "\nnorm upper bound " << ceil_sqrt(all.norm_squared) << "\n";
}

int main(int argc, char **argv) {
    try {
        require(argc == 5, "usage: probe FIELD order block workers");
        run(sponsor_field(argv[1]), std::stoul(argv[2]), std::stoi(argv[3]), std::stoi(argv[4]));
    } catch (const std::exception &error) {
        std::cerr << error.what() << "\n";
        return 1;
    }
}
