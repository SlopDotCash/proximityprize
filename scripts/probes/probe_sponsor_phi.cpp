// Exhaustive G139 half-window calculation at the two named sponsor primes.
// Build: c++ -O3 -std=c++17 probe_sponsor_phi.cpp -lgmpxx -lgmp -o phi
// Run:   phi first|second|positive-control NEW_DIRECTORY [workers]
// Scratch use at n=2^30: 4 GiB on disk and about 256 MiB for one sorting bucket.
#include "sponsor_phi_field.hpp"

#include <algorithm>
#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <future>
#include <gmpxx.h>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

namespace fs = std::filesystem;
const unsigned buckets = 16;

fs::path shard_file(const fs::path &dir, unsigned worker, unsigned bucket) {
    return dir / (std::to_string(worker) + "-" + std::to_string(bucket) + ".u64");
}

// Enumerate [lo,hi). A check against independent exponentiation detects a
// truncated or shifted recurrence. Each invocation starts directly at g^lo.
template <class Visit>
void visit_range(const Field &f, Word lo, Word hi, Visit visit) {
    mpz_class x = power(f.g, lo, f.p), base, phi;
    for (Word r = lo; r < hi; ++r) {
        mpz_sub_ui(base.get_mpz_t(), x.get_mpz_t(), 1);
        mpz_powm_ui(phi.get_mpz_t(), base.get_mpz_t(), f.n, f.p.get_mpz_t());
        visit(r, phi);
        mpz_mul(x.get_mpz_t(), x.get_mpz_t(), f.g.get_mpz_t());
        mpz_mod(x.get_mpz_t(), x.get_mpz_t(), f.p.get_mpz_t());
    }
    require(x == power(f.g, hi, f.p), "shard endpoint check failed");
}

void emit(const Field &f, const fs::path &dir, unsigned worker, Word lo, Word hi) {
    std::array<std::ofstream, buckets> files;
    for (unsigned b = 0; b < buckets; ++b) {
        files[b].exceptions(std::ios::failbit | std::ios::badbit);
        files[b].open(shard_file(dir, worker, b), std::ios::binary);
    }
    visit_range(f, lo, hi, [&](Word, const mpz_class &v) {
        const Word tag = v.get_ui();
        files[tag >> 60].write(reinterpret_cast<const char *>(&tag), sizeof(tag));
    });
    for (auto &file : files) file.close();
}

// Distinct low limbs prove distinct field values. Repeated low limbs alone
// prove nothing, so keep all repeated tags for exact recomputation.
std::set<Word> find_repeated(const fs::path &dir, unsigned workers, Word expected) {
    std::set<Word> repeated;
    Word count = 0;
    for (unsigned b = 0; b < buckets; ++b) {
        std::vector<Word> tags;
        std::size_t entries = 0;
        for (unsigned w = 0; w < workers; ++w) {
            auto bytes = fs::file_size(shard_file(dir, w, b));
            require(bytes % sizeof(Word) == 0, "partial tag");
            entries += bytes / sizeof(Word);
        }
        tags.reserve(entries);
        for (unsigned w = 0; w < workers; ++w) {
            const auto path = shard_file(dir, w, b);
            const auto bytes = fs::file_size(path);
            if (bytes == 0) continue;
            const auto offset = tags.size();
            tags.resize(offset + bytes / sizeof(Word));
            std::ifstream input(path, std::ios::binary);
            input.exceptions(std::ios::failbit | std::ios::badbit);
            input.read(reinterpret_cast<char *>(tags.data() + offset), bytes);
        }
        require(tags.size() == entries, "size mismatch");
        std::sort(tags.begin(), tags.end());
        for (std::size_t i = 0; i < tags.size(); ++i) {
            require((tags[i] >> 60) == b, "tag in wrong bucket");
            if (i && tags[i] == tags[i-1]) repeated.insert(tags[i]);
        }
        count += entries;
    }
    require(count == expected, "incomplete half-window");
    return repeated;
}

int main(int argc, char **argv) try {
    require(argc == 3 || argc == 4, "usage: phi first|second|positive-control NEW_DIRECTORY [workers]");
    const std::string name = argv[1];
    const Field f = sponsor_field(name);
    unsigned workers = argc == 4 ? std::stoul(argv[3]) : 4;
    require(workers >= 1 && workers <= 16 && workers <= f.n/2, "invalid worker count");
    require(power(f.g, f.n/2, f.p) == f.p-1 && power(f.g, f.n, f.p) == 1, "wrong order");
    const fs::path dir = argv[2];
    require(fs::create_directory(dir), "scratch directory must be new");
    std::vector<std::future<void>> tasks;
    for (unsigned w = 0; w < workers; ++w) {
        Word lo = 1 + f.n/2*w/workers, hi = 1 + f.n/2*(w+1)/workers;
        tasks.push_back(std::async(std::launch::async, emit, std::cref(f), std::cref(dir), w, lo, hi));
    }
    for (auto &task : tasks) task.get();
    const auto repeated = find_repeated(dir, workers, f.n/2);
    Word duplicates = 0;
    if (!repeated.empty()) {
        std::map<mpz_class, Word> seen;
        visit_range(f, 1, 1+f.n/2, [&](Word r, const mpz_class &phi) {
            if (!repeated.count(phi.get_ui())) return;
            auto [it, fresh] = seen.emplace(phi, r);
            if (!fresh) {
                std::cout << "collision r=" << it->second << " s=" << r << " phi=" << phi << '\n';
                ++duplicates;
            }
        });
    }
    std::cout << "field=" << name << " p=" << f.p << " g=" << f.g << " n=" << f.n
              << " checked=" << f.n/2 << " repeated_tags=" << repeated.size()
              << " image_size=" << f.n/2-duplicates << " injective=" << (duplicates ? "false":"true") << '\n';
    for (unsigned w = 0; w < workers; ++w)
        for (unsigned b = 0; b < buckets; ++b) fs::remove(shard_file(dir, w, b));
    fs::remove(dir);
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
