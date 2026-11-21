// Certified full Fourier transform of a Paley row, with disk-backed intermediate rows.
// Usage: full FIELD SIGN_FILE BLOCKS WORKERS [ORDER]. See paley-production-spectrum.md.
#include "sponsor_paley_fft.hpp"
#include <atomic>
#include <cerrno>
#include <cstdio>
#include <fstream>
#include <future>
#include <iostream>
#include <memory>
#include <unistd.h>

constexpr Integer pack_scale = 1024;
struct Packed { std::int32_t re, im; };
static_assert(sizeof(Packed) == 8);

void transfer(int fd, void *data, std::size_t size, Word offset, bool write) {
    auto *p = static_cast<char*>(data);
    while (size) {
        const auto done = write ? pwrite(fd, p, size, offset) : pread(fd, p, size, offset);
        if (done < 0 && errno == EINTR) continue;
        require(done > 0, write ? "temporary file write failed" : "temporary file read failed");
        p += done;
        offset += done;
        size -= done;
    }
}

// A product of at most 30 certified binary anchors has Euclidean error <=210/T.
// A further product of two such numbers has error <=424/T, T=root_scale.
Pair binary_phase(Word j, unsigned depth, const std::vector<Pair> &anchors, Integer scale) {
    Pair z{scale, 0};
    for (unsigned bit = 0; bit < depth; ++bit) {
        if (!(j & (Word{1} << bit))) continue;
        if (bit + 1 == depth) z = {-z.re,-z.im};
        else z = scaled_rotate(z,anchors[depth-1-bit],scale);
    }
    return z;
}

class Phases {
    Word n, low_size;
    std::vector<Pair> low, high;
public:
    explicit Phases(Word order) : n(order), low_size(std::min(order, Word{1} << 15)),
        low(low_size), high(n/low_size) {
        const auto anchors = stage_anchors(n);
        const unsigned depth = __builtin_ctzll(n);
        for (Word j=0; j<low.size(); ++j) low[j]=binary_phase(j,depth,anchors,root_scale);
        for (Word j=0; j<high.size(); ++j) high[j]=binary_phase(j*low_size,depth,anchors,root_scale);
    }
    Pair at(Word j) const {
        j &= n-1;
        return rotate(high[j/low_size], low[j % low_size]);
    }
};

Integer sign_at(const std::vector<Word> &bits, Word j) {
    return j == 0 ? 0 : 1-2*Integer((bits[j/64] >> (j%64)) & 1);
}

// The row reversal is exact on the input. Check it independently before using
// conjugation to omit the second half of the residue classes.
Integer check_input(const std::vector<Word> &bits, Word n, int gen_sign) {
    require(!(bits[0] & 1), "identity bit must be zero");
    Word negatives = 0;
    for (Word word : bits) negatives += __builtin_popcountll(word);
    for (Word j = 1; j < n/2; ++j)
        require(sign_at(bits, n-j) == ((j&1) ? gen_sign : 1)*sign_at(bits,j),
                "incorrect reflection");
    return Integer(n-1)-2*Integer(negatives);
}

void write_rows(int fd, const std::vector<Word> &bits, Word n, Word blocks, unsigned workers) {
    const Word length = n/blocks, frequencies = length/2+1;
    const auto roots = make_roots(length);
    std::atomic<Word> next{0};
    std::vector<std::future<void>> tasks;
    for (unsigned t = 0; t < workers; ++t) tasks.push_back(std::async(std::launch::async, [&]() {
        std::vector<Pair> v(length);
        std::vector<Packed> row(frequencies);
        for (Word r; (r = next.fetch_add(1)) <= blocks/2;) {
            Integer dc = 0, alt = 0;
            for (Word j = 0; j < length; ++j) {
                const Integer s = sign_at(bits, r+j*blocks);
                v[j] = {s*data_scale, 0};
                dc += s;
                alt += (j & 1) ? -s : s;
            }
            transform(v, roots);
            require(v[0].re == dc*data_scale && !v[0].im &&
                    v[length/2].re == alt*data_scale && !v[length/2].im, "DC/Nyquist mismatch");
            for (Word k = 0; k < frequencies; ++k) {
                const Integer re = v[k].re/(data_scale/pack_scale);
                const Integer im = v[k].im/(data_scale/pack_scale);
                require(INT32_MIN <= re && re <= INT32_MAX && INT32_MIN <= im && im <= INT32_MAX,
                        "packed frequency overflow");
                row[k] = {static_cast<std::int32_t>(re), static_cast<std::int32_t>(im)};
            }
            transfer(fd,row.data(),frequencies*sizeof(Packed),r*frequencies*sizeof(Packed),true);
        }
    }));
    for (auto &task : tasks) task.get();
}

struct Peak { Word upper_ceil, frequency; };

class Peaks {
    static constexpr unsigned capacity=16;
public:
    std::vector<Peak> values;
    void add(Peak peak) {
        auto better = [](Peak a, Peak b) {
            if (a.upper_ceil != b.upper_ceil) return a.upper_ceil > b.upper_ceil;
            return a.frequency < b.frequency;
        };
        if (values.size() == capacity && !better(peak,values.back())) return;
        values.insert(std::lower_bound(values.begin(),values.end(),peak,better),peak);
        if (values.size() > capacity) values.pop_back();
    }
};

Peaks finish(int fd, Word n, Word blocks, int gen_sign, unsigned workers,
            Integer row_sum, std::vector<Pair> &small_result) {
    const Word length = n/blocks, frequencies = length/2+1, rows = blocks/2+1;
    const Word tile_size = std::min(frequencies, Word{2048});
    const auto roots = make_roots(blocks);
    const Phases phases(n);
    std::atomic<Word> next{0};
    std::vector<std::future<Peaks>> tasks;
    for (unsigned t=0; t<workers; ++t) tasks.push_back(std::async(std::launch::async, [&]() {
        std::vector<Packed> tile(rows*tile_size);
        std::vector<Pair> v(blocks);
        Peaks peaks;
        for (Word base; (base = next.fetch_add(tile_size)) < frequencies;) {
            const Word count = std::min(tile_size,frequencies-base);
            for (Word r=0; r<rows; ++r)
                transfer(fd, &tile[r*tile_size], count*sizeof(Packed), (r*frequencies+base)*sizeof(Packed), false);
            for (Word i=0; i<count; ++i) {
                const Word k = base+i;
                for (Word r=0; r<rows; ++r) {
                    const Packed z = tile[r*tile_size+i];
                    const Pair b{Integer(z.re)*(data_scale/pack_scale), Integer(z.im)*(data_scale/pack_scale)};
                    v[r] = rotate(b,phases.at(k*r));
                    if (r && 2*r != blocks) {
                        const int s = (r & 1) ? gen_sign : 1;
                        v[blocks-r] = {s*v[r].re, -s*v[r].im};
                    }
                }
                transform(v, roots);
                if (!k) require(v[0].re == row_sum*data_scale && !v[0].im, "final DC mismatch");
                for (Word m=0; m<blocks; ++m) {
                    const Word j = k+m*length;
                    peaks.add({magnitude_ceil(v[m]),j});
                    if (!small_result.empty()) {
                        small_result[j] = v[m];
                        if (k && 2*k != length) small_result[n-j] = {v[m].re,-v[m].im};
                    }
                }
            }
        }
        return peaks;
    }));
    Peaks peaks;
    for (auto &task : tasks) for (auto item : task.get().values) peaks.add(item);
    return peaks;
}

// For both FFTs the normalized error per stage increases by <=210/T + 1/S.
// Packing adds <2/P. Multiplication by the certified twiddle contributes at
// most 2*length*424/T + 2/S; all errors at that level propagate by <=blocks
// in the combined bound. See the proof in the accompanying note.
Word error_bound(Word n, Word blocks) {
    const Word stages=__builtin_ctzll(n), T=root_scale, S=data_scale, P=pack_scale;
    const Word numerator=n*stages*(210+T/S)+2*blocks*(T/P)+848*n+2*blocks*(T/S);
    return (numerator+T-1)/T;
}

mpz_class from_wide(Wide t) {
    const auto u=static_cast<__uint128_t>(t < 0 ? -t : t);
    mpz_class value=mpz_class(static_cast<unsigned long>(u >> 64)) << 64;
    value+=static_cast<unsigned long>(u);
    return t < 0 ? -value : value;
}

// Direct fixed-point enclosures of selected frequencies, using 52 fraction bits.
// Sum a block using precomputed fine roots and rotate its sum once by the coarse root.
std::pair<Word,Word> direct_interval(const std::vector<Word> &bits, Word n, Word k) {
    constexpr long scale=1L<<52;
    const Word chunk=std::min(n,Word{1}<<15);
    const unsigned depth=__builtin_ctzll(n);
    const auto anchors=stage_anchors(n,scale);
    std::vector<Pair> fine(chunk);
    for (Word j=0; j<chunk; ++j) fine[j]=binary_phase((j*k)&(n-1),depth,anchors,scale);
    Wide result_re=0, result_im=0;
    for (Word j=0; j<n; j+=chunk) {
        Wide re=0, im=0;
        for (Word r=0; r<chunk; ++r) {
            const auto sign=sign_at(bits,j+r);
            re+=sign*fine[r].re; im+=sign*fine[r].im;
        }
        const auto w=binary_phase((j*k)&(n-1),depth,anchors,scale);
        result_re+=(re*w.re-im*w.im)/scale;
        result_im+=(re*w.im+im*w.re)/scale;
    }
    const auto re=from_wide(result_re), im=from_wide(result_im);
    const auto mag=floor_sqrt(re*re+im*im);
    const mpz_class margin=static_cast<unsigned long>(422*n);
    const mpz_class lower=(mag-margin)/scale;
    const mpz_class upper=(mag+1+margin+scale-1)/scale;
    return {lower<0 ? 0UL : lower.get_ui(),upper.get_ui()};
}

int main(int argc, char **argv) try {
    require(argc == 5 || argc == 6,"usage: full FIELD SIGN_FILE BLOCKS WORKERS [ORDER]");
    Field field=sponsor_field(argv[1]);
    const Word n=argc == 6 ? std::stoull(argv[5]) : field.n;
    const Word blocks=std::stoull(argv[3]);
    const unsigned workers=std::stoul(argv[4]);
    require(n >= 4 && n <= field.n && !(n & (n-1)) && field.n % n == 0, "invalid order");
    require(blocks >= 2 && blocks <= n/2 && !(blocks & (blocks-1)), "invalid blocks");
    require(workers >= 1 && workers <= 4, "invalid workers");
    const Word length=n/blocks;
    require(length <= (Word{1}<<20) && blocks <= 2048, "unsupported FFT geometry");
    const auto g=power(field.g,field.n/n,field.p);
    require(field.p%4 == 1 && power(g,n/2,field.p) == field.p-1, "wrong generator");
    const int gen_sign=mpz_legendre(g.get_mpz_t(),field.p.get_mpz_t());
    std::vector<Word> bits((n+63)/64);
    std::ifstream f(argv[2],std::ios::binary);
    f.read(reinterpret_cast<char*>(bits.data()),sizeof(Word)*bits.size());
    require(bool(f) && f.peek()==EOF, "incorrect sign file size");
    const Integer row_sum=check_input(bits,n,gen_sign);
    std::unique_ptr<FILE,decltype(&fclose)> temp(tmpfile(),fclose);
    require(bool(temp),"failed to create temporary file");
    write_rows(fileno(temp.get()),bits,n,blocks,workers);
    std::vector<Pair> small_result(n <= 1024 ? n : 0);
    const Peaks peaks=finish(fileno(temp.get()),n,blocks,gen_sign,workers,row_sum,small_result);
    const Word error=error_bound(n,blocks);
    const Peak peak=peaks.values.front();
    const Word coarse_lower=peak.upper_ceil > error+1 ? peak.upper_ceil-error-1 : 0;
    Word lower=coarse_lower, upper=0, refined=0, other_upper=0;
    const Word sampled=blocks*(length/2+1);
    if (peaks.values.size()<sampled) other_upper=peaks.values.back().upper_ceil+error;
    for (const auto &candidate : peaks.values) {
        if (candidate.upper_ceil+error < lower) {
            other_upper=std::max(other_upper,candidate.upper_ceil+error);
            continue;
        }
        const auto interval=direct_interval(bits,n,candidate.frequency);
        lower=std::max(lower,interval.first);
        upper=std::max(upper,interval.second);
        ++refined;
    }
    upper=std::max(upper,other_upper);
    std::cout<<"field="<<argv[1]<<" n="<<n<<" blocks="<<blocks<<" row_sum="<<row_sum
             <<" approx_peak_ceil="<<peak.upper_ceil<<" frequency="<<peak.frequency<<" error="<<error
             <<" refined="<<refined<<" other_upper="<<other_upper<<" lower="<<lower<<" upper="<<upper<<'\n';
    for (Word j=0; j<small_result.size(); ++j)
        std::cout<<j<<" "<<small_result[j].re<<" "<<small_result[j].im<<'\n';
    return 0;
} catch (const std::exception &e) {
    std::cerr<<e.what()<<'\n'; return 1;
}
