// Exact cyclic correlations and ternary four-site rank counts for a sponsor domain.
#include "sponsor_phi_field.hpp"
#include <algorithm>
#include <atomic>
#include <cerrno>
#include <cstdio>
#include <fstream>
#include <future>
#include <iostream>
#include <memory>
#include <unistd.h>
#include <vector>

using Residue = std::uint32_t;
using Wide = __int128_t;
constexpr Word modulus = 3221225473;
constexpr Word max_order = Word{1} << 30;

Residue multiply(Residue a, Residue b) { return Word(a)*b % modulus; }
Residue add(Residue a, Residue b) {
    const Word v = Word(a)+b;
    return v >= modulus ? v-modulus : v;
}
Residue subtract(Residue a, Residue b) {
    return a >= b ? a-b : Word(a)+modulus-b;
}
Residue mod_power(Residue a, Word n) {
    Residue result=1;
    while (n) {
        if (n&1) result=multiply(result,a);
        a=multiply(a,a);
        n >>= 1;
    }
    return result;
}

Residue check_root() {
    for (Word d=2; d*d<=modulus; ++d)
        if (modulus%d==0) throw std::runtime_error("NTT modulus is composite");
    const Residue root=mod_power(5,3);
    require(mod_power(root,max_order/2)==modulus-1 && mod_power(root,max_order)==1,
            "incorrect order of primitive NTT root");
    return root;
}

struct Transform {
    const Word n;
    std::vector<Residue> roots, inverse_roots;
    const Residue scale;
    Transform(Word size, Residue generator) : n(size), roots(n), inverse_roots(n),
                                              scale(mod_power(n,modulus-2)) {
        for (Word half=1; half<n; half*=2) {
            const Residue w=mod_power(generator,max_order/(2*half));
            const Residue inv=mod_power(w,modulus-2);
            roots[half]=inverse_roots[half]=1;
            for (Word j=1; j<half; ++j) {
                roots[half+j]=multiply(roots[half+j-1],w);
                inverse_roots[half+j]=multiply(inverse_roots[half+j-1],inv);
            }
        }
    }
    // Decimation in frequency. Input is natural, output is bit-reversed.
    void forward(std::vector<Residue> &v) const {
        for (Word half=n/2; half; half/=2)
            for (Word base=0; base<n; base+=2*half)
                for (Word j=0; j<half; ++j) {
                    const auto a=v[base+j], b=v[base+half+j];
                    v[base+j]=add(a,b);
                    v[base+half+j]=multiply(subtract(a,b),roots[half+j]);
                }
    }
    // Decimation in time reverses precisely the preceding stage order.
    void inverse(std::vector<Residue> &v) const {
        for (Word half=1; half<n; half*=2)
            for (Word base=0; base<n; base+=2*half)
                for (Word j=0; j<half; ++j) {
                    const auto a=v[base+j], b=multiply(v[base+half+j],inverse_roots[half+j]);
                    v[base+j]=add(a,b);
                    v[base+half+j]=subtract(a,b);
                }
        for (auto &x : v) x=multiply(x,scale);
    }
};

void transfer(int fd, Residue *data, Word count, Word index, bool write) {
    auto *buf=reinterpret_cast<char*>(data);
    Word offset=index*sizeof(Residue), bytes=count*sizeof(Residue);
    while (bytes) {
        const auto done=write ? pwrite(fd,buf,bytes,offset) : pread(fd,buf,bytes,offset);
        if (done<0 && errno==EINTR) continue;
        if (done<=0) throw std::runtime_error("temporary NTT file I/O failed");
        buf+=done; offset+=done; bytes-=done;
    }
}

template<class Job>
void parallel(unsigned workers, Job job) {
    std::atomic<Word> next{0};
    std::vector<std::future<void>> tasks;
    for (unsigned i=0; i<workers; ++i)
        tasks.push_back(std::async(std::launch::async,[&,i]{job(next,i);}));
    for (auto &task : tasks) task.get();
}

int sign_at(const std::vector<Word> &bits, Word j) {
    return j==0 ? 0 : ((bits[j/64]>>(j%64))&1) ? -1 : 1;
}

// Independent cyclic rotation of the packed signs. Encoding the zero site as
// +1 introduces two terms at every nonzero offset, which are removed below.
std::int64_t bit_correlation(const std::vector<Word> &bits, Word n, Word h) {
    if (n<64) {
        std::int64_t sum=0;
        for (Word j=0; j<n; ++j) sum+=sign_at(bits,j)*sign_at(bits,(j+h)%n);
        return sum;
    }
    Word distance=0, shift=h%64;
    for (Word i=0; i<bits.size(); ++i) {
        Word pos=(i+h/64)%bits.size(), word=bits[pos];
        if (shift) word=(word>>shift) | (bits[(pos+1)%bits.size()]<<(64-shift));
        distance+=__builtin_popcountll(bits[i]^word);
    }
    return std::int64_t(n)-2*std::int64_t(distance)-sign_at(bits,h)-sign_at(bits,n-h);
}

std::int64_t centered(Residue x) {
    return std::int64_t(x)-(x>modulus/2 ? std::int64_t(modulus) : 0);
}

std::string decimal(Wide v) {
    if (v<0) return "-"+decimal(-v);
    if (!v) return "0";
    std::string s;
    while (v) { s+=char('0'+v%10); v/=10; }
    std::reverse(s.begin(),s.end());
    return s;
}

int main(int argc, char **argv) try {
    require(argc==5 || argc==6,"usage: rank_counts FIELD SIGN_FILE BLOCKS WORKERS [ORDER]");
    const auto field=sponsor_field(argv[1]);
    const Word n=argc==6 ? std::stoull(argv[5]) : field.n;
    const Word blocks=std::stoull(argv[3]);
    const Word requested_workers=std::stoull(argv[4]);
    require(n>=4 && n<=field.n && n<=max_order && !(n&(n-1)), "invalid domain order");
    require(blocks>=2 && blocks<=n/2 && !(blocks&(blocks-1)), "invalid row count");
    require(requested_workers>=1 && requested_workers<=3,"use one to three workers");
    const unsigned workers=requested_workers;
    const Word length=n/blocks;
    require(length<=(Word{1}<<20) && blocks<=2048, "unsupported factorization");
    const Residue generator=check_root(), omega=mod_power(generator,max_order/n);
    const auto g=power(field.g,field.n/n,field.p);
    require(field.p%4==1 && power(g,n/2,field.p)==field.p-1,"incorrect source generator order");
    const int gamma=mpz_legendre(g.get_mpz_t(),field.p.get_mpz_t());
    std::vector<Word> bits((n+63)/64);
    std::ifstream input(argv[2],std::ios::binary);
    input.read(reinterpret_cast<char*>(bits.data()),bits.size()*sizeof(Word));
    require(bool(input) && input.peek()==EOF && !(bits[0]&1), "invalid sign file");
    if (n<64) require((bits[0]>>n)==0,"nonzero sign padding");
    std::int64_t row_sum=n-1;
    for (const auto word : bits) row_sum-=2*__builtin_popcountll(word);
    for (Word j=1; j<n/2; ++j)
        if (sign_at(bits,n-j)!=((j&1) ? gamma : 1)*sign_at(bits,j))
            throw std::runtime_error("input reversal mismatch");
    std::map<Word,std::int64_t> samples;
    for (Word h : {Word{1},Word{2},Word{63},Word{64},Word{65},n/7,n/2-1,n/2})
        if (h && h<n) samples[h]=bit_correlation(bits,n,h);
    std::unique_ptr<FILE,decltype(&fclose)> temp(tmpfile(),fclose);
    require(bool(temp),"cannot create temporary file");
    int fd=fileno(temp.get());
    const Transform long_fft(length,generator), short_fft(blocks,generator);
    parallel(workers,[&](auto &next,unsigned) {
        std::vector<Residue> row(length);
        for (Word r; (r=next.fetch_add(1))<blocks;) {
            for (Word j=0; j<length; ++j) {
                int sign=sign_at(bits,r+j*blocks);
                row[j]=sign<0 ? modulus-1 : sign;
            }
            long_fft.forward(row);
            transfer(fd,row.data(),length,r*length,true);
        }
    });
    std::vector<Word>().swap(bits);
    const Word tile_size=std::min(Word{4096},length);
    std::vector<Word> reversed(length);
    for (Word i=1; i<length; ++i) reversed[i]=reversed[i/2]/2+(i%2)*(length/2);
    const Residue inv_omega=mod_power(omega,modulus-2);
    parallel(workers,[&](auto &next,unsigned) {
        std::vector<Residue> tile(blocks*tile_size), column(blocks);
        for (Word base; (base=next.fetch_add(tile_size))<length;) {
            for (Word r=0; r<blocks; ++r)
                transfer(fd,&tile[r*tile_size],tile_size,r*length+base,false);
            for (Word i=0; i<tile_size; ++i) {
                const Word k=reversed[base+i];
                const auto w=mod_power(omega,k), iw=mod_power(inv_omega,k);
                Residue phase=1;
                for (Word r=0; r<blocks; ++r) {
                    column[r]=multiply(tile[r*tile_size+i],phase);
                    phase=multiply(phase,w);
                }
                short_fft.forward(column);
                if (k==0)
                    require(column[0]==(std::int64_t(modulus)+row_sum)%modulus,"frequency zero mismatch");
                if (gamma==1) {
                    for (auto &v : column) v=multiply(v,v);
                } else {
                    // f+n/2 toggles the top bit of the natural short frequency.
                    // In bit-reversed order this pairs adjacent entries.
                    for (Word j=0; j<blocks; j+=2) {
                        const auto joint=multiply(column[j],column[j+1]);
                        column[j]=column[j+1]=joint;
                    }
                }
                short_fft.inverse(column);
                phase=1;
                for (Word r=0; r<blocks; ++r) {
                    tile[r*tile_size+i]=multiply(column[r],phase);
                    phase=multiply(phase,iw);
                }
            }
            for (Word r=0; r<blocks; ++r)
                transfer(fd,&tile[r*tile_size],tile_size,r*length+base,true);
        }
    });
    struct Stats { Wide sum=0, squares=0; std::int64_t absolute_peak=0; };
    std::vector<Stats> stats(workers);
    std::vector<std::int64_t> control(n<=1024 ? n : 0);
    parallel(workers,[&](auto &next,unsigned worker) {
        std::vector<Residue> row(length);
        auto &s=stats[worker];
        for (Word r; (r=next.fetch_add(1))<blocks;) {
            transfer(fd,row.data(),length,r*length,false);
            long_fft.inverse(row);
            for (Word j=0; j<length; ++j) {
                const Word h=r+j*blocks;
                const auto v=centered(row[j]);
                if (h==0) require(v==std::int64_t(n-1),"zero correlation mismatch");
                else if (std::abs(v)>std::int64_t(n-2) || v%2 || (gamma==-1 && (h&1) && v!=0))
                    throw std::runtime_error("invalid centered correlation");
                if (h) s.absolute_peak=std::max(s.absolute_peak,std::abs(v));
                s.sum+=v; s.squares+=Wide(v)*v;
                if (!control.empty()) control[h]=v;
            }
            for (const auto &[h,expected] : samples)
                if (h%blocks==r) require(centered(row[h/blocks])==expected,
                                          "packed rotate/popcount correlation mismatch");
        }
    });
    Stats total;
    for (const auto &s : stats) {
        total.sum+=s.sum; total.squares+=s.squares;
        total.absolute_peak=std::max(total.absolute_peak,s.absolute_peak);
    }
    require(total.sum==Wide(row_sum)*row_sum,"sum of correlations mismatch");
    const Wide m=n, energy=m*total.squares;
    const Wide four=m*(m-1)*(m-2)*(m-3)/24;
    const Wide numerator=energy-m*(m-1)*(2*m-3)+8*four;
    require(numerator>=0 && numerator%32==0 && numerator/32<=four,"invalid minor count");
    if (n==max_order) {
        const Wide norm=std::string(argv[1])=="first" ? 197063 : 146018;
        require(energy<=m*(m-1)*norm*norm,"independent certified spectral upper bound failed");
    }
    std::cout<<"field="<<argv[1]<<" n="<<n<<" gamma="<<gamma<<" row_sum="<<row_sum
             <<" sum_correlations="<<decimal(total.sum)<<" sum_squares="<<decimal(total.squares)
             <<" max_offdiag="<<total.absolute_peak<<" energy="<<decimal(energy)
             <<" singular="<<decimal(numerator/32)<<" four_subsets="<<decimal(four)<<'\n';
    if (control.empty()) {
        std::cout<<"popcount";
        for (const auto &[h,v] : samples) std::cout<<" "<<h<<"="<<v;
        std::cout<<'\n';
    }
    for (Word h=0; h<control.size(); ++h) std::cout<<h<<' '<<control[h]<<'\n';
    return 0;
} catch (const std::exception &e) { std::cerr<<e.what()<<'\n'; return 1; }
