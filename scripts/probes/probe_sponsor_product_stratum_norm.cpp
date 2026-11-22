// Certify the operator norm on each product stratum from the packed Legendre row.
// Generate INPUT with probe_sponsor_paley_signs.cpp, then run FIELD INPUT B WORKERS.
// Use "controls" for independent direct computations of both block fourth moments.
#include "sponsor_phi_field.hpp"
#include <algorithm>
#include <array>
#include <atomic>
#include <fstream>
#include <future>
#include <iostream>
#include <set>
#include <vector>

using Signed = std::int64_t;
using Wide = __int128_t;
using Correlation = std::array<Signed, 2>;
using Moments = std::array<Wide, 2>;

int sign_at(const std::vector<Word> &bits, Word r) {
    return 1 - 2*int((bits[r/64] >> (r%64)) & 1);
}

// The repeated copy allows all four pointers to advance without wrapping.
Correlation correlation(const std::vector<Word> &bits, Word n, Word a, Word b) {
    const Word mask = n-1;
    Correlation sums{};
    if (a%64 || b%64 || n<64) {
        for (Word r=0; r<n; ++r) {
            Signed value=1;
            for (Word offset : {Word(0),a,b,a+b}) {
                const Word k=(r+offset)&mask;
                value *= k ? sign_at(bits,k) : 0;
            }
            sums[r%2] += value;
        }
        return sums;
    }
    constexpr Word even=0x5555555555555555ULL;
    Word neg_even=0, neg_odd=0;
    for (Word j=0; j<n/64; ++j) {
        const Word v=bits[j] ^ bits[j+a/64] ^ bits[j+b/64] ^ bits[j+(a+b)/64];
        neg_even += __builtin_popcountll(v & even);
        neg_odd += __builtin_popcountll(v & ~even);
    }
    sums = {Signed(n/2)-2*Signed(neg_even), Signed(n/2)-2*Signed(neg_odd)};
    // The packed sign at the identity is +1. Replace its contributions by zero,
    // including repeated offsets exactly once.
    for (Word r : std::set<Word>{0,(-a)&mask,(-b)&mask,(-a-b)&mask}) {
        Signed value=1;
        for (Word offset : {Word(0),a,b,a+b}) value *= sign_at(bits,(r+offset)&mask);
        sums[r%2] -= value;
    }
    return sums;
}

Moments aggregate(const std::vector<Word> &bits, Word n, Word block, unsigned workers) {
    const Word step=n/block;
    require(block>=2 && !(block & (block-1)) && n%block==0 && step%2==0, "invalid block");
    require(1<=workers && workers<=4, "expected one to four workers");
    struct Job { Word a,b,weight; };
    std::vector<Job> jobs;
    for (Word a=0; a<=block/2; ++a) for (Word b=a; b<=block/2; ++b) {
        const Word weight=(a && a<block/2 ? 2:1)*(b && b<block/2 ? 2:1)*(a==b ? 1:2);
        jobs.push_back({a*step,b*step,weight});
    }
    std::atomic<size_t> next{0};
    std::vector<std::future<Moments>> tasks;
    for (unsigned i=0; i<workers; ++i) {
        tasks.push_back(std::async(std::launch::async,[&] {
            Moments result{};
            for (;;) {
                const size_t j=next.fetch_add(1);
                if (j>=jobs.size()) break;
                const auto [a,b,w]=jobs[j];
                const auto [e,o]=correlation(bits,n,a,b);
                result[0] += 2*Wide(w)*(Wide(e)*e+Wide(o)*o);
                result[1] += 4*Wide(w)*e*o;
            }
            return result;
        }));
    }
    Moments sum{};
    for (auto &task:tasks) {
        const auto part=task.get();
        for (unsigned k=0; k<2; ++k) sum[k]+=part[k];
    }
    return sum;
}

mpz_class big(Wide x) {
    require(x>=0,"negative fourth moment");
    mpz_class z;
    mpz_import(z.get_mpz_t(),1,1,sizeof(x),0,0,&x);
    return z;
}

// Small-field control sums the squares of row scalar products in each literal
// field-character block, without the parity transform or four-point reduction.
Moments direct(const Field &field, Word block) {
    std::vector<mpz_class> powers(field.n,1);
    for (Word i=1;i<field.n;++i) powers[i]=powers[i-1]*field.g%field.p;
    Moments moments{};
    for (Word parity=0;parity<2;++parity) {
        std::vector<mpz_class> trace(field.n);
        for (Word i=0;i<field.n;++i) trace[i]=powers[i]+powers[(parity-i)&(field.n-1)];
        std::vector<int> entries(field.n*field.n);
        for (Word i=0;i<field.n;++i) for (Word j=0;j<field.n;++j) {
            mpz_class diff=trace[i]-trace[j];
            entries[i*field.n+j]=mpz_legendre(diff.get_mpz_t(),field.p.get_mpz_t());
        }
        const Word step=field.n/block;
        for (Word i=0;i<field.n;++i) for (Word k=i%step;k<field.n;k+=step)
            for (Word residue=0;residue<step;++residue) {
                Signed dot=0;
                for (Word j=residue;j<field.n;j+=step)
                    dot+=entries[i*field.n+j]*entries[k*field.n+j];
                moments[parity]+=dot*dot;
            }
    }
    return moments;
}

// Drop the diagonal of the block row Gram matrix before applying its
// Frobenius norm. For shift a=0 the four-point sums only count nonzero sites.
mpz_class norm_upper(const mpz_class &moment, Word n, Word block, unsigned parity) {
    const unsigned long step=n/block;
    const Wide half=n/2;
    auto diagonal=[&](Wide count) {
        return parity==0 ? 2*(count*count+half*half) : 4*count*half;
    };
    const mpz_class omitted=big(diagonal(half-1)+(block-1)*diagonal(half-2));
    require(moment>=omitted,"negative off-diagonal energy");
    const mpz_class base=mpz_class(step)*step*static_cast<unsigned long>(block);
    const mpz_class tail=(moment-omitted)*step*step;
    mpz_class root;
    if (!mpz_root(root.get_mpz_t(),tail.get_mpz_t(),2)) ++root;
    const mpz_class upper_sq=base+root;
    if (!mpz_root(root.get_mpz_t(),upper_sq.get_mpz_t(),2)) ++root;
    return root;
}

int main(int argc,char **argv) try {
    if (argc==2 && std::string(argv[1])=="controls") {
        for (const auto *name:{"positive-control","primitive-control","sextic-control","asymmetric-control"}) {
            const Field f=sponsor_field(name);
            const Word words=(f.n+63)/64;
            std::vector<Word> bits(2*words);
            for (Word r=0;r<f.n;++r) {
                mpz_class v=1-power(f.g,r,f.p);
                if (mpz_legendre(v.get_mpz_t(),f.p.get_mpz_t())<0) bits[r/64] |= Word(1)<<(r%64);
            }
            std::copy_n(bits.begin(),words,bits.begin()+words);
            for (Word block=2;block<=f.n/2;block*=2)
                require(aggregate(bits,f.n,block,1)==direct(f,block),"direct field matrix mismatch");
        }
        std::cout << "All four direct field controls passed.\n";
        return 0;
    }
    require(argc==5,"expected FIELD INPUT B WORKERS or controls");
    const auto f=sponsor_field(argv[1]);
    require(f.n==(1UL<<30),"requested field is not a prize prime");
    const Word block=std::stoul(argv[3]);
    const Word words=f.n/64;
    std::vector<Word> bits(2*words);
    std::ifstream file(argv[2],std::ios::binary);
    file.read(reinterpret_cast<char*>(bits.data()),words*sizeof(Word));
    require(bool(file) && file.peek()==EOF && !(bits[0]&1),"incorrect packed row");
    Word negatives=0;
    for (Word i=0;i<words;++i) negatives+=__builtin_popcountll(bits[i]);
    const Signed row=Signed(f.n-1)-2*Signed(negatives);
    require(row==(std::string(argv[1])=="first" ? -30929 : -1441),"wrong field row sum");
    std::copy_n(bits.begin(),words,bits.begin()+words);
    const Moments moments=aggregate(bits,f.n,block,std::stoul(argv[4]));
    for (unsigned parity=0;parity<2;++parity) {
        const mpz_class moment=big(moments[parity]);
        const mpz_class upper=norm_upper(moment,f.n,block,parity);
        std::cout << argv[1] << " block=" << block << " parity=" << parity
                  << " local_fourth_sum=" << moment << " lifted_norm_upper=" << upper << '\n';
    }
    return 0;
} catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
}
