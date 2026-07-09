// wf-G1 (disprove lane, issue #444): worst-case C(n) = max_{rough primes p~n^4} M(n)/sqrt(n*ln(p/n)),
// pushed to large n with a GROWTH FIT.  M(n)=max_{b!=0}|sum_{x in mu_n} e_p(bx)| measured EXACTLY
// (no moments), parallel over cosets.  Per n: scan many primes p=1 mod n near beta~4, classify each by
// ROUGHNESS = largest prime factor of m=(p-1)/n (K2 found rough = worst), report WORST C and the
// worst prime's structure.  Bounded -> prize TRUE; growing (log n / n^c) -> prize FALSE.
//
// usage: wf9G1 <n> <num_primes> <nthreads> [beta]
//   prints one line per prime (n p m roughness v2 C truemax) then the WORST summary line "WORST ...".
use std::f64::consts::PI;
use std::thread; use std::sync::{Arc,Mutex};
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}if n%3==0{return n==3}let mut d=5;while d*d<=n{if n%d==0{return false}if n%(d+2)==0{return false}d+=6}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
// largest prime factor of x (trial division, ok for m ~ n^4/n = n^3 .. fine up to ~1e9; for bigger use rho-lite)
fn largest_pf(mut x:u64)->u64{
    let mut best=1u64;
    while x%2==0{x/=2; best=best.max(2);}
    let mut d=3u64;
    while d*d<=x{ while x%d==0{x/=d; best=best.max(d);} d+=2; }
    if x>1{best=best.max(x);}
    best
}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// exact truemax = max_{b!=0} |eta_b|, parallel over the m cosets.
fn truemax(n:u64,p:u64,nth:usize)->f64{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p); let mu=Arc::new(mu);
    let chunk=(m+nth as u64-1)/nth as u64; let mut hs=vec![];
    for t in 0..nth as u64{
        let lo=t*chunk; let hi=((t+1)*chunk).min(m); if lo>=hi{continue;}
        let mu=Arc::clone(&mu);
        hs.push(thread::spawn(move||{
            let mut mx=0.0f64; let pp=p as u128; let inv=2.0*PI/p as f64;
            let mut b=mpow(gn,lo,p);
            for _ in lo..hi{
                let mut re=0.0f64; let mut im=0.0f64;
                for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64; let a=inv*(tt as f64); re+=a.cos(); im+=a.sin();}
                let mag2=re*re+im*im; if mag2>mx{mx=mag2;}
                b=((b as u128*gn as u128)%pp)as u64;
            }
            mx
        }));
    }
    let mut best=0.0f64; for hh in hs{let mx=hh.join().unwrap(); if mx>best{best=mx;}}
    best.sqrt()
}

fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:u64=a[1].parse().unwrap();
    let num:usize=if a.len()>2{a[2].parse().unwrap()}else{50};
    let nth:usize=if a.len()>3{a[3].parse().unwrap()}else{8};
    let beta:f64=if a.len()>4{a[4].parse().unwrap()}else{4.0};
    let lo=(n as f64).powf(beta) as u64;
    // collect num primes p=1 mod n at/above n^beta
    let mut primes=vec![]; let mut p = lo - (lo%n) + 1; if p<lo{p+=n;}
    while primes.len()<num { if isp(p){primes.push(p);} p+=n; if p< n {break;} }
    // for each prime: roughness (largest prime factor of m), v2(p-1). Stratify; report worst C.
    println!("# n p m roughness v2 C truemax beta_actual");
    let worst=Arc::new(Mutex::new((0.0f64,0u64,0u64,0u32))); // C,p,rough,v2
    let worst_rough=Arc::new(Mutex::new((0.0f64,0u64,0u64))); // among roughest 25%: C,p,rough
    // precompute roughness for all, sort to find rough threshold
    let mut info:Vec<(u64,u64,u32)>=primes.iter().map(|&p|{let m=(p-1)/n; (p,largest_pf(m),v2(p-1))}).collect();
    let mut roughs:Vec<u64>=info.iter().map(|x|x.1).collect(); roughs.sort();
    let rough_thresh = roughs[roughs.len()*3/4];
    for (p,rough,vv) in info.drain(..){
        let m=(p-1)/n;
        let tm=truemax(n,p,nth);
        let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
        let c=tm/prize;
        let ba=(p as f64).ln()/(n as f64).ln();
        println!("{} {} {} {} {} {:.5} {:.3} {:.3}",n,p,m,rough,vv,c,tm,ba);
        {let mut w=worst.lock().unwrap(); if c>w.0{*w=(c,p,rough,vv);}}
        if rough>=rough_thresh {let mut w=worst_rough.lock().unwrap(); if c>w.0{*w=(c,p,rough);}}
    }
    let w=worst.lock().unwrap(); let wr=worst_rough.lock().unwrap();
    println!("WORST n={} C={:.5} p={} rough={} v2={} | WORST_ROUGH C={:.5} p={} rough={}",
        n,w.0,w.1,w.2,w.3, wr.0,wr.1,wr.2);
}
