// wf-G1: MAXIMALLY-ROUGH targeted disprove. Find primes p=1 mod n near beta with m=(p-1)/n = 2^k * q,
// q a SINGLE large prime (the extreme of K2's "rough = worst" observation), and measure exact C.
// This gives the disproof its strongest shot: the most arithmetically structured / least-cancelling cosets.
// usage: wf9G1_maxrough <n> <num_targets> <nthreads> [beta]
use std::f64::consts::PI;
use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}if n%3==0{return n==3}let mut d=5;while d*d<=n{if n%d==0{return false}if n%(d+2)==0{return false}d+=6}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
// odd part: returns (odd, v2)
fn oddpart(x:u64)->(u64,u32){let v=v2(x); (x>>v, v)}
fn truemax(n:u64,p:u64,nth:usize)->f64{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p); let mu=Arc::new(mu);
    let chunk=(m+nth as u64-1)/nth as u64; let mut hs=vec![];
    for t in 0..nth as u64{
        let lo=t*chunk; let hi=((t+1)*chunk).min(m); if lo>=hi{continue;}
        let mu=Arc::clone(&mu);
        hs.push(thread::spawn(move||{
            let mut mx=0.0f64; let pp=p as u128; let inv=2.0*PI/p as f64; let mut b=mpow(gn,lo,p);
            for _ in lo..hi{ let mut re=0.0f64; let mut im=0.0f64;
                for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64; let a=inv*(tt as f64); re+=a.cos(); im+=a.sin();}
                let mg=re*re+im*im; if mg>mx{mx=mg;} b=((b as u128*gn as u128)%pp)as u64; } mx
        }));
    }
    let mut best=0.0f64; for hh in hs{let mx=hh.join().unwrap(); if mx>best{best=mx;}} best.sqrt()
}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:u64=a[1].parse().unwrap();
    let num:usize=if a.len()>2{a[2].parse().unwrap()}else{8};
    let nth:usize=if a.len()>3{a[3].parse().unwrap()}else{8};
    let beta:f64=if a.len()>4{a[4].parse().unwrap()}else{4.0};
    let lo=(n as f64).powf(beta) as u64;
    println!("# MAXROUGH n p m oddpart_largepf C truemax (m=2^k*q, q prime)");
    let mut p = lo - (lo%n) + 1; if p<lo{p+=n;}
    let mut found=0; let mut worstc=0.0f64; let mut worstp=0u64;
    while found<num {
        if isp(p){
            let m=(p-1)/n; let (odd,_v)=oddpart(m);
            // maximally rough: odd part is a single prime (or 1)
            if odd==1 || isp(odd) {
                let tm=truemax(n,p,nth);
                let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
                let c=tm/prize;
                println!("{} {} {} {} {:.5} {:.3}",n,p,m,odd,c,tm);
                if c>worstc{worstc=c;worstp=p;}
                found+=1;
            }
        }
        p+=n;
        if p > lo*4 {break;} // give up the window
    }
    println!("WORST_MAXROUGH n={} C={:.5} p={}",n,worstc,worstp);
}
