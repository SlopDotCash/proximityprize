"""
C054 attack: the sqrt|V| 'union tax' bracket for the Shaw operator.

Claim (C054): max_{s0} ||Shaw(S;s0,s1)||^2 lies in [M, |V|*M], a multiplicative
gap of EXACTLY sqrt|V| = q^{n/2}, and this is W-Johnson relocated to base-point space.

Shaw(S;s0,s1) = sum_{psi perp s1, psi != 0} psi(s0) * b(psi),  b(psi)=sum_{s in S} psi(-s)
M = sum_{psi perp s1, psi != 0} |b(psi)|^2

KEY structural fact to test:
  - psi perp s1  <=>  psi factors through V/<s1>.  So Shaw(s0) depends only on s0 mod <s1>.
  - Hence there are only |V|/|<s1>| = |V|/|F| EFFECTIVE base points (assuming s1 != 0).
  - Plancherel on the quotient group V/<s1>:  sum over effective s0 of |Shaw|^2 = (|V|/|F|)*M.
  - => average over EFFECTIVE base points of |Shaw|^2 = M / |perp-set fraction|... let's just measure.

We measure the TRUE gap  max|Shaw|^2 / M  and compare it to:
  - the claimed upper bound |V|  (the 'sqrt|V| tax' squared)
  - the EFFECTIVE-basepoint upper bound  (|V|/|F|)  [Plancherel on quotient]
  - the actual realized max/avg ratio.

We work on a literal F-module V = F_q^m, exact arithmetic via complex roots of unity
on the additive characters of (Z/p)^m... but additive chars of F_q^m for q=p prime
are products of e_p over coordinates. Use V = (Z/q)^m as additive group (q prime).
"""
import cmath, math, itertools

def primitive_chars_Zq(q):
    # additive characters of Z/q: psi_a(x) = exp(2pi i a x / q), a in 0..q-1
    return list(range(q))

def run(q, m, S_gen, s1, label):
    # V = (Z/q)^m additive group. Field F = Z/q acts; line F*s1 = {gamma*s1 : gamma in Z/q}.
    # additive chars psi_a for a in (Z/q)^m: psi_a(x) = exp(2pi i <a,x>/q)
    p = q
    w = lambda t: cmath.exp(2j*math.pi*(t % p)/p)
    def inner(a,x): return sum(ai*xi for ai,xi in zip(a,x)) % p
    # the set S
    S = S_gen
    # all chars
    allcoords = list(itertools.product(range(p), repeat=m))
    # which psi are perp to s1 and nonzero:  psi_a(gamma*s1)=1 for all gamma  <=> <a,s1>=0 mod p
    perp = [a for a in allcoords if (sum(ai*si for ai,si in zip(a,s1)) % p)==0 and any(a)]
    # b(psi_a) = sum_{s in S} psi_a(-s)
    b = {a: sum(w(-inner(a,s)) for s in S) for a in perp}
    M = sum(abs(b[a])**2 for a in perp)
    # Shaw(s0) = sum_{a in perp} psi_a(s0)*b(a)
    vals = {}
    for s0 in allcoords:
        sh = sum(w(inner(a,s0))*b[a] for a in perp)
        vals[s0] = abs(sh)**2
    maxv = max(vals.values())
    # base points are V (size p^m); effective = V/<s1>
    Vsize = p**m
    # <s1> size = order of s1 in additive group = p/gcd... it's p (if s1!=0) times? line F*s1 has p elements if s1!=0
    line = set(tuple((g*si)%p for si in s1) for g in range(p))
    lineSize = len(line)
    # effective basepoints = Vsize/lineSize
    eff = Vsize//lineSize
    avg_over_all = sum(vals.values())/Vsize          # = M (Plancherel full V): check
    avg_over_eff = M/eff if eff else 0               # quotient-Plancherel average
    print(f"== {label}: q={q} m={m} |V|={Vsize} |S|={len(S)} |perp|={len(perp)} lineSize={lineSize} eff_bp={eff}")
    print(f"   M = {M:.4f}   avg_all = {avg_over_all:.4f} (should = M: {abs(avg_over_all-M)<1e-6})")
    print(f"   max|Shaw|^2 = {maxv:.4f}")
    print(f"   TRUE gap max/M           = {maxv/M:.4f}   (claimed upper |V|={Vsize})")
    print(f"   eff-Plancherel max/avg   = {maxv/avg_over_eff:.4f} (eff-upper bound = eff_bp = {eff})")
    print(f"   ratio  max / (sqrt(|V|*M))^2-style: max/(|V|*M)={maxv/(Vsize*M):.6f}  (=1 would saturate tax)")
    # structure test: is argmax s0 in a low-dim coset? count how many s0 achieve >= 0.9*max
    near = [s0 for s0,v in vals.items() if v >= 0.5*maxv]
    print(f"   #{{s0 : |Shaw|^2 >= 0.5 max}} = {len(near)} of {Vsize}")
    return maxv, M, Vsize, eff

# Small literal RS-flavored module instances. m up to 3, q small prime.
# S = a 'ball'-like set; use a structured low-weight set to mimic delta-ball.
if __name__=="__main__":
    # q=5, m=2: V=F_5^2.  S = low-weight words (Hamming weight <=1)
    q=5; m=2
    S=[ (a,b) for a in range(q) for b in range(q) if (a!=0)+(b!=0) <= 1 ]  # weight<=1 ball
    run(q,m,S,(1,0),"F5^2 wt<=1, s1=(1,0)")
    run(q,m,S,(1,2),"F5^2 wt<=1, s1=(1,2) [generic dir]")
    print()
    q=7; m=2
    S=[ (a,b) for a in range(q) for b in range(q) if (a!=0)+(b!=0) <= 1 ]
    run(q,m,S,(1,3),"F7^2 wt<=1, s1=(1,3)")
    print()
    q=5; m=3
    S=[ t for t in itertools.product(range(q),repeat=3) if sum(1 for x in t if x!=0) <= 1 ]
    run(q,m,S,(1,2,3),"F5^3 wt<=1, s1=(1,2,3)")
    run(q,m,S,(0,1,2),"F5^3 wt<=1, s1=(0,1,2)")
