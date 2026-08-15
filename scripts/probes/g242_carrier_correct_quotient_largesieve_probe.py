# G242 probe: verify the CARRIER-CORRECT fiber large-sieve for the quotient-Jacobi object.
# Fable G241 showed G240's l2_mass_floor_of_quotient_fibers has a carrier bug: fiber map is over G
# (where cls collapses to trivial class) but hInputParseval demands n*m*||a||^2 (which lives on Fp^*).
# The honest fix: run the fiber map x -> class(2-x) over the CARRIER Fp^* (size n*m).
# Verify: (1) fiber ceiling <= n on Fp^*, (2) input Parseval sum_{x in Fp^*} |F_a(x)|^2 = n*m*||a||^2,
#         (3) output/class energy chain gives outputEnergy <= n^2 ||a||^2 with the CORRECT carrier.
import cmath, math, random

def is_prime(p):
    if p < 2: return False
    for q in range(2, int(p**0.5)+1):
        if p % q == 0: return False
    return True

def primitive_root(p):
    # find generator of F_p^*
    fac = []
    phi = p-1
    d = phi
    q = 2
    while q*q <= d:
        if d % q == 0:
            fac.append(q)
            while d % q == 0: d //= q
        q += 1
    if d > 1: fac.append(d)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in fac):
            return g
    return None

def test_cell(p, n):
    # G = unique subgroup of order n in F_p^*; m = (p-1)/n
    assert (p-1) % n == 0
    m = (p-1)//n
    g = primitive_root(p)
    # G = <g^m>, elements g^(m*k) for k in 0..n-1
    G = sorted({pow(g, (m*k) % (p-1), p) for k in range(n)})
    assert len(G) == n
    # quotient class map: x in F_p^* -> coset x*G, label by min dlog mod m
    # dlog table
    dlog = {}
    cur = 1
    for e in range(p-1):
        dlog[cur] = e
        cur = (cur*g) % p
    def cls(x):
        # class of x in F_p^*/G  == dlog(x) mod m
        return dlog[x] % m
    Fpstar = list(range(1, p))
    # (1) fiber ceiling of the map x -> cls(2-x) over Fp^*  (2-x must be nonzero, i.e. x != 2)
    #     Also 2-x ranges over field; exclude x where 2-x==0 (x==2) and x==0 (not in Fp^*).
    from collections import defaultdict
    fibers = defaultdict(int)
    for x in Fpstar:
        y = (2 - x) % p
        if y == 0:  # 2-x = 0, no quotient class; skip (measure-zero, a single x)
            continue
        fibers[cls(y)] += 1
    maxfiber = max(fibers.values())
    # Each quotient class has exactly n preimages under the class map on Fp^*;
    # composing with x->2-x (a bijection on the field minus a point) preserves that up to the excluded point.
    # (2) input Parseval on Fp^*: F_a(x) = sum_{A in Q} a_A * chi_A(x) where chi_A are quotient characters.
    #     Quotient char indexed by j in 0..m-1: psi_j(x) = zeta_m^{ j * (dlog(x) mod m ... )}?
    #     Cleanest: Fourier over Q ~ Z/m. F_a(x) = sum_{j<m} a_j * exp(2pi i j * cls(x)/m).
    zeta_m = [cmath.exp(2j*math.pi*t/m) for t in range(m)]
    a = [complex(random.gauss(0,1), random.gauss(0,1)) for _ in range(m)]
    aNorm2 = sum(abs(v)**2 for v in a)
    def F(x):
        c = cls(x)
        return sum(a[j]*zeta_m[(j*c) % m] for j in range(m))
    inputEnergy = sum(abs(F(x))**2 for x in Fpstar)
    L_target = n*m*aNorm2
    # (3) class energy: T_D = sum_{x in Fp^*, cls(2-x)=D} F(x); outputEnergy uses 1/m normalization
    Tsum = defaultdict(complex)
    for x in Fpstar:
        y = (2-x) % p
        if y == 0: continue
        Tsum[cls(y)] += F(x)
    classEnergy = sum(abs(v)**2 for v in Tsum.values())
    outputEnergy = classEnergy / m
    return dict(p=p,n=n,m=m,maxfiber=maxfiber,
                inputEnergy=inputEnergy, L_target=L_target,
                L_ok=abs(inputEnergy-L_target)/L_target < 1e-6,
                classEnergy=classEnergy,
                class_le_n_input = classEnergy <= n*inputEnergy + 1e-6,
                outputEnergy=outputEnergy,
                out_le_nsq = outputEnergy <= n*n*aNorm2 + 1e-6,
                nsq_aNorm2 = n*n*aNorm2)

cells = [(1009,8),(1297,16),(2593,32),(3617,16),(4673,64)]
for p,n in cells:
    if not is_prime(p):
        print(p,"not prime"); continue
    if (p-1)%n!=0:
        print(p,n,"n not dividing p-1"); continue
    r = test_cell(p,n)
    print(f"n={r['n']:3d} p={r['p']:6d} m={r['m']:5d}  maxfiber={r['maxfiber']:3d} (<=n:{r['maxfiber']<=r['n']})  "
          f"L_ok={r['L_ok']}  class<=n*input={r['class_le_n_input']}  out<=n^2||a||^2={r['out_le_nsq']}")
