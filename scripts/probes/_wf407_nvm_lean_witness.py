# Produce the EXACT matrix entries for the Lean countermodel (ZMod 73).
# Points: 1, 72(=-1), 27 (= zeta^2, where zeta=10 a primitive 8th root in F_73).
# Degrees: 0,1,4  -> det should be 0 mod 73.
p=73
zeta=10
# verify zeta is a primitive 8th root of unity
print("zeta^8 mod p =", pow(zeta,8,p), "(want 1)")
print("zeta^4 mod p =", pow(zeta,4,p), "(want 72 = -1)")
pts=[1, 72, 27]   # 27 = zeta^2 = 100 mod 73 = 27
print("zeta^2 mod p =", pow(zeta,2,p))
degs=[0,1,4]
M=[[pow(x,d,p) for d in degs] for x in pts]
print("Matrix [x^d] rows=points {1,72,27}, cols deg {0,1,4}:")
for row in M: print("  ", row)
# determinant mod p, exact integer det then mod
def detZ(M):
    import itertools
    n=len(M); s=0
    for perm in itertools.permutations(range(n)):
        # sign
        sign=1
        pl=list(perm)
        for i in range(n):
            for j in range(i+1,n):
                if pl[i]>pl[j]: sign=-sign
        prod=1
        for i in range(n): prod*=M[i][perm[i]]
        s+=sign*prod
    return s
dZ=detZ(M)
print("integer det =", dZ, " mod 73 =", dZ % 73)
# also the nonsingular control deg 0,1,2
M2=[[pow(x,d,p) for d in [0,1,2]] for x in pts]
print("control det (deg 0,1,2) =", detZ(M2)%73, "(nonzero)")
