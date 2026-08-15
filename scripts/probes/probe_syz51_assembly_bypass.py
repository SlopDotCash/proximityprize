# Block-scale profile audit for the SYZ51 assembly-bypass conjecture.
# Question: at spread parameters (m>=4 blocks, each union U_j > 2n/3, rate 1/2 n=2k),
# do the block-scale pairwise-exclusive-intersection profiles (a,b,c) land in
# SYZ47's PROVEN region  max(a,b,c) >= floor((a+b+c)/2) - 1  (the 37.7% unbalanced strip)?
# SYZ47 is BLIND (gives only iota <= floor(d/2)) on the BALANCED interior:
#   BalancedInterior:  max(a,b,c) + 1 < floor((a+b+c)/2)
# We test whether balanced-interior block-scale profiles arise -> bypass fails there.

def in_proven_region(a,b,c):
    S=a+b+c
    return max(a,b,c) >= (S//2) - 1

def balanced_interior(a,b,c):
    S=a+b+c
    return max(a,b,c)+1 < (S//2)

# Enumerate symmetric / near-symmetric big-block pairwise-intersection profiles.
# For m>=4 blocks each of union size U>2n/3 in n points, pairwise intersections are
# >= 2U-n > n/3. Model the reduced band profile (a,b,c) = pairwise-exclusive overlap
# region sizes; balanced big blocks -> a~=b~=c~= (2U-n) region.
found_bal=0; found_proven=0; examples=[]
for k in range(4,41):
    n=2*k
    # band-realizable enumeration (SYZ50.Realizable) restricted to profiles that could be
    # "block-scale" (large a,b,c). We just report the full realizable split.
    for a in range(1,n):
        for b in range(a,n):
            for c in range(b,n):
                for t in range(0,n):
                    if not (a+b+c+t<=n): continue
                    if not (max(a,b,c)+1+t<=k): continue
                    if not (2*k+1<=a+b+c+2*t): continue
                    # realizable
                    if balanced_interior(a,b,c):
                        found_bal+=1
                        if len(examples)<6: examples.append((n,k,a,b,c,t))
                    if in_proven_region(a,b,c):
                        found_proven+=1
tot=found_bal+found_proven
print("realizable balanced-interior (SYZ47-BLIND) count:",found_bal)
print("realizable in-proven-region count:",found_proven)
print("sample balanced-interior realizable profiles (n,k,a,b,c,t):")
for e in examples: print("  ",e)
# specifically the symmetric big-block case:
print("\nsymmetric (d,d,d) realizable & balanced-interior:")
for k in range(4,41):
    n=2*k
    for d in range(1,n):
        for t in range(0,n):
            if 3*d+t<=n and d+1+t<=k and 2*k+1<=3*d+2*t:
                if balanced_interior(d,d,d):
                    print(f"  n={n} k={k} d={d} t={t}  max={d} floorS2={ (3*d)//2 }  BALANCED-INTERIOR (SYZ47 gives only iota<= {(3*d)//2 - d})")
                break
