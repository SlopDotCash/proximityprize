#!/usr/bin/env python3
"""
sweep_A26_interleaved_subjohnson.py  --  Actionable A26, Part B.

Compute the ACTUAL m=2 interleaved list size of explicit split stacks (u0, u1) over the
smooth RS code RS[F17, mu_16, k=2] at agreement floors BELOW the interleaved Johnson radius,
to extract a concrete *interleaved* beyond-Johnson list-size lower bound for a Lean brick.

interleavedList(C, u0, u1, a) = #{ (c0, c1) in C x C :
        #{x in mu_n : c0(x)=u0(x) AND c1(x)=u1(x)} >= a }.

Interleaved Johnson cap (interleavedList_card_le_johnson):
    |interleavedList| <= n^2/(a^2 - n*e)   when  n*e < a^2,   e = k-1 = 1.
So the interleaved Johnson radius is a_IJ = floor(sqrt(n*e)) = floor(sqrt(16)) = 4.
At a <= 4 the cap is N/A; any interleaved list size we exhibit there is BEYOND what the
interleaved Johnson bound delivers.

We look for an explicit (u0, u1) whose interleaved list at a sub-Johnson floor a<=4 is
provably >1 (a non-trivial interleaved list below the Johnson radius) --- landable by decide.
"""

p = 17
G = list(range(1, 17))
n = len(G)
k = 2
e = k - 1

# all RS codewords = lines b*x+c
lines = [(b, c) for b in range(p) for c in range(p)]

def cw(b, c):
    return [(b*x + c) % p for x in G]

def joint_agree(c0vals, c1vals, u0, u1):
    return sum(1 for i in range(n)
               if c0vals[i] == u0[i] and c1vals[i] == u1[i])

def interleaved_list_size(u0, u1, a):
    cnt = 0
    for (b0, c0) in lines:
        v0 = cw(b0, c0)
        # quick row-0 prune
        if sum(1 for i in range(n) if v0[i] == u0[i]) < a:
            continue
        for (b1, c1) in lines:
            v1 = cw(b1, c1)
            if joint_agree(v0, v1, u0, u1) >= a:
                cnt += 1
    return cnt

print("=== A26 Part B: interleaved list sizes below the interleaved Johnson radius ===")
import math
a_IJ = math.isqrt(n*e)
print(f"  n={n}, e=k-1={e}, interleaved Johnson radius a_IJ=floor(sqrt(n*e))={a_IJ}")
print(f"  Johnson cap N/A at a <= {a_IJ}; any |interleavedList| at such a is beyond-Johnson.")
print()

# Build a split stack: u0 = a hard word that is itself a stitch of lines (row 0),
# u1 = another stitch (row 1). Use the in-tree hard word for row 0; design row 1 to share
# the SAME block structure so joint agreement clusters.
w0 = [1,2,3,4,13,15,0,2,16,2,5,8,10,14,1,5]      # in-tree hard word (4 line-blocks)
# row 1: stitch four DIFFERENT lines on the same four blocks so each block has a joint match.
# blocks of G: [1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]
def stitch(line_per_block):
    out = []
    for blk in range(4):
        b, c = line_per_block[blk]
        for x in G[blk*4:(blk+1)*4]:
            out.append((b*x + c) % p)
    return out

# Recover which line each block of w0 follows (it is a stitch):
def recover_block_lines(word):
    res = []
    for blk in range(4):
        xs = G[blk*4:(blk+1)*4]
        ys = word[blk*4:(blk+1)*4]
        # solve b,c from first two points
        x0,x1 = xs[0],xs[1]; y0,y1=ys[0],ys[1]
        # b*(x0-x1) = y0-y1 mod p
        inv = pow((x0-x1) % p, p-2, p)
        b = ((y0-y1) * inv) % p
        c = (y0 - b*x0) % p
        # verify all four
        ok = all((b*x+c)%p == y for x,y in zip(xs,ys))
        res.append((b,c,ok))
    return res

print("  row-0 word block decomposition (b,c,exact-line?):", recover_block_lines(w0))

# row 1: pick four lines distinct from row-0's and from each other
u1lines = [(2,1),(7,3),(11,5),(1,9)]
w1 = stitch(u1lines)
print("  row-1 stitched word:", w1)
print()

for a in range(2, 6):
    sz = interleaved_list_size(w0, w1, a)
    gap = (n*e < a*a)
    cap = (n*n)//(a*a - n*e) if gap else None
    tag = f"Johnson cap = {cap}" if gap else "Johnson cap N/A (sub-radius)"
    beyond = (not gap and sz > 1)
    print(f"  a={a}: |interleavedList(w0,w1,a)| = {sz:4d}   ({tag})"
          f"{'   <-- BEYOND-JOHNSON (>1, cap N/A)' if beyond else ''}")
print()

# Also report base-code single-row sub-Johnson lower bound (the simplest landable statement):
def base_list2(word, a):
    cnt=0
    for (b,c) in lines:
        ag = sum(1 for i in range(n) if (b*G[i]+c)%p==word[i])
        if ag>=a: cnt+=1
    return cnt

print("=== base-code (single-row) sub-Johnson list lower bound on w0 ===")
print(f"  Johnson base radius a_J = floor(sqrt(n*e)) = {a_IJ};  Johnson gap (n*e<a^2) needs a>={a_IJ+1}")
for a in range(2,6):
    sz=base_list2(w0,a)
    gap=(n*e<a*a)
    print(f"  a={a}: base listSize={sz:4d}  Johnson-gap(n*e<a^2)={gap}"
          f"{'   <-- beyond-Johnson (cap N/A) list >1' if (not gap and sz>1) else ''}")
print()
print("=== DONE ===")
