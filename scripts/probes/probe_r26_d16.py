import sympy as sp
import random

# ---- A. fold 16->8: conjugate product identity ----
w = sp.symbols('w')
s = sp.symbols('s0:16')
R  = sum(w**j * s[j] for j in range(16))
Rc = sum((-1)**j * w**j * s[j] for j in range(16))
v = w**2
P = sum(s[2*i] * v**i for i in range(8))
Q = sum(s[2*i+1] * v**i for i in range(8))
assert sp.expand(R*Rc - (P**2 - v*Q**2)) == 0
print("A1 fold identity OK")

# c_m convolution formula
V = sp.symbols('V')
p = [s[2*i] for i in range(8)]; qq = [s[2*i+1] for i in range(8)]
Pv = sum(p[i]*V**i for i in range(8)); Qv = sum(qq[i]*V**i for i in range(8))
expr = sp.expand(Pv**2 - V*Qv**2)
c = []
for m in range(16):
    cm = sum(p[i]*p[m-i] for i in range(8) if 0 <= m-i <= 7) \
       - sum(qq[i]*qq[m-1-i] for i in range(8) if 0 <= m-1-i <= 7)
    c.append(sp.expand(cm))
assert sp.expand(expr - sum(c[m]*V**m for m in range(16))) == 0
print("A2 c_m convolution OK")
for m in range(16):
    print("c%d = %s" % (m, c[m]))

# ---- B. regroup: sedecic e_j = c_j + t*c_{j+8}; b_i = a_i + a_{i+8} s, s^2 = t ----
a = sp.symbols('a0:16'); t, S = sp.symbols('t S')
# substitute s_j -> a_j in c
subs = {s[j]: a[j] for j in range(16)}
cc = [ci.subs(subs) for ci in c]
e = [sp.expand(cc[j] + t*cc[j+8]) for j in range(8)]
b = [a[i] + a[i+8]*S for i in range(8)]
h = [
 b[0]**2 + S*(2*b[2]*b[6] + b[4]**2 - 2*b[1]*b[7] - 2*b[3]*b[5]),
 2*b[0]*b[2] - b[1]**2 + S*(2*b[4]*b[6] - 2*b[3]*b[7] - b[5]**2),
 2*b[0]*b[4] + b[2]**2 - 2*b[1]*b[3] + S*(b[6]**2 - 2*b[5]*b[7]),
 2*b[0]*b[6] + 2*b[2]*b[4] - 2*b[1]*b[5] - b[3]**2 - S*b[7]**2,
]
for j in range(4):
    diff = sp.expand(h[j] - (e[j] + S*e[j+4]))
    rem = sp.rem(sp.Poly(diff, S), sp.Poly(S**2 - t, S))
    if sp.expand(sp.expand(rem.as_expr())) != 0:
        print("B FAIL j=%d rem=%s" % (j, rem.as_expr())); break
else:
    print("B regroup identity OK (h_j = e_j + s*e_{j+4} mod s^2=t)")

# ---- C. numeric end-to-end over F_97 (q=97, 16|96) ----
q = 97; e16 = (q-1)//16
Fx = sp.GF(q)
# find g squarefree deg 1 -> use g = X + 3 (deg 1, squarefree); w = g^e in blocks? Numeric shortcut:
# pick random point evaluation: X=x0, Y=y0; w = g(x0)^e16 * ... actually verify the folded 8-block
# relation numerically: choose random field elems for A_j blocks at a point, gX=g(x0), gY=g(y0)
random.seed(1)
for trial in range(200):
    gX = random.randrange(1, q); gY = random.randrange(1, q)
    A = [random.randrange(q) for _ in range(16)]
    # E_j = gX*c_j + gY*c_{j+8} evaluated
    def conv(m):
        r = sum(A[2*i]*A[2*(m-i)] for i in range(8) if 0 <= m-i <= 7) \
          - sum(A[2*i+1]*A[2*(m-1-i)+1] for i in range(8) if 0 <= m-1-i <= 7)
        return r % q
    # if sum relation holds: R = sum g^{je} s_j = 0 with s_j = A_j (point eval, subq trivial at point? approximate check of ring identity):
    wv = pow(gX, e16, q)
    R = sum(pow(wv, j, q)*A[j] for j in range(16)) % q
    Rc = sum(pow(q-1, j, q)*pow(wv, j, q)*A[j] for j in range(16)) % q
    lhs = (gX * R * Rc) % q
    # rhs = sum_{j<8} v^j * (gX*c_j + gX^q... at point gY plays role of g^q=g(X^q)->g(Y); for pure numeric identity use gX for both halves with v^8 = w^16 = gX^{q-1}=1
    vv = pow(wv, 2, q)
    rhs = sum(pow(vv, j, q) * ((gX*conv(j) + pow(gX, q, q)*conv(j+8)) % q) for j in range(8)) % q
    assert lhs == rhs, (trial, lhs, rhs)
print("C numeric F_97 fold OK (200 trials)")

# ---- D. quotients K_j: h_j - (e_j + S e_{j+4}) = K_j * (S^2 - t) ----
for j in range(4):
    diff = sp.expand(h[j] - (e[j] + S*e[j+4]))
    Kj, rem = sp.div(sp.Poly(diff, S), sp.Poly(S**2 - t, S))
    assert sp.expand(rem.as_expr()) == 0
    print("K%d =" % j, sp.factor(sp.expand(Kj.as_expr())))
