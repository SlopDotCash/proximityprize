import sympy as sp

a0,a1,a2,a3,c = sp.symbols('a0 a1 a2 a3 c')
E0 = a0**2 + c*(a2**2 - 2*a1*a3)
E1 = 2*a0*a2 - a1**2 - c*a3**2
u = a0*a1 - c*a2*a3
v = a1*a2 - a0*a3
n = a1**2 - c*a3**2
# claimed: u^2 + c v^2 = (a1^2+c a3^2)E0 - 2 c a1 a3 E1
A = sp.expand(u**2 + c*v**2 - ((a1**2+c*a3**2)*E0 - 2*c*a1*a3*E1))
B = sp.expand(2*u*v - n**2 - ((a1**2+c*a3**2)*E1 - 2*a1*a3*E0))
print("identity A residual:", A)
print("identity B residual:", B)

# End-to-end d=4 over F13, g = X(X-1)(X-2), e=(q-1)/4=3
import itertools, random
q=13
X = sp.symbols('X')
Fp = sp.GF(q) if hasattr(sp,'GF') else None
g = sp.Poly(X*(X-1)*(X-2), X, modulus=q)
e=(q-1)//4
w = g**e
# random blocks A_j(X,Y) with Y-deg <=2, X-block deg <= D; check relation sum g^{je} subq(Aj) = 0 only for trivial
# instead verify the derived-relation algebra: pick random A_j, compute R = sum w^j subq Aj, then check
# g*[(S0+w^2 S2)^2 - w^2 (S1+w^2 S3)^2] == subq(B0) + g^{2e} subq(B1) as polynomials, where
# B0 = g(X)A0^2 + g(Y)(A2^2-2A1A3), B1 = g(X)(2A0A2-A1^2) - g(Y)A3^2 evaluated at Y=X^q.
random.seed(1)
def rpoly(deg):
    return sp.Poly([random.randrange(q) for _ in range(deg+1)], X, modulus=q)
D=2
for trial in range(5):
    A=[[rpoly(D) for _ in range(3)] for _ in range(4)]  # Aj = sum_k Ajk(X) Y^k
    def subq(Aj):
        return sum((Aj[k]*sp.Poly(X**(q*k),X,modulus=q) for k in range(3)), sp.Poly(0,X,modulus=q))
    S=[subq(Aj) for Aj in A]
    lhs = g*((S[0]+w**2*S[2])**2 - w**2*(S[1]+w**2*S[3])**2)
    gY = lambda P: P  # g(X^q) = g^q mod p? g(X)^q == g(X^q) in F_q[X]
    gq = g**q

    sub_gY = gq
    B0s = g*S[0]**2 + sub_gY*(S[2]**2 - 2*S[1]*S[3])
    B1s = g*(2*S[0]*S[2]-S[1]**2) - sub_gY*S[3]**2
    rhs = B0s + g**(2*e)*B1s
    print("trial",trial,"fold identity:", (lhs-rhs)==sp.Poly(0,X,modulus=q))
