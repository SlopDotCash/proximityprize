import math
isqrt=math.isqrt
def fam(q):
    s=isqrt((q-4)//10); return s,2*s,s+1,(q-5)//2
def admiss(q,B):
    s,m,J,D=fam(q); e=(q-1)//2
    Dtot=3*(m+e)+D+q*(J-1)
    return 2*Dtot+3*m <= m*(B+q)
for c0 in [30,32,33,36,40]:
    lastfail=0
    for q in range(15,3000002,2):
        b=isqrt(10*q); B=2*b+c0
        if not(admiss(q,B) and B*B<=49*q): lastfail=q
    print("c0=",c0,"last fail:",lastfail)
# check key sublemmas for c0=33: 11s>=b+1 and B^2<=49q thresholds
lf1=lf2=0
for q in range(15,3000002,2):
    s=isqrt((q-4)//10); b=isqrt(10*q)
    if not(11*s>=b+1): lf1=q
    if not((2*b+33)**2<=49*q): lf2=q
print("11s>=b+1 last fail:",lf1," (2b+33)^2<=49q last fail:",lf2)
