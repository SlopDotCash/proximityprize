import math
isqrt=math.isqrt
def fam(q):
    s=isqrt((q-4)//10); m=2*s; J=s+1; D=(q-5)//2
    return s,m,J,D
def check(q,B,K):
    s,m,J,D=fam(q); e=(q-1)//2
    if not(m>0 and J>0 and m<=e and 2*D+3<q and m*(D+2*m+J)<2*(J*(D+1))): return "budget-fail"
    Dtot=3*(m+e)+D+q*(J-1)
    if not(2*Dtot+3*m <= m*(B+q)): return "admiss-fail"
    if not(B*B<=K*q): return "Bsq-fail"
    return "ok"

# k=13 family: B=4*isqrt(10q), K=169, claim: all odd q>=171 ok (q<=169 trivial)
bad=[q for q in range(171,300002,2) if check(q,4*isqrt(10*q),169)!="ok"]
print("k13 fails in [171,300001]:", bad[:10], "count",len(bad))
for q in [171,173,1009,10007,65537,2**20+7]:
    print(q, check(q,4*isqrt(10*q),169), "B/sqrt(q)=",4*isqrt(10*q)/math.sqrt(q))
# also find min q0 where k13 family works for ALL odd q>=q0
q0=171
for q in range(169,89,-2):
    if check(q,4*isqrt(10*q),169)=="ok": q0=q
    else: break
print("k13 works down to q0 =", q0)
# tight k=7 family: B = isqrt(49*q); find q0(7)
lastfail=0
for q in range(5,2000002,2):
    if check(q,isqrt(49*q),49)!="ok": lastfail=q
print("k7 (B=isqrt(49q)) last fail:",lastfail)
# k=8
lastfail=0
for q in range(5,2000002,2):
    if check(q,isqrt(64*q),64)!="ok": lastfail=q
print("k8 last fail:",lastfail)
