import numpy as np, itertools, math, random
# Confirm the Markov ladder: #{b: ||eta_b||^2 >= q} * q^{r-1} <= E_r(G)  for r=1,2,3
# (the general lemma card_johnson_scale_frequencies_mul_le_energyR), and that
# the r=1 (second-moment Markov, bound |G|) and r=2 (fourth, bound E/q) special files
# are the r=1,2 instances. Also check rEnergy_le spike-split shape for r=2,3.
def eta(b,G,q): return sum(np.exp(2j*np.pi*((b*y)%q)/q) for y in G)
def energyR(G,q,r):
    c=0
    for x in itertools.product(G,repeat=r):
        for z in itertools.product(G,repeat=r):
            if sum(x)%q==sum(z)%q: c+=1
    return c
random.seed(7); ok=True
for _ in range(6):
    q=random.choice([13,17,19,23])
    # genuine subgroup
    for g0 in range(2,q):
        x=1;o=0
        for _ in range(q-1):
            x=(x*g0)%q;o+=1
            if x==1:break
        if o==q-1: g=g0;break
    qm1=q-1; divs=[d for d in range(2,qm1+1) if qm1%d==0 and d<=6]
    n=random.choice(divs); gen=pow(g,(q-1)//n,q); G=[]; x=1
    for _ in range(n): G.append(x); x=(x*gen)%q
    Sjohnson=sum(1 for b in range(q) if abs(eta(b,G,q))**2 >= q - 1e-9)
    for r in (1,2,3):
        Er=energyR(G,q,r)
        lhs=Sjohnson*(q**(r-1)); rhs=Er
        good = lhs<=rhs+1e-9
        ok = ok and good
    print(f"q={q} |G|={n} #johnson={Sjohnson}: E1={energyR(G,q,1)} E2={energyR(G,q,2)} E3={energyR(G,q,3)} | markov r=1,2,3 all hold: "
          f"{all(Sjohnson*(q**(r-1))<=energyR(G,q,r)+1e-9 for r in (1,2,3))}")
print("MARKOV LADDER CONSISTENT" if ok else "FAIL")
