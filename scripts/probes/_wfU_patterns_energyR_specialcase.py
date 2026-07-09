import itertools, random
# Confirm: energyR G 1 == |G|,  energyR G 2 == addEnergy(G) (2-tuple),  energyR G 3 == addEnergy3(G)
# i.e. the three special-case "moment" files are LITERAL instances of energyR at r=1,2,3.
def energyR(G, q, r):
    cnt=0
    for x in itertools.product(G, repeat=r):
        for z in itertools.product(G, repeat=r):
            if sum(x)%q == sum(z)%q: cnt+=1
    return cnt
def addEnergy2(G,q):
    c=0
    for a in G:
        for ap in G:
            for cc in G:
                for cp in G:
                    if (a+ap)%q==(cc+cp)%q: c+=1
    return c
def addEnergy3(G,q):
    c=0
    for y in itertools.product(G,repeat=3):
        for z in itertools.product(G,repeat=3):
            if sum(y)%q==sum(z)%q: c+=1
    return c
random.seed(3)
ok=True
for _ in range(8):
    q=random.choice([7,11,13,17,19])
    G=sorted(random.sample(range(q), random.randint(2,4)))
    e1,e2,e3 = energyR(G,q,1), energyR(G,q,2), energyR(G,q,3)
    a2,a3 = addEnergy2(G,q), addEnergy3(G,q)
    c1 = (e1==len(G)); c2=(e2==a2); c3=(e3==a3)
    ok = ok and c1 and c2 and c3
    print(f"q={q} G={G}: energyR1={e1}(=|G|? {c1}) energyR2={e2}(=addEnergy {c2}) energyR3={e3}(=addEnergy3 {c3})")
print("ALL CONSISTENT" if ok else "MISMATCH")
