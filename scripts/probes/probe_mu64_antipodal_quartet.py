"""Check whether the two even sextics of the antipodal septic quartet can split on μ64."""
from collections import Counter, defaultdict
from math import comb
from probe_many_head_locator_attack import require
from probe_mu64_septic_character import SITES, PRIME


def partial(rows, count):
    """Signed products on distinct antipodal classes (with the represented root mask)."""
    def visit(start, left, value, mask):
        if not left:
            yield value, mask
            return
        for i in range(start,len(rows)-left+1):
            j,pos,neg=rows[i]
            yield from visit(i+1,left-1,value*pos % PRIME,mask | 1 << j)
            yield from visit(i+1,left-1,value*neg % PRIME,mask | 1 << (j+32))
    yield from visit(0,count,1,0)


def main():
    eligible=defaultdict(lambda:[set(),set()])
    for j in range(1,32):
        t=SITES[j]
        target=[(-t-1)*pow(t-1,-1,PRIME)%PRIME,(-t+1)*pow(t+1,-1,PRIME)%PRIME]
        rows=[]
        for k in range(1,32):
            if k==j:
                continue
            x=SITES[k]
            pos=(t-x)*pow(-t-x,-1,PRIME)%PRIME
            neg=(t+x)*pow(-t+x,-1,PRIME)%PRIME
            require(pos*neg%PRIME==1,"opposite roots give reciprocal factors")
            rows.append((k,pos,neg))
        for r in range(8):
            small, large = (rows[:15],rows[15:]) if r<=3 else (rows[15:],rows[:15])
            small_count=min(r,7-r)
            table=defaultdict(list)
            for value,mask in partial(small,small_count):
                for color in (0,1):
                    table[target[color]*pow(value,-1,PRIME)%PRIME].append((color,mask))
            for value,mask in partial(large,7-small_count):
                for color,remainder in table.get(value,()):
                    eligible[mask|remainder][color].add(j)
    counts=Counter(len(c|d) for c,d in eligible.values())
    require(counts=={1:174528,2:96} and max(min(len(c),len(d)) for c,d in eligible.values())==1,
            "eligible antipodal pairs")
    print(f"{comb(31,7)*2**7} supports; {counts[1]} with one eligible pair, "
          f"{counts[2]} with two, none with three; the quartet needs six")


if __name__=="__main__":
    main()
