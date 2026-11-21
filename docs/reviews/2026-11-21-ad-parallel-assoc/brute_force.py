# Brute-force check of AD parallel associativity at one started prior.
# Usage: python3 -I brute_force.py N MODE [SAMPLES]
#   N states; MODE total | partial | nondet picks the symmetric, associative merges j;
#   SAMPLES limits the operand triples checked per merge (default: all).
# Full AD at a fixed started prior s0. An A-healthy AD there is a pair (F, U):
#   F = up-closed family of sets on which it may diverge (¬pre, PBMH), may contain {}
#   U = up-closed family of terminating offered sets (post, PBMH), {} ∉ U (A0)
# observations: (False, X) for X in F; (True, X) for X in F ∪ U.
# Parallel uses merge_ades_obs at ok0 = True:
#   XL≠{} ∧ XR≠{} ∧ (∀∀∃s'. j) ∧ (okL ∧ okR ⟶ ok' ∧ ∀∀∃s'∈Z. j)
import itertools, sys, random
n = int(sys.argv[1]); mode = sys.argv[2]; samples = int(sys.argv[3]) if len(sys.argv) > 3 else 0
S = range(n); FULL = 1 << n
def el(m): return [i for i in S if m >> i & 1]
upsets = []
for fam in range(1 << FULL):
    F = [X for X in range(FULL) if fam >> X & 1]
    if all((X | Y) in F for X in F for Y in range(FULL)): upsets.append(frozenset(F))
ADs = []
for F in upsets:
    for U in upsets:
        if 0 in U: continue
        ADs.append(frozenset([(False, X) for X in F] + [(True, X) for X in F | U]))
def par(OP, OQ, J):
    out = set()
    for cl, XL in OP:
        if not XL: continue
        for cr, XR in OQ:
            if not XR: continue
            if not all(J[a][b] for a in el(XL) for b in el(XR)): continue
            for c in (False, True):
                for Z in range(FULL):
                    if (c, Z) in out: continue
                    if not (cl and cr) or (c and all(J[a][b] & Z for a in el(XL) for b in el(XR))):
                        out.add((c, Z))
    return frozenset(out)
def assoc(J):
    for a, b, c in itertools.product(S, S, S):
        l = 0
        for u in el(J[a][b]): l |= J[u][c]
        r = 0
        for v in el(J[b][c]): r |= J[v][a]
        if l != r: return False
    return True
opts = {'total': [1 << i for i in S], 'partial': [0] + [1 << i for i in S],
        'nondet': list(range(1, FULL))}[mode]
pairs = [(a, b) for a in S for b in S if a <= b]
Js = []
for ch in itertools.product(opts, repeat=len(pairs)):
    J = [[0]*n for _ in S]
    for (a, b), m in zip(pairs, ch): J[a][b] = J[b][a] = m
    if assoc(J): Js.append(J)
print("ADs per prior:", len(ADs), "symmetric associative j:", len(Js))
trip = list(itertools.product(ADs, repeat=3))
if samples: trip = random.sample(trip, min(samples, len(trip)))
for J in Js:
    cache = {}
    def p(a, b):
        k = (a, b)
        if k not in cache: cache[k] = par(a, b, J)
        return cache[k]
    for P, Q, R in trip:
        if p(p(P, Q), R) != p(P, p(Q, R)):
            def show(O): return sorted((c, el(X)) for c, X in O if not any(c2 >= c and Y & X == Y and Y != X for c2, Y in O))
            print("COUNTEREXAMPLE j =", {(a, b): el(J[a][b]) for a, b in pairs})
            for nm, O in (("P", P), ("Q", Q), ("R", R)): print(" ", nm, "minimal obs:", show(O))
            print("  left only :", sorted((c, el(X)) for c, X in p(p(P,Q),R) - p(P,p(Q,R)))[:6])
            print("  right only:", sorted((c, el(X)) for c, X in p(P,p(Q,R)) - p(p(P,Q),R))[:6])
            sys.exit(0)
print("no counterexample")
