"""F with divergence, at one started prior.

A process is a pair (UT, UF) of up-closed families of nonempty state sets, with
UF <= UT (H2): the sets the angel may pick with ok' true, and with ok' false.
A CSP (A2) process is an atom (GT, GF) with GF <= GT: it offers a set iff the set
meets GT (ok' true) or GF (ok' false). g <= P iff GT blocks UT and GF blocks UF.

Parallel of atoms follows merge_rdes: a pair of terminating states merges by j;
a pair with a divergent side merges by D and leaves ok' free. F is the join of the
atom parallels below the operands. Run with python3 -I; under a second.
"""
import itertools
import random

N = 2
S = range(N)
NS = 1 << N
SETS = list(range(1, NS))


def upclosed(fam):
    return all(Y in fam for X in fam for Y in SETS if X & Y == X)


FAMS = [fam for bits in range(1 << len(SETS))
        for fam in [frozenset(SETS[i] for i in range(len(SETS)) if bits >> i & 1)]
        if upclosed(fam)]
PROCS = [(UT, UF) for UT in FAMS for UF in FAMS if UF <= UT]
ATOMS = [(GT, GF) for GT in range(NS) for GF in range(NS) if GF & GT == GF]


def blocks(G, fam):
    return all(G & X for X in fam)


def below(atom, P):
    return blocks(atom[0], P[0]) and blocks(atom[1], P[1])


def fam_of(H):
    return frozenset(X for X in SETS if X & H)


def par_atoms(g, h, j, D):
    (GT, GF), (HT, HF) = g, h
    img_t = img_d = 0
    for a in S:
        for b in S:
            if GT >> a & 1 and HT >> b & 1:
                img_t |= j[a][b]
            if (GF >> a & 1 and HT >> b & 1) or (GT >> a & 1 and HF >> b & 1):
                img_d |= D[a][b]
    return fam_of(img_t | img_d), fam_of(img_d)


def F(P, Q, j, D):
    UT, UF = set(SETS), set(SETS)
    for g in ATOMS:
        if below(g, P):
            for h in ATOMS:
                if below(h, Q):
                    t, f = par_atoms(g, h, j, D)
                    UT &= t
                    UF &= f
    return frozenset(UT), frozenset(UF)


def join(P, Q):
    return P[0] & Q[0], P[1] & Q[1]


def cached(j, D):
    memo = {}

    def FF(P, Q):
        if (P, Q) not in memo:
            memo[(P, Q)] = F(P, Q, j, D)
        return memo[(P, Q)]
    return FF


def lift_sets(j, A, B):
    r = 0
    for a in S:
        for b in S:
            if A >> a & 1 and B >> b & 1:
                r |= j[a][b]
    return r


def check_angelic_dist():
    rng = random.Random(20261125)
    stats = {}
    for trial in range(12):
        j = [[rng.randrange(NS) for _ in S] for _ in S]
        if trial % 2:
            D = [[NS - 1] * N for _ in S]
        else:
            D = [[j[a][b] | rng.randrange(NS) for b in S] for a in S]
        FF = cached(j, D)
        for P, Q, R in itertools.product(PROCS, repeat=3):
            ok = FF(P, join(Q, R)) == join(FF(P, Q), FF(P, R))
            for name, cond in [("all operands", True),
                               ("Q, R nondivergent", not Q[1] and not R[1]),
                               ("Q, R with equal divergence", Q[1] == R[1])]:
                if cond:
                    c, f = stats.get(name, (0, 0))
                    stats[name] = (c + 1, f + (not ok))
    print("A. F over the angelic choice, 12 random merges on 2 states:")
    for name, (c, f) in stats.items():
        print(f"   {name}: {c} cases, {f} failures")


def check_named():
    # j(0,0) = {0}, j(0,1) = {}, j(1,0) = {0,1}, D = all; P = <0> join <1>,
    # Q = Chaos_0 join Chaos_1, R = <0>: Q join R = <0> join <1> loses Q's divergence
    j = [[1, 0], [3, 0]]
    D = [[3, 3], [3, 3]]
    P = (frozenset({3}), frozenset())
    Q = (frozenset({3}), frozenset({3}))
    R = (frozenset({1, 3}), frozenset())
    FF = cached(j, D)
    lhs, rhs = FF(P, join(Q, R)), join(FF(P, Q), FF(P, R))
    print("B. named case: F(P, Q join R) =", sorted(lhs[0]), sorted(lhs[1]),
          " F(P,Q) join F(P,R) =", sorted(rhs[0]), sorted(rhs[1]))


def check_assoc():
    merges = []
    for vals in itertools.product(range(1, NS), repeat=N * N):
        j = [[vals[a * N + b] for b in S] for a in S]
        if any(j[a][b] != j[b][a] for a in S for b in S):
            continue
        if all(lift_sets(j, lift_sets(j, 1 << a, 1 << b), 1 << c) ==
               lift_sets(j, 1 << a, lift_sets(j, 1 << b, 1 << c))
               for a in S for b in S for c in S):
            merges.append(j)
    for name, mk in [("D = all", lambda j: [[NS - 1] * N for _ in S]), ("D = j", lambda j: j)]:
        cases = fails = 0
        for j in merges:
            FF = cached(j, mk(j))
            for P, Q, R in itertools.product(PROCS, repeat=3):
                cases += 1
                fails += FF(FF(P, Q), R) != FF(P, FF(Q, R))
        print(f"C. F associative, {len(merges)} total symmetric associative merges, {name}: "
              f"{cases} cases, {fails} failures")


if __name__ == "__main__":
    print(len(PROCS), "processes,", len(ATOMS), "CSP atoms on", N, "states")
    check_angelic_dist()
    check_named()
    check_assoc()
