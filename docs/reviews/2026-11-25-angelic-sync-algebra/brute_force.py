"""Brute-force comparison of parallel operators for angelic choice.

Three finite models, all at one started prior and without the ok flags:

A. Abstract: states 0..n-1, a program is BOT (divergence) or an up-closed
   family U of nonempty sets ac' (the demon offers ac', the angel picks a
   state in it).  U = {} is Miracle.  P ⊑ Q iff U_Q ⊆ U_P.  ⊓ is union,
   ⊔ is intersection.  A merge j maps a pair of branch states to a set of
   merged states (empty: no merge).
B. Reactive: the RAD observations (wait, tr, ref) after a started,
   non-waiting prior with tr0 = [], over events {a, b}; families are kept as
   antichains of minimal sets.  jsync synchronises on every event.
C. Failures style: the A2 (CSP) processes of model B, with the demon-first
   reading of the angelic choice that stays unresolved while both branches
   can do the event (candidate d).

Parallel operators compared:
  lift   (e)  the current lift: ∃X∈U_P, Y∈U_Q. ∀x∈X, y∈Y. ac' ∩ j(x,y) ≠ {}
  F      (b)  the join of g ∥ h over A2 g ⊑ P, h ⊑ Q; computed with blockers:
              ∀G∈b(U_P), H∈b(U_Q). ac' ∩ j[G×H] ≠ {}
  MIN    (a)  minimal sets, only the pairs that merge (at least one)
  GIVEUP (c)  minimal sets; an unmatched pair with an angelic alternative
              gives up (a designated deadlock outcome); demonic ones block
  H      (f)  demon first with deterministic atoms: ⊓ over deterministic
              refinements of each blocker, then ⊔ of the CSP parallels
  ⊞      (d)  CSP parallel, with the angelic choice replaced by ⊞ (part C)
Run: python3 -I brute_force.py   (about 30 s; the seed is fixed)
"""
import itertools, random, sys
from functools import lru_cache

random.seed(20261125)
FAILS = []


def report(name, ok, cex=None):
    line = f"{'PASS' if ok else 'FAIL'}  {name}"
    if cex is not None:
        line += f"\n        counterexample: {cex}"
    print(line)
    return ok


def bits(m):
    i = 0
    while m:
        if m & 1:
            yield i
        m >>= 1
        i += 1


def popcount(m):
    return bin(m).count("1")


# =====================================================================
# A. Abstract model
# =====================================================================
BOT = None


class Abs:
    def __init__(self, n, names=None, enumerate_all=True):
        self.n = n
        self.subs = list(range(1, 1 << n))
        self.FULL = sum(1 << Z for Z in self.subs)
        self.names = names or [str(i) for i in range(n)]
        self.up = {X: sum(1 << Z for Z in self.subs if Z & X == X) for X in self.subs}
        self._min = {}
        self._blk = {}
        self._T = {}
        if enumerate_all:
            self.fams = sorted({self.upclose(f) for f in self.antichains()})
        self.A2vals = [BOT] + [self.A2(G) for G in range(1 << n)]

    def antichains(self):
        # every up-closed family is the up-closure of a set of nonempty subsets
        for k in range(0, 1 << len(self.subs)):
            yield sum(1 << self.subs[i] for i in bits(k))

    def upclose(self, f):
        out = 0
        for X in bits(f):
            out |= self.up[X]
        return out

    def members(self, f):
        return [X for X in self.subs if f >> X & 1]

    def minimal(self, f):
        if f not in self._min:
            mem = self.members(f)
            self._min[f] = [X for X in mem if not any(Y != X and Y & X == Y for Y in mem)]
        return self._min[f]

    def T(self, E):
        """Family of nonempty sets meeting every set in E."""
        E = tuple(sorted(set(E)))
        if E not in self._T:
            if any(e == 0 for e in E):
                self._T[E] = 0
            else:
                self._T[E] = sum(1 << Z for Z in self.subs if all(Z & e for e in E))
        return self._T[E]

    def A2(self, G):
        """Demonic choice over the states in G (Miracle if G is empty)."""
        return sum(1 << Z for Z in self.subs if Z & G)

    def point(self, *xs):
        return self.A2(sum(1 << x for x in xs))

    def blockers(self, f):
        if f not in self._blk:
            mem = self.members(f)
            c = [G for G in range(1 << self.n) if all(G & X for X in mem)]
            self._blk[f] = [G for G in c if not any(H != G and H & G == H for H in c)]
        return self._blk[f]

    def is_A2(self, f):
        if f is BOT:
            return True
        pts = sum(1 << x for x in range(self.n) if f >> (1 << x) & 1)
        return f == self.A2(pts)

    def show(self, f):
        if f is BOT:
            return "Chaos"
        if f == 0:
            return "Miracle"
        sets = ["{" + ",".join(self.names[x] for x in bits(X)) + "}" for X in self.minimal(f)]
        return "↑{" + " ".join(sets) + "}"


def dem(P, Q):
    return BOT if P is BOT or Q is BOT else P | Q


def ang(P, Q):
    if P is BOT:
        return Q
    if Q is BOT:
        return P
    return P & Q


def ref(P, Q):
    """P ⊑ Q"""
    if P is BOT:
        return True
    if Q is BOT:
        return False
    return Q & ~P == 0


def zeros(P, Q):
    if P == 0 or Q == 0:        # Miracle is a zero, also against Chaos
        return 0
    if P is BOT or Q is BOT:    # Chaos is a zero against feasible operands
        return BOT
    return "go"


def lift(M, P, Q, j):
    z = zeros(P, Q)
    if z != "go":
        return z
    fam = 0
    for X in M.minimal(P):
        for Y in M.minimal(Q):
            fam |= M.T([j[x][y] for x in bits(X) for y in bits(Y)])
    return fam


def Fop(M, P, Q, j):
    z = zeros(P, Q)
    if z != "go":
        return z
    fam = M.FULL
    for G in M.blockers(P):
        for H in M.blockers(Q):
            img = 0
            for g in bits(G):
                for h in bits(H):
                    img |= j[g][h]
            fam &= M.A2(img)
    return fam


def Fkan(M, P, Q, j):
    """Join of lift(g, h) over A2 g ⊑ P and h ⊑ Q (the defining form of F)."""
    acc = BOT
    for g in M.A2vals:
        if ref(g, P):
            for h in M.A2vals:
                if ref(h, Q):
                    acc = ang(acc, lift(M, g, h, j))
    return acc


def MINop(M, P, Q, j):
    z = zeros(P, Q)
    if z != "go":
        return z
    fam = 0
    for X in M.minimal(P):
        for Y in M.minimal(Q):
            E = [j[x][y] for x in bits(X) for y in bits(Y) if j[x][y]]
            if E:
                fam |= M.T(E)
    return fam


def make_giveup(delta):
    def GIVEUP(M, P, Q, j):
        z = zeros(P, Q)
        if z != "go":
            return z
        fam = 0
        for X in M.minimal(P):
            for Y in M.minimal(Q):
                angelic = popcount(X) > 1 or popcount(Y) > 1
                E, ok = [], True
                for x in bits(X):
                    for y in bits(Y):
                        if j[x][y]:
                            E.append(j[x][y])
                        elif angelic:
                            E.append(1 << delta)
                        else:
                            ok = False
                if ok:
                    fam |= M.T(E)
        return fam
    return GIVEUP


# ---------------------------------------------------------------------
# merges
# ---------------------------------------------------------------------
def rand_merge(n, kind, sym=False):
    j = [[0] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            if sym and y < x:
                j[x][y] = j[y][x]
                continue
            if kind == "fun":
                v = 1 << random.randrange(n)
            elif kind == "pfun":
                v = random.choice([0] + [1 << k for k in range(n)])
            elif kind == "rel":
                v = random.randrange(1, 1 << n)
            else:  # prel
                v = random.randrange(0, 1 << n)
            j[x][y] = v
    return j


def is_sym(j):
    n = len(j)
    return all(j[x][y] == j[y][x] for x in range(n) for y in range(n))


def img(j, A, B):
    out = 0
    for a in bits(A):
        for b in bits(B):
            out |= j[a][b]
    return out


def is_assoc(j):
    n = len(j)
    return all(img(j, j[a][b], 1 << c) == img(j, 1 << a, j[b][c])
               for a in range(n) for b in range(n) for c in range(n))


def is_fun(j):
    return all(popcount(v) == 1 for row in j for v in row)


def is_total(j):
    return all(v for row in j for v in row)


def all_sym_merges(n):
    pairs = [(x, y) for x in range(n) for y in range(x, n)]
    for vals in itertools.product(range(1 << n), repeat=len(pairs)):
        j = [[0] * n for _ in range(n)]
        for (x, y), v in zip(pairs, vals):
            j[x][y] = j[y][x] = v
        yield j


OPS = {"lift (e)": lift, "F (b)": Fop, "MIN (a)": MINop}


def law_suite(M, ops, merges, samples, label):
    """Check L1, L2, L4, L5 (commutativity, zeros) for each operator."""
    vals = [BOT] + M.fams
    feas = [f for f in M.fams if f != 0]
    A2s = [v for v in vals if M.is_A2(v)]
    res = {}
    for name, op in ops.items():
        r = {}
        cex = {}

        def note(key, ok, c):
            if not ok and key not in cex:
                cex[key] = c
            r[key] = r.get(key, True) and ok

        for _ in range(samples):
            j = random.choice(merges)
            P, Q, R = random.choice(vals), random.choice(vals), random.choice(vals)
            # L1: agreement with the lift (= ordinary parallel) on A2 operands
            g, h = random.choice(A2s), random.choice(A2s)
            note("L1 A2 agreement", op(M, g, h, j) == lift(M, g, h, j), (g, h, j))
            # L2: monotonicity in both arguments
            P2 = ang(P, R)       # P ⊑ P ⊔ R
            note("L2 monotone left", ref(op(M, P, Q, j), op(M, P2, Q, j)), (P, P2, Q, j))
            note("L2 monotone right", ref(op(M, Q, P, j), op(M, Q, P2, j)), (Q, P, P2, j))
            # L4: distribution over ⊔ and ⊓
            note("L4 ⊔-dist right", op(M, P, ang(Q, R), j) == ang(op(M, P, Q, j), op(M, P, R, j)),
                 (P, Q, R, j))
            note("L4 ⊔-dist left", op(M, ang(Q, R), P, j) == ang(op(M, Q, P, j), op(M, R, P, j)),
                 (Q, R, P, j))
            note("L4 ⊓-dist right", op(M, P, dem(Q, R), j) == dem(op(M, P, Q, j), op(M, P, R, j)),
                 (P, Q, R, j))
            note("L4 ⊓-dist left", op(M, dem(Q, R), P, j) == dem(op(M, Q, P, j), op(M, R, P, j)),
                 (Q, R, P, j))
            note("  (P∥Q)⊔(P∥R) ⊑ P∥(Q⊔R)",
                 ref(ang(op(M, P, Q, j), op(M, P, R, j)), op(M, P, ang(Q, R), j)), (P, Q, R, j))
            note("  P∥(Q⊓R) ⊑ (P∥Q)⊓(P∥R)",
                 ref(op(M, P, dem(Q, R), j), dem(op(M, P, Q, j), op(M, P, R, j))), (P, Q, R, j))
            # L5: Miracle zero (always); Chaos zero for total merges, feasible partner
            note("L5 Miracle zero", op(M, 0, P, j) == 0 and op(M, P, 0, j) == 0, (P, j))
            if is_total(j):
                Pf = random.choice(feas)
                note("L5 Chaos zero (total j)", op(M, BOT, Pf, j) is BOT, (Pf, j))
            if is_sym(j):
                note("L5 commutative (symmetric j)", op(M, P, Q, j) == op(M, Q, P, j), (P, Q, j))
            # L6: A2 closure
            note("L6 A2 closure", M.is_A2(op(M, g, h, j)), (g, h, j))
        res[name] = (r, cex)
    return res


def print_suite(M, res, label):
    print(f"\n--- {label} ---")
    for name, (r, cex) in res.items():
        for key, ok in r.items():
            c = None
            if not ok:
                args = cex[key]
                c = "  ".join(M.show(a) if not isinstance(a, list) else f"j={a}" for a in args)
            report(f"{name:9s} {key}", ok, c)


def assoc_suite(M, ops, merges, samples, divergence):
    vals = ([BOT] if divergence else []) + M.fams
    out = {}
    for name, op in ops.items():
        ok, cex = True, None
        for _ in range(samples):
            j = random.choice(merges)
            P, Q, R = random.choice(vals), random.choice(vals), random.choice(vals)
            if op(M, op(M, P, Q, j), R, j) != op(M, P, op(M, Q, R, j), j):
                ok = False
                cex = (P, Q, R, j)
                break
        out[name] = (ok, cex)
    return out


def part_A():
    print("=" * 70)
    print("A. Abstract model")
    print("=" * 70)

    # A0: F's blocker form is the join over A2 refinement-lower-bounds,
    #     F is below the lift, and F is the least monotone A2-agreeing operator
    for n in (2, 3):
        M = Abs(n)
        vals = [BOT] + M.fams
        ok_kan = ok_below = True
        for _ in range(4000):
            j = rand_merge(n, random.choice(["fun", "pfun", "rel", "prel"]))
            P, Q = random.choice(vals), random.choice(vals)
            if Fop(M, P, Q, j) != Fkan(M, P, Q, j):
                ok_kan = False
            if not ref(Fop(M, P, Q, j), lift(M, P, Q, j)):
                ok_below = False
        report(f"n={n}: blocker form of F = join of g∥h over A2 g ⊑ P, h ⊑ Q (4000 samples)", ok_kan)
        report(f"n={n}: F ⊑ lift (4000 samples)", ok_below)
        # for a functional merge, F is the dual of the lift on the dual operands
        dual = lambda f: sum(1 << G for G in M.subs if all(G & X for X in M.members(f)))
        feas = [f for f in M.fams if f]
        ok_dual = True
        for _ in range(2000):
            j = rand_merge(n, "fun")
            P, Q = random.choice(feas), random.choice(feas)
            if Fop(M, P, Q, j) != dual(lift(M, dual(P), dual(Q), j)):
                ok_dual = False
        report(f"n={n}: functional j: F(P,Q) = b(lift(b P, b Q)), b the blocker (2000 samples)", ok_dual)

    # A1: law suites
    M2 = Abs(2)
    merges2 = [[[a, b], [c, d]] for a in range(4) for b in range(4) for c in range(4) for d in range(4)]
    ops = dict(OPS)
    ops["GIVEUP (c)"] = make_giveup(1)
    print_suite(M2, law_suite(M2, ops, merges2, 40000, "n=2"), "n = 2, all 256 merges, 40000 samples")
    M3 = Abs(3)
    merges3 = [rand_merge(3, k, s) for k in ("fun", "pfun", "rel", "prel") for s in (False, True)
               for _ in range(40)]
    ops3 = dict(OPS)
    ops3["GIVEUP (c)"] = make_giveup(2)
    print_suite(M3, law_suite(M3, ops3, merges3, 40000, "n=3"), "n = 3, 320 random merges, 40000 samples")

    # A2: associativity by merge class
    print("\n--- L5 associativity, symmetric associative merges ---")
    sym3 = [j for j in all_sym_merges(3) if is_assoc(j)]
    classes = {
        "functional total": [j for j in sym3 if is_fun(j)],
        "functional partial": [j for j in sym3 if all(popcount(v) <= 1 for r in j for v in r)
                               and not is_total(j)],
        "relational total": [j for j in sym3 if is_total(j) and not is_fun(j)],
        "relational partial": [j for j in sym3 if not is_total(j)
                               and not all(popcount(v) <= 1 for r in j for v in r)],
    }
    print("symmetric associative merges on 3 states: "
          + ", ".join(f"{k} {len(v)}" for k, v in classes.items()))
    for cls, ms in classes.items():
        for div in (False, True):
            if not ms:
                continue
            out = assoc_suite(M3, OPS, ms, 6000, div)
            for name, (ok, cex) in out.items():
                c = None
                if not ok:
                    P, Q, R, j = cex
                    c = f"P={M3.show(P)} Q={M3.show(Q)} R={M3.show(R)} j={j}"
                report(f"{name:9s} associative, {cls}, {'with' if div else 'no'} Chaos", ok, c)

    # A3: the named counterexample for the lift with a nondeterministic merge
    M = Abs(2)
    j = [[0b01, 0b10], [0b10, 0b11]]  # j(0,x) = {x}, j(1,1) = {0,1}
    P = Q = M.point(1)
    R = ang(M.point(0), M.point(1))
    for name, op in OPS.items():
        l, r = op(M, op(M, P, Q, j), R, j), op(M, P, op(M, Q, R, j), j)
        report(f"{name:9s} assoc on j(0,x)={{x}}, j(1,1)={{0,1}}, P=Q=⟨1⟩, R=⟨0⟩⊔⟨1⟩:"
               f" {M.show(l)} vs {M.show(r)}", l == r)

    # A4: interchange obstruction, frame-disjoint merge on {0,1}²
    print("\n--- Interchange: no operator agreeing on points is ⊔- and ⊓-distributive ---")
    names = ["00", "01", "10", "11"]
    M = Abs(4, names, enumerate_all=False)
    st = lambda u, v: 2 * u + v
    jfd = [[1 << st(x >> 1, y & 1) for y in range(4)] for x in range(4)]
    s0 = st(0, 0)
    xset = lambda u: M.point(st(u, 0))      # left branch: x := u
    yset = lambda v: M.point(st(0, v))      # right branch: y := v
    P = ang(xset(0), xset(1))               # angelic on x
    Q = dem(yset(0), yset(1))               # demonic on y
    pts_ok = all(lift(M, xset(u), yset(v), jfd) == M.point(st(u, v)) for u in (0, 1) for v in (0, 1))
    report("points: (x := u) ∥ (y := v) = (x,y) := (u,v) for the lift", pts_ok)
    angdem = ang(dem(M.point(st(0, 0)), M.point(st(0, 1))), dem(M.point(st(1, 0)), M.point(st(1, 1))))
    demang = dem(ang(M.point(st(0, 0)), M.point(st(1, 0))), ang(M.point(st(0, 1)), M.point(st(1, 1))))
    report(f"⊔_u ⊓_v ⟨u,v⟩ = {M.show(angdem)}  ≠  ⊓_v ⊔_u ⟨u,v⟩ = {M.show(demang)}", angdem != demang)
    report(f"lift(P,Q) = ⊓_v ⊔_u ⟨u,v⟩ (demon first)", lift(M, P, Q, jfd) == demang)
    report(f"F(P,Q)    = ⊔_u ⊓_v ⟨u,v⟩ (angel first)", Fop(M, P, Q, jfd) == angdem)

    # A5: the AD equality-merge example: monotone + point agreement force Miracle
    print("\n--- AD equality merge: x:=1 ∥ (x:=1 ⊔ x:=2) ---")
    M = Abs(3, ["1", "2", "δ"])
    jeq = [[(1 << x) if x == y else 0 for y in range(3)] for x in range(3)]
    p1, p2 = M.point(0), M.point(1)
    for name, op in list(OPS.items()) + [("GIVEUP (c)", make_giveup(2))]:
        v = op(M, p1, ang(p1, p2), jeq)
        print(f"  {name:9s} x:=1 ∥ (x:=1 ⊔ x:=2) = {M.show(v)}")
    report("x:=1 ∥ x:=2 = Miracle for the lift, so every monotone point-agreeing ∥ gives Miracle",
           lift(M, p1, p2, jeq) == 0)
    report("MIN breaks monotonicity: x:=2 ⊑ x:=1 ⊔ x:=2 but x:=2 ∥ x:=1 = Miracle ⋢ x:=1",
           not ref(MINop(M, p2, p1, jeq), MINop(M, ang(p1, p2), p1, jeq)))


# =====================================================================
# B. Reactive model (RAD observations after a started, non-waiting prior)
# =====================================================================
SIG = ("a", "b")
REFS = [frozenset(c) for k in range(3) for c in itertools.combinations(SIG, k)]
LMAX = 2


def traces(L):
    return [t for k in range(L + 1) for t in itertools.product(SIG, repeat=k)]


def obs_str(o):
    w, t, r = o
    return f"{'w' if w else 't'}{''.join(t) or 'ε'}/{''.join(sorted(r)) or '∅'}"


STOP = frozenset((True, (), r) for r in REFS)
SKIP = frozenset((False, (), r) for r in REFS)
NOOBS = frozenset()


def prefix(e, P):
    return frozenset({(True, (), r) for r in REFS if e not in r}
                     | {(w, (e,) + t, r) for (w, t, r) in P if len(t) + 1 <= LMAX})


def ext(P, Q):
    stop = lambda o: o[0] and o[1] == ()
    return frozenset(o for o in P | Q if not stop(o) or (o in P and o in Q))


def minimize(S):
    S = sorted(set(S), key=len)
    out = []
    for X in S:
        if not any(Y <= X for Y in out):
            out.append(X)
    return frozenset(out)


def fam(P):
    return frozenset(frozenset([o]) for o in P)


def fang(A, B):
    return minimize({X | Y for X in A for Y in B})


def fdem(A, B):
    return minimize(A | B)


def fref(A, B):
    """A ⊑ B: every set B offers contains a set A offers."""
    return all(any(X <= Y for X in A) for Y in B)


def min_transversals(E):
    cur = {frozenset()}
    for e in E:
        nxt = set()
        for T in cur:
            if T & e:
                nxt.add(T)
            else:
                for v in e:
                    nxt.add(T | {v})
        cur = set(minimize(nxt))
    return frozenset(cur)


@lru_cache(maxsize=None)
def jsync(x, y):
    if x[1] != y[1]:
        return frozenset()
    return frozenset([(x[0] or y[0], x[1], x[2] | y[2])])


def rlift(A, B, j=jsync):
    out = set()
    for X in A:
        for Y in B:
            E = [j(x, y) for x in X for y in Y]
            if all(E):
                out |= min_transversals(E)
    return minimize(out)


def rF(A, B, j=jsync):
    edges = []
    for G in min_transversals(list(A)):
        for H in min_transversals(list(B)):
            im = frozenset().union(*[j(g, h) for g in G for h in H]) if G and H else frozenset()
            if not im:
                return frozenset()
            edges.append(im)
    return minimize(min_transversals(edges))


def rMIN(A, B, j=jsync):
    out = set()
    for X in A:
        for Y in B:
            E = [j(x, y) for x in X for y in Y if j(x, y)]
            if E:
                out |= min_transversals(E)
    return minimize(out)


def lcp(s, t):
    k = 0
    while k < min(len(s), len(t)) and s[k] == t[k]:
        k += 1
    return s[:k]


def rGIVEUP(A, B, j=jsync):
    out = set()
    for X in A:
        for Y in B:
            angelic = len(X) > 1 or len(Y) > 1
            E, ok = [], True
            for x in X:
                for y in Y:
                    m = j(x, y)
                    if m:
                        E.append(m)
                    elif angelic:
                        E.append(frozenset([(True, lcp(x[1], y[1]), frozenset(SIG))]))
                    else:
                        ok = False
            if ok:
                out |= min_transversals(E)
    return minimize(out)


ROPS = {"lift (e)": rlift, "F (b)": rF, "MIN (a)": rMIN, "GIVEUP (c)": rGIVEUP}


def obs_of(A):
    """Observations of an A2 family (its singleton offers)."""
    return frozenset(next(iter(X)) for X in A if len(X) == 1)


def is_rA2(A):
    return A == fam(obs_of(A))


DETS = None


def det_obs(T, term):
    """Deterministic process with prefix-closed trace set T; term = ✓-leaves."""
    out = set()
    for t in T:
        init = {e for e in SIG if t + (e,) in T}
        if t in term:
            if init:
                return None
            out |= {(False, t, r) for r in REFS}
        else:
            out |= {(True, t, r) for r in REFS if not (r & init)}
    return frozenset(out)


def get_dets():
    global DETS
    if DETS is None:
        trs = traces(LMAX)
        DETS = []
        for k in range(1 << len(trs)):
            T = frozenset(trs[i] for i in bits(k))
            if () not in T or any(t[:-1] not in T for t in T if t):
                continue
            leaves = [t for t in T if not any(t + (e,) in T for e in SIG)]
            for m in range(1 << len(leaves)):
                term = frozenset(leaves[i] for i in bits(m))
                o = det_obs(T, term)
                if o is not None:
                    DETS.append((T, term, o))
    return DETS


def dets_in(G):
    return [o for (T, m, o) in get_dets() if o <= G]


def covered(P):
    """P is the ⊓ of its deterministic refinements (false for Skip inside □)."""
    return frozenset().union(*dets_in(P)) == P


def rand_csp(d):
    """A random CSP term of depth d: (observations, text)."""
    k = random.randrange(5) if d else 0
    if k == 0:
        return random.choice([(STOP, "Stop"), (SKIP, "Skip")])
    if k in (1, 2):
        e = random.choice(SIG)
        P, s = rand_csp(d - 1)
        return prefix(e, P), f"{e}→{s}"
    (P, s), (Q, t) = rand_csp(d - 1), rand_csp(d - 1)
    if k == 3:
        return P | Q, f"({s} ⊓ {t})"
    return ext(P, Q), f"({s} □ {t})"


def rand_cov(d):
    while True:
        P, s = rand_csp(d)
        if covered(P):
            return P, s


def rand_proc(d):
    """A CSP term, or ⊓ or ⊔ of two: (family, text)."""
    k = random.randrange(4)
    (P, s), (Q, t) = rand_cov(d), rand_cov(d)
    if k == 0:
        return fam(P), s
    if k == 1:
        return fdem(fam(P), fam(Q)), f"({s} ⊓ {t})"
    return fang(fam(P), fam(Q)), f"({s} ⊔ {t})"


def minimal_sets(S):
    S = set(S)
    return [X for X in S if not any(Y < X for Y in S)]


def rH(A, B, j=jsync):
    """Demon first with deterministic atoms: ⊓ over deterministic refinements
    d_G of each blocker G of A (and e_H of B) of ⊔_{G,H} d_G ∥ e_H."""
    if not A or not B:
        return frozenset()
    choices = []
    for F in (A, B):
        ds = [dets_in(G) for G in min_transversals(list(F))]
        if not all(ds):
            return None
        choices.append(minimal_sets(frozenset(f) for f in itertools.product(*ds)))
    out = set()
    for SA in choices[0]:
        for SB in choices[1]:
            term = None
            for d in SA:
                for e in SB:
                    v = rlift(fam(d), fam(e), j)
                    term = v if term is None else fang(term, v)
            out |= term
    return minimize(out)


@lru_cache(maxsize=None)
def interleavings(s, t):
    if not s:
        return frozenset([t])
    if not t:
        return frozenset([s])
    return frozenset({(s[0],) + u for u in interleavings(s[1:], t)}
                     | {(t[0],) + u for u in interleavings(s, t[1:])})


@lru_cache(maxsize=None)
def jinter(x, y):
    """Interleaving: any interleaving of the traces, refusals intersect."""
    return frozenset((x[0] or y[0], t, x[2] & y[2]) for t in interleavings(x[1], y[1]))


def show_fam(A, limit=6):
    if not A:
        return "Miracle"
    sets = sorted(("{" + " ".join(sorted(map(obs_str, X))) + "}" for X in A), key=len)
    more = f" …(+{len(sets) - limit})" if len(sets) > limit else ""
    return "↑{" + " ".join(sets[:limit]) + more + "}"


def part_B():
    print("\n" + "=" * 70)
    print("B. Reactive model, jsync, events {a,b}, traces up to length 2")
    print("   observations: w = waiting, t = terminated, then trace / refusal")
    print("=" * 70)
    ROPS["H (f)"] = rH
    a, b = prefix("a", SKIP), prefix("b", SKIP)
    A, B, S = fam(a), fam(b), fam(STOP)
    ANG, DEM, EXT = fang(A, B), fdem(A, B), fam(ext(a, b))
    aMir = fam(prefix("a", NOOBS))
    aOrStop = fang(A, S)

    report("a→Skip ∥ a→Skip = a→Skip", rlift(A, A) == A)
    report("a→Skip ∥ b→Skip = Stop", rlift(A, B) == S)
    report("a→Skip ⊔ Stop ⊑ a→Miracle, strictly", fref(aOrStop, aMir) and aOrStop != aMir)
    report("a→Skip ⊑ a→Skip ⊔ Stop, strictly (Stop ⋢ a→Skip)", fref(A, aOrStop) and A != aOrStop)
    print("\n  a→Skip ∥ (a→Skip ⊔ b→Skip):")
    for name, op in ROPS.items():
        v = op(A, ANG)
        tag = ("a→Miracle" if v == aMir else "a→Skip ⊔ Stop" if v == aOrStop
               else "a→Skip" if v == A else show_fam(v))
        print(f"    {name:10s} = {tag}")
    report("lift: = a→Miracle (rad_sync_angelic_miracle)", rlift(A, ANG) == aMir)
    report("MIN: = a→Skip ⊓ Stop, the demonic answer", rMIN(A, ANG) == fdem(A, S))
    gv = obs_of(rGIVEUP(A, ANG))
    report("GIVEUP: never performs a, and its refusals are not subset-closed",
           is_rA2(rGIVEUP(A, ANG)) and all(o[0] and o[1] == () for o in gv)
           and (True, (), frozenset(SIG)) in gv and (True, (), frozenset("a")) not in gv)
    report("F and H: = (a∥a) ⊔ (a∥b) = a→Skip ⊔ Stop",
           rF(A, ANG) == rH(A, ANG) == fang(rlift(A, A), rlift(A, B)) == aOrStop)
    report("baseline: a→Skip ∥ (a→Skip □ b→Skip) = a→Skip", rlift(A, EXT) == A)
    report("demonic: a→Skip ∥ (a→Skip ⊓ b→Skip) = a→Skip ⊓ Stop", rlift(A, DEM) == fdem(A, S))
    print("\n  monotonicity instance b→Skip ⊑ a→Skip ⊔ b→Skip:")
    for name, op in ROPS.items():
        report(f"    {name:10s} a∥b ⊑ a∥(a⊔b)", fref(op(A, B), op(A, ANG)))

    print("\n  the angel against a demonic partner: (a→Skip ⊓ b→Skip) ∥ (a→Skip ⊔ b→Skip)")
    informed = fdem(fang(A, S), fang(S, B))     # (a ⊔ Stop) ⊓ (Stop ⊔ b)
    blind = fang(fdem(A, S), fdem(S, B))        # (a ⊓ Stop) ⊔ (Stop ⊓ b)
    for name, op in ROPS.items():
        v = op(DEM, ANG)
        tag = ("(a⊔Stop) ⊓ (Stop⊔b)" if v == informed else "(a⊓Stop) ⊔ (Stop⊓b)" if v == blind
               else show_fam(v, 3))
        print(f"    {name:10s} = {tag}")
    report("F(a⊔b, a⊓b) ≠ F(a⊔b, a) ⊓ F(a⊔b, b): F is not ⊓-distributive",
           rF(ANG, DEM) != fdem(rF(ANG, A), rF(ANG, B)) and fdem(rF(ANG, A), rF(ANG, B)) == informed)
    report("H(a⊓b, a⊔b) ≠ H(a, a⊔b) ⊓ H(b, a⊔b): H is not ⊓-distributive",
           rH(DEM, ANG) != fdem(rH(A, ANG), rH(B, ANG)))
    report("  because a□b ⊒ a⊓b is a deterministic refinement: H adds (a□b)∥(a⊔b) = a ⊔ b",
           rH(DEM, ANG) == fdem(informed, ANG))

    # random law checks
    print("\n--- random processes: a CSP term of depth 1, or ⊓ / ⊔ of two (jsync) ---")
    results = {n: {} for n in ROPS}
    cexs = {n: {} for n in ROPS}
    N = 250
    for _ in range(N):
        (P, ps), (Q, qs), (R, rs) = rand_proc(1), rand_proc(1), rand_proc(1)
        (g, gs), (h, hs) = rand_cov(1), rand_cov(1)
        g, h = fam(g), fam(h)
        for name, op in ROPS.items():
            def note(key, ok, c):
                results[name][key] = results[name].get(key, True) and ok
                if not ok and (key not in cexs[name] or len(c) < len(cexs[name][key])):
                    cexs[name][key] = c
            note("L1 A2 agreement", op(g, h) == rlift(g, h), f"P={gs}, Q={hs}")
            note("L2 monotone", fref(op(P, Q), op(fang(P, R), Q)), f"P={ps} ⊑ P⊔R, R={rs}, Q={qs}")
            note("L4 ⊔-dist", op(P, fang(Q, R)) == fang(op(P, Q), op(P, R)), f"P={ps}, Q={qs}, R={rs}")
            note("L4 ⊓-dist", op(P, fdem(Q, R)) == fdem(op(P, Q), op(P, R)), f"P={ps}, Q={qs}, R={rs}")
            note("L5 commutative", op(P, Q) == op(Q, P), f"P={ps}, Q={qs}")
            note("L5 associative", op(op(P, Q), R) == op(P, op(Q, R)), f"P={ps}, Q={qs}, R={rs}")
            note("L6 A2 closure", is_rA2(op(g, h)), f"P={gs}, Q={hs}")
    for name in ROPS:
        for key, ok in results[name].items():
            report(f"{name:10s} {key} ({N} samples)", ok, cexs[name].get(key))

    print("\n--- associativity with the interleaving merge (relational, associative) ---")
    for name, op in (("lift (e)", rlift), ("F (b)", rF)):
        ok, cex, done, skipped = True, None, 0, 0
        while done < 150:
            (P, ps), (Q, qs), (R, rs) = rand_proc(1), rand_proc(1), rand_proc(1)
            PQ, QR = op(P, Q, jinter), op(Q, R, jinter)
            if len(PQ) > 40 or len(QR) > 40:     # keep the blocker computations small
                skipped += 1
                continue
            done += 1
            if op(PQ, R, jinter) != op(P, QR, jinter):
                c = f"P={ps}, Q={qs}, R={rs}"
                if cex is None or len(c) < len(cex):
                    ok, cex = False, c
        report(f"{name:10s} associative under interleaving (150 samples, {skipped} large skipped)", ok, cex)


# =====================================================================
# C. Demon-first unresolved angelic choice (candidate d) on CSP processes
# =====================================================================
def boxplus(P, Q):
    """⊓ over deterministic refinements p, q of the deterministic process with
    the union of their traces; conflict when one terminates where the other
    continues."""
    out, conflict = set(), False
    dp = [(T, m) for (T, m, o) in get_dets() if o <= P]
    dq = [(T, m) for (T, m, o) in get_dets() if o <= Q]
    for T1, m1 in dp:
        for T2, m2 in dq:
            o = det_obs(T1 | T2, m1 | m2)
            if o is None:
                conflict = True
            else:
                out |= o
    return frozenset(out), conflict


def part_C():
    print("\n" + "=" * 70)
    print("C. Unresolved angelic choice ⊞ (demon-first), CSP parallel = lift on A2")
    print("=" * 70)
    a, b = prefix("a", SKIP), prefix("b", SKIP)
    par = lambda P, Q: obs_of(rlift(fam(P), fam(Q)))
    bp = lambda P, Q: boxplus(P, Q)[0]
    report("a→Skip ∥ (a→Skip ⊞ b→Skip) = a→Skip", par(a, bp(a, b)) == a)
    report("a→Skip ⊞ b→Skip = a→Skip □ b→Skip (distinct initials)", bp(a, b) == ext(a, b))
    report("⊞ is not an upper bound: a→Skip ⋢ a→Skip ⊞ b→Skip", not (bp(a, b) <= a))
    aab = prefix("a", prefix("b", STOP))
    report("a→Stop ⊞ a→b→Stop = a→b→Stop (shared event a stays unresolved)",
           bp(prefix("a", STOP), aab) == aab)
    report("a→Stop □ a→b→Stop = a→(Stop ⊓ b→Stop)",
           ext(prefix("a", STOP), aab) == prefix("a", STOP | prefix("b", STOP)))
    ok_mono = ok_box = ok_sub = ok_ext = ok_det = True
    cex_dist = None
    skipped = 0
    dets = get_dets()
    for _ in range(500):
        (P, ps), (Q, qs), (R, rs) = rand_cov(2), rand_cov(2), rand_cov(2)
        QR, c1 = boxplus(Q, R)
        PQ, PR = par(P, Q), par(P, R)
        rhs, c2 = boxplus(PQ, PR)
        if c1 or c2:
            skipped += 1
            continue
        ds = dets_in(P)
        P2 = frozenset().union(*random.sample(ds, random.randint(1, len(ds))))  # P ⊑ P2
        if not bp(P2, Q) <= bp(P, Q):
            ok_mono = False
        lhs = par(P, QR)
        if lhs != rhs:
            ok_box = False
            c = f"P={ps}, Q={qs}, R={rs}"
            if cex_dist is None or len(c) < len(cex_dist):
                cex_dist = c
        if not lhs <= rhs:
            ok_sub = False
        if not bp(P, Q) <= ext(P, Q):
            ok_ext = False
        d = random.choice(ds)
        dq, c3 = boxplus(par(d, Q), par(d, R))
        if not c3 and par(d, QR) != dq:
            ok_det = False
    print(f"  500 samples of depth-2 terms; {skipped} skipped (one branch terminates where the other continues)")
    report("⊞ monotone", ok_mono)
    report("□ ⊑ ⊞", ok_ext)
    report("P ∥ (Q ⊞ R) = (P∥Q) ⊞ (P∥R) on the random samples (the named case below fails)", ok_box, cex_dist)
    report("(P∥Q) ⊞ (P∥R) ⊑ P ∥ (Q ⊞ R)", ok_sub)
    report("P ∥ (Q ⊞ R) = (P∥Q) ⊞ (P∥R) for deterministic P", ok_det)
    Pn, bS = a | b, b
    report("named: P = a→Skip ⊓ b→Skip, Q = a→Skip, R = b→Skip breaks ⊞-distribution",
           par(Pn, bp(a, bS)) != bp(par(Pn, a), par(Pn, bS)))


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
