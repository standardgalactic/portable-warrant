"""Disposition Lab: a small executable reference for The Calculus of Disposition.

Implements the ledger semantics (records, the lifecycle step function delta,
replay), enumerates every admissible ledger up to a bound, and provides the
book's three instruments:

  * Disposition Worlds  - finite pointed worlds, satisfaction, countermodel search
  * History Twins       - pairs of worlds equal under one lens, distinct under another
  * Causal Shuffles     - all linearizations of a world's dependence order

It also runs exhaustive checks of the book's untyped theorems over the
enumerated ledgers, a perturbation mode, and the witness mixer.

Run:  python3 disposition_lab.py [max_events]
"""

import itertools
import sys
from functools import lru_cache

# ---------------------------------------------------------------- the model

PRINCIPALS = ("a1", "a2")
# Fixed policy: a1 binds, collapses, compensates, refuses;
# a2 verifies, collapses, refuses.
POLICY = {
    ("a1", "bind"), ("a1", "collapse"), ("a1", "compensate"), ("a1", "refuse"),
    ("a2", "verify"), ("a2", "collapse"), ("a2", "refuse"), ("a2", "discharge"),
    ("a1", "clock"),
}
T = "t1"           # the single declared deadline interval
OMEGA = "w1"       # the single external obligation each commitment may await
IDS = ("c1", "c2")
Q = "q"
B = "b"
F = "inc"          # the only transformation: inc(b) = v
V = "v"
R = "r0"           # the only explicit refusal reason
K = "val"          # the only observation rule: observe_val(v) = v


def evaluate(f, b):
    return V if (f, b) == (F, B) else None


def good_witness(c, v):
    return ("w", c, v)


BAD_WITNESS = ("w", "bad")


def failure_certificate(c, v):
    """An authenticated failure certificate issued by the verifier on (c, v)."""
    return ("cert", "g", "k1", c, v)


def check_failure(phi, c, v):
    """Authentication check on a certificate; does not rerun the verifier."""
    return phi == ("cert", "g", "k1", c, v)


def discharge_certificate(c, omega):
    return ("cert", "env", "k1", c, omega, "discharged")


def check_discharge(phi, c, omega):
    return phi == ("cert", "env", "k1", c, omega, "discharged")


def timeout_certificate(c, omega, t):
    return ("cert", "clock", "k1", c, (omega, t), "expired")


def check_timeout(phi, c, omega, t):
    return phi == ("cert", "clock", "k1", c, (omega, t), "expired")


def valid(w, c, v):
    """Index-sensitive validity: a witness is valid only for its own (c, v)."""
    return w == ("w", c, v)


def observe(k, v):
    return v if k == K else None


def may(a, kind):
    return (a, kind) in POLICY


# Records are tuples; the first field is the constructor.
#  ("Pop", c, q)  ("Comp", a, c, q, d)  ("Bind", a, c, b)
#  ("Trans", c, f, b, v)  ("Ver", a, c, v, w)  ("Ref", a, c, r)
#  ("Col", a, c, k, w, o)

# ("Dis", a, c, omega, phi) records an authenticated discharge on c.

def subj(rec):
    return rec[1] if rec[0] in ("Pop", "Trans") else rec[2]   # VF, TO, Dis: rec[2]


def pred(rec):
    return rec[4] if rec[0] == "Comp" else None


LAB_VERSION = "4 (verificationFailed state, certificates, discharge, timeout)"


def is_vf(r):
    """Retained for reports: v4 has no reserved refusal reasons."""
    return False


LIVE = {"open", "bound", "transformed", "verified", "failed"}   # failed = verificationFailed
TERMINAL = {"refused", "collapsed"}


def delta(state, rec):
    """The lifecycle step function of the Ledger Path Lemma chapter.
    States are tuples (kind, data...). Returns the new state or None (undefined)."""
    tag = rec[0]
    if state is None:
        if tag == "Pop":
            return ("open", rec[2])
        if tag == "Comp":
            return ("open", rec[3])
        return None
    kind = state[0]
    if tag == "Bind" and kind == "open":
        return ("bound", state[1], rec[3])
    if tag == "Trans" and kind == "bound" and rec[3] == state[2]:
        return ("transformed", rec[3], rec[4])
    if tag == "Ver" and kind == "transformed" and rec[3] == state[2]:
        return ("verified", rec[3], rec[4]) if valid(rec[4], rec[2], rec[3]) else None
    if tag == "Dis":
        return state if kind in LIVE and check_discharge(rec[4], rec[2], rec[3]) else None
    if tag == "TO":
        return state if kind in LIVE and check_timeout(rec[5], rec[2], rec[3], rec[4]) else None
    if tag == "VF":
        if kind == "transformed" and rec[3] == state[2] and check_failure(rec[4], rec[2], rec[3]):
            return ("failed", rec[3], rec[4])
        return None
    if tag == "Ref" and kind in LIVE:
        return ("refused", rec[3])
    if tag == "Col" and kind == "verified" and rec[4] == state[2]:
        return ("collapsed", rec[5]) if rec[5] == observe(rec[3], state[1]) else None
    return None


def apply(X, rec):
    """Replay step. X = (A, O, D): A a frozen dict (tuple of pairs), O the
    observations, D the (commitment, obligation) pairs already discharged.
    None = undefined."""
    if X is None:
        return None
    A, O, D = dict(X[0]), set(X[1]), set(X[2])
    if rec[0] in ("Dis", "TO"):
        if (rec[2], rec[3]) in D:       # an obligation is settled at most once
            return None
        D.add((rec[2], rec[3]))
    s = subj(rec)
    if rec[0] == "Comp":
        d = pred(rec)
        if d not in A or A[d][0] not in TERMINAL:
            return None
    new = delta(A.get(s), rec)
    if new is None:
        return None
    A[s] = new
    if rec[0] == "Col":
        O.add((s, rec[3], rec[5]))
    return (tuple(sorted(A.items())), frozenset(O), frozenset(D))


EMPTY = ((), frozenset(), frozenset())


def replay(H, X=EMPTY):
    for rec in H:
        X = apply(X, rec)
        if X is None:
            return None
    return X


# ------------------------------------------------- enumerating admissible ledgers

def enabled(X):
    """All records an authorized, maximally nondeterministic process could append.
    This is the operational semantics of the Labelled Disposition Semantics chapter
    read at the level of records, with the process layer abstracted away."""
    A = dict(X[0])
    out = []
    fresh = [c for c in IDS if c not in A]
    if fresh:
        c = fresh[0]            # canonical fresh identity (equivariance)
        out.append(("Pop", c, Q))
        for d, st in A.items():
            if st[0] in TERMINAL:
                for a in PRINCIPALS:
                    if may(a, "compensate"):
                        out.append(("Comp", a, c, Q, d))
    D = X[2]
    for c, st in A.items():
        kind = st[0]
        if kind in LIVE and (c, OMEGA) not in D:
            out += [("Dis", a, c, OMEGA, discharge_certificate(c, OMEGA))
                    for a in PRINCIPALS if may(a, "discharge")]
            out += [("TO", a, c, OMEGA, T, timeout_certificate(c, OMEGA, T))
                    for a in PRINCIPALS if may(a, "clock")]
        if kind == "open":
            out += [("Bind", a, c, B) for a in PRINCIPALS if may(a, "bind")]
        if kind == "bound":
            v = evaluate(F, st[2])
            if v is not None:
                out.append(("Trans", c, F, st[2], v))
        if kind == "transformed":
            v = st[2]
            for a in PRINCIPALS:
                if may(a, "verify"):
                    out.append(("Ver", a, c, v, good_witness(c, v)))
                    # failing verification: a certified negative result; c stays live
                    out.append(("VF", a, c, v, failure_certificate(c, v)))
        if kind == "verified":
            v, w = st[1], st[2]
            out += [("Col", a, c, K, w, observe(K, v)) for a in PRINCIPALS if may(a, "collapse")]
        if kind in LIVE:
            out += [("Ref", a, c, R) for a in PRINCIPALS if may(a, "refuse")]
    return out


def all_ledgers(n):
    """Every admissible ledger of length <= n, as tuples of records."""
    result = [()]
    frontier = [((), EMPTY)]
    for _ in range(n):
        nxt = []
        for H, X in frontier:
            for rec in enabled(X):
                X2 = apply(X, rec)
                assert X2 is not None, (H, rec)
                nxt.append((H + (rec,), X2))
        result += [H for H, _ in nxt]
        frontier = nxt
    return result


# -------------------------------------------------- dependence and linearization

def independent(r1, r2):
    s1, s2 = subj(r1), subj(r2)
    if s1 == s2:
        return False
    if pred(r1) == s2 or pred(r2) == s1:
        return False
    return True


def dependence_order(H):
    """Strict order on positions: transitive closure of dependent earlier->later."""
    n = len(H)
    lt = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if not independent(H[i], H[j]):
                lt[i][j] = True
    for k in range(n):
        for i in range(n):
            if lt[i][k]:
                for j in range(n):
                    if lt[k][j]:
                        lt[i][j] = True
    return lt


def linearizations(H, limit=5000):
    lt = dependence_order(H)
    n = len(H)
    out = []

    def rec(prefix, remaining):
        if len(out) >= limit:
            return
        if not remaining:
            out.append(tuple(H[i] for i in prefix))
            return
        for i in sorted(remaining):
            if all(not lt[j][i] for j in remaining if j != i):
                rec(prefix + [i], remaining - {i})

    rec([], frozenset(range(n)))
    return out


def downsets(H):
    lt = dependence_order(H)
    n = len(H)
    for mask in range(1 << n):
        xs = [i for i in range(n) if mask >> i & 1]
        if all(mask >> j & 1 for i in xs for j in range(n) if lt[j][i]):
            yield xs


# ------------------------------------------------------------- worlds and logic

class World:
    """A single-history pointed world: the events of H under its dependence order,
    with the current configuration the downset given by `upto` (default: all)."""

    def __init__(self, H):
        self.H = tuple(H)
        self.state = replay(self.H)

    def A(self):
        return dict(self.state[0])

    def O(self):
        return set(self.state[1])

    def commitments(self):
        return sorted({subj(r) for r in self.H})

    def principals(self):
        return sorted({r[1] for r in self.H if r[0] in ("Comp", "Bind", "Ver", "Ref", "Col")})

    def depth(self):
        lt = dependence_order(self.H)
        n = len(self.H)
        best = [1] * n
        for j in range(n):
            for i in range(j):
                if lt[i][j]:
                    best[j] = max(best[j], best[i] + 1)
        return max(best, default=0)

    def size_key(self):
        return (len(self.commitments()), len(self.H), len(self.principals()), self.depth())

    # atoms
    def kind(self, c):
        st = self.A().get(c)
        return st[0] if st else None

    def live(self, c):
        return self.kind(c) in LIVE

    def refused(self, c):
        return self.kind(c) == "refused"

    def collapsed(self, c):
        return self.kind(c) == "collapsed"

    def verified(self, c):
        return any(r[0] == "Ver" and r[2] == c for r in self.H)

    def binder(self, c):
        for r in self.H:
            if r[0] == "Bind" and r[2] == c:
                return r[1]
        return None


def extensions(H, bound):
    """All admissible extensions of H with at most `bound` events in total."""
    X = replay(H)
    out = [H]
    frontier = [(H, X)]
    while frontier:
        nxt = []
        for G, Y in frontier:
            if len(G) >= bound:
                continue
            for rec in enabled(Y):
                G2 = G + (rec,)
                nxt.append((G2, apply(Y, rec)))
        out += [G for G, _ in nxt]
        frontier = nxt
    return out


HORIZON = 4   # longest lifecycle path: open -> bound -> transformed -> verified -> terminal


def diamond(H, phi, bound=None):
    """<>phi: some admissible extension satisfies phi. The default horizon is
    len(H) + HORIZON, enough for any commitment to reach a terminal state, so a
    bounded search cannot report a false negative for single-commitment goals."""
    if bound is None:
        bound = len(H) + HORIZON
    return any(phi(World(G)) for G in extensions(H, bound))


def countermodel(phi, ledgers):
    """Smallest world (lexicographic: commitments, events, principals, depth)
    falsifying phi, or None."""
    bad = [World(H) for H in ledgers if not phi(World(H))]
    return min(bad, key=lambda w: (w.size_key(), repr(w.H)), default=None)


# ------------------------------------------------------------------ lenses

def lens_present(w):
    """Coarse: the multiset of observed values, ignoring which commitment."""
    return tuple(sorted(o for (_, _, o) in w.O()))


def lens_refusals(w):
    """Refusal-sensitive: which refusal and verification-failure records occurred
    (up to identity renaming)."""
    return tuple(sorted((r[0], r[3] if r[0] == "Ref" else "") for r in w.H if r[0] in ("Ref", "VF")))


def lens_authority(w):
    """Authority-sensitive: who performed each collapse."""
    return tuple(sorted(r[1] for r in w.H if r[0] == "Col"))


def lens_state(w):
    """The present commitment map, up to identity renaming (kinds only)."""
    return tuple(sorted(st[0] for st in w.A().values()))


def twins(lens_eq, lens_ne, ledgers, require=lambda w: True):
    """Smallest pair of worlds equal under lens_eq and distinct under lens_ne."""
    worlds = [w for w in (World(H) for H in ledgers if H) if require(w)]
    groups = {}
    for w in worlds:
        groups.setdefault(lens_eq(w), []).append(w)
    best = None
    for grp in groups.values():
        grp.sort(key=lambda w: (w.size_key(), repr(w.H)))
        for i, w1 in enumerate(grp):
            for w2 in grp[i + 1:]:
                if lens_ne(w1) != lens_ne(w2):
                    key = (len(w1.H) + len(w2.H), w1.size_key(), w2.size_key())
                    if best is None or key < best[0]:
                        best = (key, w1, w2)
    return None if best is None else (best[1], best[2])


# ------------------------------------------------------------------ checks

def path_lemma(H):
    """delta* of each projection equals replay's map entry."""
    A = dict(replay(H)[0])
    for c in {subj(r) for r in H}:
        st = None
        for r in H:
            if subj(r) == c:
                st = delta(st, r)
                if st is None:
                    return False
        if A.get(c) != st:
            return False
    return True


def terminal_exclusive(H):
    for c in {subj(r) for r in H}:
        proj = [r for r in H if subj(r) == c]
        terms = [i for i, r in enumerate(proj) if r[0] in ("Ref", "Col")]
        if len(terms) > 1 or (terms and terms[0] != len(proj) - 1):
            return False
    return True


def vf_unforgeable(H):
    """P-CertificateAuthentic: every VerificationFailed record follows a
    transformed state, carries an authentic certificate for that commitment
    and value, and names a principal with verification authority."""
    X = EMPTY
    for r in H:
        if r[0] == "VF":
            st = dict(X[0]).get(r[2])
            if not (st and st[0] == "transformed" and may(r[1], "verify")
                    and check_failure(r[4], r[2], st[2])):
                return False
        X = apply(X, r)
    return True


def failed_verification_live(H):
    """P-FailedVerificationLive: immediately after a VerificationFailed record
    the commitment is live, in the failed state."""
    X = EMPTY
    for r in H:
        X = apply(X, r)
        if r[0] == "VF" and dict(X[0]).get(r[2], ("?",))[0] != "failed":
            return False
    return True


def no_verifier_disposition(H):
    """P-NoVerifierDisposition: no terminal record is attributed to a principal
    lacking refusal or collapse authority, and no verification record (positive
    or negative) produces a terminal state."""
    X = EMPTY
    for r in H:
        X2 = apply(X, r)
        st = dict(X2[0]).get(subj(r))
        if r[0] in ("Ver", "VF") and st[0] in TERMINAL:
            return False
        if r[0] == "Ref" and not may(r[1], "refuse"):
            return False
        if r[0] == "Col" and not may(r[1], "collapse"):
            return False
        X = X2
    return True


def shuffle_ok(H):
    base = replay(H)
    lins = linearizations(H)
    return all(replay(L) == base for L in lins), len(lins)


def downsets_ok(H):
    """World admissibility: every configuration (downset) has a defined replay."""
    for xs in downsets(H):
        # any linearization of the downset; use ledger order restricted to it
        if replay(tuple(H[i] for i in xs)) is None:
            return False
    return True


def perturb(H):
    """Change exactly one thing in an admissible ledger; report what breaks."""
    reports = []
    for i, r in enumerate(H):
        if r[0] == "Ver":
            other = "c2" if r[2] == "c1" else "c1"
            G = H[:i] + (r[:4] + (good_witness(other, r[3]),),) + H[i + 1:]
            reports.append(("foreign witness at %d" % i, G))
        if r[0] == "Bind":
            G = H[:i] + (("Bind", "a2") + r[2:],) + H[i + 1:]
            reports.append(("unauthorized binder at %d" % i, G))
        if r[0] == "Col":
            G = H[:i] + (r[:4] + (BAD_WITNESS,) + r[5:],) + H[i + 1:]
            reports.append(("collapse cites wrong witness at %d" % i, G))
    for i in range(len(H) - 1):
        if not independent(H[i], H[i + 1]):
            G = H[:i] + (H[i + 1], H[i]) + H[i + 2:]
            reports.append(("swap dependent records %d,%d" % (i, i + 1), G))
    for i, r in enumerate(H):
        if r[0] == "VF":
            G = H[:i] + (r[:4] + (("cert", "forged"),),) + H[i + 1:]
            reports.append(("forged failure certificate at %d" % i, G))
    if H and H[0][0] == "Pop":
        G = H + (("Pop", H[0][1], Q),)
        reports.append(("reuse identity %s" % H[0][1], G))
    for i in range(len(H)):
        G = H[:i] + H[i + 1:]
        reports.append(("delete record %d" % i, G))
    out = []
    for name, G in reports:
        diag = diagnose(G)
        out.append((name, diag))
    return out


def diagnose(G):
    """Name the first record at which replay fails, and why; also flag authority."""
    X = EMPTY
    for i, r in enumerate(G):
        kinds = {"Bind": "bind", "Ver": "verify", "Col": "collapse", "Comp": "compensate",
                 "Dis": "discharge", "TO": "clock"}
        if r[0] in kinds and not may(r[1], kinds[r[0]]):
            return "record %d %s: principal %s lacks %s authority" % (i, r[0], r[1], kinds[r[0]])
        Y = apply(X, r)
        if Y is None:
            st = dict(X[0]).get(subj(r))
            return "record %d %s: delta undefined from state %s" % (i, r[0], st[0] if st else "bottom")
        X = Y
    return "no failure detected"


# ------------------------------------------------------------------ control

from fractions import Fraction

# Atomic interventions on the decision points of a single commitment c1.
# Each is a filter that removes some enabled records.
INTERVENTIONS = {
    "V+ (verification succeeds)": lambda r: r[0] != "VF",
    "V- (verification fails)":    lambda r: r[0] != "Ver",
    "a1 never refuses":           lambda r: not (r[0] == "Ref" and r[1] == "a1"),
    "a2 never refuses":           lambda r: not (r[0] == "Ref" and r[1] == "a2"),
    "a2 never collapses":         lambda r: not (r[0] == "Col" and r[1] == "a2"),
}


def enabled_c1(X, K):
    # Control concerns the principals' decisions; discharge is the environment's
    # and is excluded, so these figures are over the disposition records only.
    return [r for r in enabled(X) if subj(r) == "c1" and r[0] not in ("Dis", "TO")
            and all(INTERVENTIONS[k](r) for k in K)]


def completions(K):
    """All maximal admissible ledgers for the single commitment c1 under K."""
    out = []

    def go(H, X):
        nxt = enabled_c1(X, K)
        if not nxt:
            out.append(H)
            return
        for r in nxt:
            go(H + (r,), apply(X, r))

    go((), EMPTY)
    return out


def outcome(H):
    st = dict(replay(H)[0]).get("c1")
    return st[0] if st else "unopened"


def force(K, d):
    """d is inevitable: every maximal completion under K ends with c1 in state d."""
    return all(outcome(H) == d for H in completions(K))


def influence(K, d):
    """Probability that c1 ends in d under a uniform random scheduler, given K."""
    def go(X):
        nxt = enabled_c1(X, K)
        if not nxt:
            st = dict(X[0]).get("c1")
            return Fraction(1 if st and st[0] == d else 0)
        return sum(go(apply(X, r)) for r in nxt) / len(nxt)
    return go(EMPTY)


def min_forcing_sets(d):
    names = list(INTERVENTIONS)
    for size in range(len(names) + 1):
        found = [K for K in itertools.combinations(names, size) if force(K, d)]
        if found:
            return found
    return []


def control_report():
    print("== Disposition control (single commitment c1)")
    for d in ("collapsed", "refused"):
        print("  target %s:  influence with no intervention = %s"
              % (d, influence((), d)))
        for K in min_forcing_sets(d):
            print("    minimal forcing set: {%s}" % ", ".join(K))
    print("  influence without forcing (target collapsed):")
    names = list(INTERVENTIONS)
    rows = []
    for size in (1, 2):
        for K in itertools.combinations(names, size):
            if not force(K, "collapsed"):
                rows.append((influence(K, "collapsed"), K))
    for p, K in sorted(rows, reverse=True)[:4]:
        print("    {%s}: %s  (not forcing)" % (", ".join(K), p))
    print()


# ------------------------------------------------------------------ report

def fmt(H):
    def f(r):
        t = r[0]
        if t == "Pop":
            return "Pop(%s)" % r[1]
        if t == "Comp":
            return "Compensates(%s,%s after %s)" % (r[1], r[2], r[4])
        if t == "Bind":
            return "Bind(%s,%s)" % (r[1], r[2])
        if t == "Trans":
            return "Transform(%s)" % r[1]
        if t == "Ver":
            return "Verify(%s,%s)" % (r[1], r[2])
        if t == "Ref":
            return "Refuse(%s,%s,%s)" % (r[1], r[2], r[3])
        if t == "VF":
            return "VerificationFailed(%s,%s)" % (r[1], r[2])
        if t == "Col":
            return "Collapse(%s,%s)" % (r[1], r[2])
        if t == "Dis":
            return "Discharged(%s,%s)" % (r[1], r[2])
        if t == "TO":
            return "TimedOut(%s,%s)" % (r[1], r[2])
    return " ; ".join(f(r) for r in H)


def main(n):
    ledgers = all_ledgers(n)
    nonempty = [H for H in ledgers if H]
    print("Disposition Lab v%s  (max events = %d)" % (LAB_VERSION, n))
    print("admissible ledgers enumerated: %d" % len(ledgers))
    print()

    print("== Property index (bounded propositions over the class H<=%d)" % n)
    klass = ("admissible ledgers, <= %d records, identities {c1,c2}, principals {a1,a2}, "
             "one value, one transformation, one rule, one obligation and deadline per commitment" % n)
    print("  class: " + klass)
    print("  normalization: fresh identities chosen canonically (equivariance); "
          "ledgers compared as record sequences")
    total_lins = 0

    def shuffle_prop(H):
        nonlocal total_lins
        ok, k = shuffle_ok(H)
        total_lins += k
        return ok

    PROPERTIES = [
        ("P-ReplaySound", "path lemma: delta* of each projection equals replay's map", path_lemma),
        ("P-TerminalExclusive", "at most one terminal record per commitment, and it is last", terminal_exclusive),
        ("P-CertificateAuthentic", "every VerificationFailed record checks against its state and a verifier", vf_unforgeable),
        ("P-FailedVerificationLive", "a VerificationFailed record leaves its commitment live", failed_verification_live),
        ("P-NoVerifierDisposition", "verification never yields a terminal state; terminal records need their authority", no_verifier_disposition),
        ("P-TraceInvariant", "every linearization of the dependence order replays identically", shuffle_prop),
        ("P-WorldAdmissible", "every configuration (downset) has a defined replay", downsets_ok),
    ]
    for name, desc, fn in PROPERTIES:
        bad = [H for H in ledgers if not fn(H)]
        cm = min(bad, key=lambda H: (len(H), repr(H))) if bad else None
        print("  %-26s expected: holds   result: %s   checked: %d" %
              (name, "holds" if not bad else "FAILS (%d)" % len(bad), len(ledgers)))
        print("      %s" % desc)
        if cm is not None:
            print("      minimized counterexample: %s" % fmt(cm))
    print("  linearizations replayed for P-TraceInvariant: %d" % total_lins)
    print("  not checked here (need the process or typed layer): P-RightsAgree, "
          "P-DelegationConservative; parser properties are checked by disposition_parser.py")
    print()

    print("== Modal terminal exclusivity:  Refused(c) -> not <>Collapsed(c)")
    viol = 0
    tested = 0
    for H in ledgers:
        w = World(H)
        for c in w.commitments():
            if w.refused(c):
                tested += 1
                if diamond(H, lambda u, c=c: u.collapsed(c)):
                    viol += 1
    print("  pointed worlds with a refusal tested: %d, violations: %d" % (tested, viol))
    print()

    print("== Countermodel search")
    conj1 = ("Verified(c) -> Authorized(binder(c), verify, c)",
             lambda w: all(may(w.binder(c), "verify") for c in w.commitments() if w.verified(c)))
    conj2 = ("Refused(c) -> c was never verified",
             lambda w: all(not w.verified(c) for c in w.commitments() if w.refused(c)))
    conj3 = ("Live(c) -> <>Collapsed(c)",
             lambda w: all(diamond(w.H, lambda u, c=c: u.collapsed(c)) for c in w.commitments() if w.live(c)))
    conj5 = ("Live(c) -> <>Terminal(c)",
             lambda w: all(diamond(w.H, lambda u, c=c: u.kind(c) in TERMINAL) for c in w.commitments() if w.live(c)))
    conj4 = ("Refused(c) -> not <>Collapsed(c)",
             lambda w: all(not diamond(w.H, lambda u, c=c: u.collapsed(c)) for c in w.commitments() if w.refused(c)))
    small = [H for H in ledgers if len(H) <= min(n, 6)]
    for name, phi in (conj1, conj2, conj3, conj5, conj4):
        cm = countermodel(phi, small)
        print("  %s" % name)
        if cm is None:
            print("    no countermodel with <= %d events" % min(n, 6))
        else:
            print("    smallest countermodel %s: %s" % (cm.size_key(), fmt(cm.H)))
    print()

    print("== History twins")
    observed = lambda w: len(w.O()) > 0
    for eq, ne, label, req in ((lens_present, lens_refusals, "present values equal, refusals differ", observed),
                               (lens_present, lens_authority, "present values equal, collapsing principal differs", observed),
                               (lens_state, lens_refusals, "state kinds equal, refusals differ", lambda w: True)):
        t = twins(eq, ne, nonempty, require=req)
        print("  %s" % label)
        if t is None:
            print("    none found")
        else:
            print("    W : %s" % fmt(t[0].H))
            print("    W': %s" % fmt(t[1].H))
    print()

    print("== Causal shuffle example")
    ex = next(H for H in ledgers if len({subj(r) for r in H}) == 2 and len(H) >= 4
              and len(linearizations(H)) >= 4)
    lins = linearizations(ex)
    print("  ledger: %s" % fmt(ex))
    print("  %d linearizations of its dependence order, replay identical: %s"
          % (len(lins), all(replay(L) == replay(ex) for L in lins)))
    print()

    print("== Perturbation mode (one change to an admissible ledger)")
    base = next(H for H in ledgers if [r[0] for r in H] == ["Pop", "Bind", "Trans", "Ver", "Col"])
    print("  base: %s" % fmt(base))
    for name, diag in perturb(base):
        print("   - %-34s -> %s" % (name, diag))
    base2 = next(H for H in ledgers
                 if [r[0] for r in H] == ["Pop", "Bind", "Trans", "Ref"])
    base3 = next(H for H in ledgers if [r[0] for r in H] == ["Pop", "Bind", "Trans", "VF", "Ref"])
    print("  base: %s" % fmt(base2))
    for name, diag in perturb(base2):
        if name.startswith("delete"):
            print("   - %-34s -> %s" % (name, diag))
    print("  base: %s" % fmt(base3))
    for name, diag in perturb(base3):
        if name.startswith("forged"):
            print("   - %-34s -> %s" % (name, diag))
    print()

    control_report()

    print("== Witness mixer")
    H = (("Pop", "c1", Q), ("Pop", "c2", Q), ("Bind", "a1", "c1", B), ("Bind", "a1", "c2", B),
         ("Trans", "c1", F, B, V), ("Trans", "c2", F, B, V))
    w1, w2 = good_witness("c1", V), good_witness("c2", V)
    ok = replay(H + (("Ver", "a2", "c1", V, w1),)) is not None
    swapped = replay(H + (("Ver", "a2", "c1", V, w2),)) is not None
    unindexed = (lambda w, v: w[0] == "w" and w[-1] == v)(w2, V)
    print("  c1, c2 both transformed(b, v); w1 indexed to c1, w2 indexed to c2")
    print("  verify c1 with w1: accepted=%s" % ok)
    print("  verify c1 with w2: accepted=%s   (an unindexed check would accept: %s)" % (swapped, unindexed))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
