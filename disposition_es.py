"""Bounded checks for the event-structure chapter.

Builds the branching disposition event structure W from all admissible
ledgers of the laboratory (from the empty configuration, up to n records),
with events as prime traces: a record together with its causal past.

Checks (bounded propositions over the ledgers of length <= n):
  P-ESRealized     every ledger's event set is a configuration of W
                   (downward closed and pairwise conflict free)
  P-ESComplete     every configuration of W with <= n events replays
                   (so consistency is binary: pairwise suffices)
  P-ESHeredity     conflict is inherited: e # e' and e' <= e'' imply e # e''
  P-ESTraceIso     all linearizations of a ledger's dependence order have the
                   same event set, with the same order (O(H) is invariant)

Run:  python3 disposition_es.py [n]
"""

import sys
import itertools
import disposition_lab as lab


def lexmin_linearization(H, members, lt):
    """Lexicographically least linearization (by repr of records) of the
    sub-order of H's dependence order on the given positions."""
    remaining = set(members)
    out = []
    while remaining:
        ready = [i for i in remaining if not any(lt[j][i] for j in remaining if j != i)]
        i = min(ready, key=lambda k: repr(H[k]))
        out.append(i)
        remaining.remove(i)
    return out


def events_of(H):
    """Map each position of H to its event id: the lex-least linearization of
    its causal past (itself included), as a tuple of records."""
    lt = lab.dependence_order(H)
    n = len(H)
    ids = []
    for i in range(n):
        past = [j for j in range(n) if lt[j][i]] + [i]
        order = lexmin_linearization(H, past, lt)
        ids.append(tuple(H[k] for k in order))
    return ids, lt


def build(n):
    ledgers = lab.all_ledgers(n)
    preds = {}          # event id -> frozenset of immediate-or-transitive predecessor ids
    for H in ledgers:
        ids, lt = events_of(H)
        for i, e in enumerate(ids):
            p = frozenset(ids[j] for j in range(len(H)) if lt[j][i])
            if e in preds and preds[e] != p:
                raise AssertionError("event with two different pasts: %r" % (e,))
            preds[e] = p
    return ledgers, preds


def down(e, preds):
    return preds[e] | {e}


def replays(events, preds):
    """Replay the records of a set of events in a causal order."""
    evs = list(events)
    remaining = set(evs)
    X = lab.EMPTY
    while remaining:
        ready = [e for e in remaining if not (preds[e] & remaining)]
        if not ready:
            return False
        e = min(ready, key=repr)
        X = lab.apply(X, e[-1])
        if X is None:
            return False
        remaining.remove(e)
    return True


def main(n):
    ledgers, preds = build(n)
    E = list(preds)
    print("Event-structure checks over ledgers with <= %d records" % n)
    print("  ledgers: %d   events of W: %d" % (len(ledgers), len(E)))

    compat_cache = {}

    def compatible(e, f):
        """e and f occur together in some execution, with the pasts they claim:
        every dependent pair in the union of their pasts is causally ordered
        (otherwise whichever came first would be in the other's past), and the
        union replays. By Proposition commute the order of the remaining,
        independent, events does not matter."""
        key = (e, f) if repr(e) <= repr(f) else (f, e)
        if key not in compat_cache:
            U = down(e, preds) | down(f, preds)
            ok = True
            for x, y in itertools.combinations(U, 2):
                if not lab.independent(x[-1], y[-1]) and x not in preds[y] and y not in preds[x]:
                    ok = False
                    break
            compat_cache[key] = ok and replays(U, preds)
        return compat_cache[key]

    # P-ESRealized
    bad = 0
    for H in ledgers:
        ids, _ = events_of(H)
        S = set(ids)
        closed = all(preds[e] <= S for e in S)
        pairwise = all(compatible(e, f) for e, f in itertools.combinations(S, 2))
        bad += not (closed and pairwise)
    print("  P-ESRealized    %s" % ("holds" if not bad else "FAILS (%d)" % bad))

    # P-ESTraceIso
    bad = 0
    lins = 0
    for H in ledgers:
        ids, _ = events_of(H)
        base = (frozenset(ids), frozenset((e, preds[e]) for e in ids))
        for L in lab.linearizations(H):
            lins += 1
            ids2, _ = events_of(L)
            if (frozenset(ids2), frozenset((e, preds[e]) for e in ids2)) != base:
                bad += 1
    print("  P-ESTraceIso    %s over %d linearizations" % ("holds" if not bad else "FAILS (%d)" % bad, lins))

    # P-ESHeredity
    succ = {e: set() for e in E}
    for e in E:
        for p in preds[e]:
            succ[p].add(e)
    bad = 0
    conflicts = 0
    for e, f in itertools.combinations(E, 2):
        if not compatible(e, f):
            conflicts += 1
            for g in succ[f]:
                if compatible(e, g):
                    bad += 1
            for g in succ[e]:
                if compatible(f, g):
                    bad += 1
    print("  P-ESHeredity    %s  (%d conflicting pairs)" % ("holds" if not bad else "FAILS (%d)" % bad, conflicts))

    # P-ESComplete: enumerate configurations (downward closed, pairwise
    # conflict free) with <= n events; each must replay.
    configs = {frozenset()}
    frontier = [frozenset()]
    for _ in range(n):
        nxt = []
        for X in frontier:
            for e in E:
                if e in X or not preds[e] <= X:
                    continue
                if all(compatible(e, f) for f in X):
                    Y = X | {e}
                    if Y not in configs:
                        configs.add(Y)
                        nxt.append(Y)
        frontier = nxt
    bad = [X for X in configs if not replays(X, preds)]
    print("  P-ESComplete    %s over %d configurations" %
          ("holds" if not bad else "FAILS (%d)" % len(bad), len(configs)))
    realized = set()
    for H in ledgers:
        ids, _ = events_of(H)
        realized.add(frozenset(ids))
    extra = [X for X in configs if X not in realized]
    print("  configurations realized by an enumerated ledger: %d of %d" %
          (len(configs) - len(extra), len(configs)))
    if extra:
        ex = min(extra, key=lambda X: (len(X), repr(sorted(map(repr, X)))))
        print("    example not enumerated (canonical naming), but replayable: %s"
              % " ; ".join(lab.fmt((e[-1],)) for e in sorted(ex, key=lambda e: len(e))))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
