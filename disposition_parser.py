"""Concrete syntax, parser, and printer for the disposition calculus, with the
machine checks of the Unique Parsing chapter.

There is exactly one grammar, GRAMMAR. The parser is a table-driven LL(1)
parser generated from it, so the grammar that is analyzed for conflicts is
the grammar that is parsed. The parse tree is then converted to an abstract
syntax tree.

Claims and checks, kept at their proper strength:
  Lexical   tokenization is unique (disjoint lexical classes; argued in the book)
  General   P-ParserLL1: GRAMMAR has no LL(1) conflicts, hence every token
            sequence in L(GRAMMAR) has exactly one derivation (a theorem about
            all inputs, established by the table check plus the standard result)
  Bounded   P-ParserUnique, P-ParserRoundTrip, P-ParserNormalize: checks over
            every AST of constructor size <= n, which exercise the
            implementation and printer; they do not stand in for the theorem
  Named     P-ParserNamed: targeted cases with expected ASTs
  Reject    P-ParserRejects: malformed and incomplete inputs

Enumeration uses a tiny atom alphabet. That suffices because parsing depends
on token kinds, not on the identities of atoms.

Run:  python3 disposition_parser.py [max_size]
"""

import itertools
import re
import sys
from functools import lru_cache

# ------------------------------------------------------------------ lexing

KEYWORDS = {"pop", "as", "after", "bind", "to", "transform", "with", "refuse",
            "because", "collapse", "verify", "using", "then", "else", "await",
            "within", "nu"}
PUNCT = {"(", ")", "[", "]", ",", ".", "|", "+", "!", "0"}
NAME = r"[A-Za-z_][A-Za-z0-9_]*"

# Lexical classes, disjoint by their first character:
#   #NAME commitment names (CN)   @NAME principals (PR)    ?NAME obligations (OB)
#   %NAME observation rules (RL)  ~NAME intervals (TM)     "..." reasons (RS),
#   with backslash escapes        lowercase-initial NAME that is not a keyword:
#   values, functions, requests (VAL)                      keywords and punctuation
TOKEN_RE = re.compile(
    r'\s*(?:'
    r'(#' + NAME + r')|(@' + NAME + r')|(\?' + NAME + r')|(%' + NAME + r')|(~' + NAME + r')'
    r'|("(?:[^"\\\n]|\\.)*")'
    r'|([a-z][A-Za-z0-9_]*)'
    r'|([()\[\],.|+!0]))')


class LexError(Exception):
    pass


def unescape(lit):
    return re.sub(r"\\(.)", r"\1", lit[1:-1])


def lex(src):
    toks = []
    pos = 0
    src = src.rstrip()
    while pos < len(src):
        m = TOKEN_RE.match(src, pos)
        if not m or m.end() == pos:
            raise LexError("cannot lex at: %r" % src[pos:pos + 12])
        pos = m.end()
        cn, pr, ob, rl, tm, rs, ident, ch = m.groups()
        if cn:
            toks.append(("CN", cn))
        elif pr:
            toks.append(("PR", pr))
        elif ob:
            toks.append(("OB", ob))
        elif rl:
            toks.append(("RL", rl))
        elif tm:
            toks.append(("TM", tm))
        elif rs:
            toks.append(("RS", unescape(rs)))
        elif ident:
            toks.append((ident, ident) if ident in KEYWORDS else ("VAL", ident))
        elif ch:
            toks.append((ch, ch))
        else:
            raise LexError("cannot lex at: %r" % src[pos:pos + 12])
    toks.append(("$", "$"))
    return toks


# ------------------------------------------------------------------ grammar

EPS = ()
GRAMMAR = {
    "P":  [("S", "P1")],
    "P1": [("+", "P"), EPS],
    "S":  [("U", "S1")],
    "S1": [("|", "S"), EPS],
    "U": [
        ("0",),
        ("(", "P", ")"),
        ("nu", "CN", ".", "U"),
        ("!", "U"),
        ("pop", "POP"),
        ("bind", "[", "PR", "]", "CN", "to", "VAL", ".", "U"),
        ("transform", "CN", "with", "VAL", ".", "U"),
        ("refuse", "[", "PR", "]", "CN", "because", "RS", ".", "U"),
        ("collapse", "[", "PR", ",", "RL", "]", "CN", ".", "U"),
        ("verify", "[", "PR", "]", "CN", "using", "VAL", "then", "U", "else", "U"),
        ("await", "[", "PR", "]", "CN", "OB", "AW"),
    ],
    "POP": [("VAL", "as", "CN", ".", "U"),
            ("[", "PR", "]", "VAL", "as", "CN", "after", "CN", ".", "U")],
    "AW": [(".", "U"),
           ("within", "[", "PR", "]", "TM", "then", "U", "else", "U")],
}
START = "P"
NONTERMS = set(GRAMMAR)


def first_follow():
    first = {A: set() for A in NONTERMS}
    nullable = {A: False for A in NONTERMS}

    def first_seq(seq):
        out = set()
        for X in seq:
            if X in NONTERMS:
                out |= first[X]
                if not nullable[X]:
                    return out, False
            else:
                out.add(X)
                return out, False
        return out, True

    changed = True
    while changed:
        changed = False
        for A, alts in GRAMMAR.items():
            for alt in alts:
                f, n = first_seq(alt)
                if not f <= first[A]:
                    first[A] |= f
                    changed = True
                if n and not nullable[A]:
                    nullable[A] = True
                    changed = True
    follow = {A: set() for A in NONTERMS}
    follow[START].add("$")
    changed = True
    while changed:
        changed = False
        for A, alts in GRAMMAR.items():
            for alt in alts:
                for i, X in enumerate(alt):
                    if X in NONTERMS:
                        f, n = first_seq(alt[i + 1:])
                        add = f | (follow[A] if n else set())
                        if not add <= follow[X]:
                            follow[X] |= add
                            changed = True
    return first, nullable, follow, first_seq


def predict_table():
    """The LL(1) table and the list of conflicts (empty iff LL(1))."""
    first, nullable, follow, first_seq = first_follow()
    table, conflicts = {}, []
    for A, alts in GRAMMAR.items():
        for alt in alts:
            f, n = first_seq(alt)
            for t in f | (follow[A] if n else set()):
                if (A, t) in table and table[(A, t)] != alt:
                    conflicts.append((A, t, table[(A, t)], alt))
                table[(A, t)] = alt
    return table, conflicts


TABLE, CONFLICTS = predict_table()


def count_derivations(tokens):
    """Number of derivations of the token kinds under GRAMMAR (end marker excluded)."""
    kinds = tuple(t[0] for t in tokens if t[0] != "$")
    n = len(kinds)

    @lru_cache(maxsize=None)
    def seq(symbols, i, j):
        if not symbols:
            return 1 if i == j else 0
        X, rest = symbols[0], symbols[1:]
        return sum(sym(X, i, k) * seq(rest, k, j) for k in range(i, j + 1) if sym(X, i, k))

    @lru_cache(maxsize=None)
    def sym(X, i, j):
        if X not in NONTERMS:
            return 1 if j == i + 1 and kinds[i] == X else 0
        return sum(seq(alt, i, j) for alt in GRAMMAR[X])

    return sym(START, 0, n)


# ------------------------------------------------------------------ table-driven parsing

class ParseError(Exception):
    pass


def parse_tree(tokens):
    """LL(1) predictive parse driven by TABLE. Returns a tree (symbol, children)
    in which terminal leaves carry their token values."""
    pos = 0

    def expand(X):
        nonlocal pos
        kind, val = tokens[pos]
        if X not in NONTERMS:
            if kind != X:
                raise ParseError("expected %s, found %r" % (X, val))
            pos += 1
            return (X, val)
        alt = TABLE.get((X, kind))
        if alt is None:
            raise ParseError("no rule for %s on %r" % (X, val))
        return (X, [expand(Y) for Y in alt])

    tree = expand(START)
    if tokens[pos][0] != "$":
        raise ParseError("trailing input at %r" % (tokens[pos][1],))
    return tree


def to_ast(t):
    """Convert a GRAMMAR parse tree to the abstract syntax tree."""
    X, kids = t
    if X == "P":
        s, p1 = kids
        left = to_ast(s)
        return ("sum", left, to_ast(p1[1][1])) if p1[1] else left
    if X == "S":
        u, s1 = kids
        left = to_ast(u)
        return ("par", left, to_ast(s1[1][1])) if s1[1] else left
    if X == "U":
        head = kids[0][0]
        v = [k[1] if k[0] not in NONTERMS else k for k in kids]
        if head == "0":
            return ("nil",)
        if head == "(":
            return to_ast(kids[1])
        if head == "nu":
            return ("nu", v[1], to_ast(kids[3]))
        if head == "!":
            return ("rep", to_ast(kids[1]))
        if head == "pop":
            pk = kids[1][1]
            pv = [k[1] if k[0] not in NONTERMS else k for k in pk]
            if pk[0][0] == "VAL":
                return ("pop", pv[0], pv[2], to_ast(pk[4]))
            return ("popafter", pv[1], pv[3], pv[5], pv[7], to_ast(pk[9]))
        if head == "bind":
            return ("bind", v[2], v[4], v[6], to_ast(kids[8]))
        if head == "transform":
            return ("transform", v[1], v[3], to_ast(kids[5]))
        if head == "refuse":
            return ("refuse", v[2], v[4], v[6], to_ast(kids[8]))
        if head == "collapse":
            return ("collapse", v[2], v[4], v[6], to_ast(kids[8]))
        if head == "verify":
            return ("verify", v[2], v[4], v[6], to_ast(kids[8]), to_ast(kids[10]))
        if head == "await":
            aw = kids[6][1]
            if aw[0][0] == ".":
                return ("await", v[2], v[4], v[5], to_ast(aw[1]))
            av = [k[1] if k[0] not in NONTERMS else k for k in aw]
            return ("awaitdl", v[2], v[4], v[5], av[2], av[4], to_ast(aw[6]), to_ast(aw[8]))
    raise ValueError(X)


def parse(src):
    return to_ast(parse_tree(lex(src)))


# ------------------------------------------------------------------ printing

def q(r):
    """Quote a reason with escapes."""
    return '"%s"' % r.replace("\\", "\\\\").replace('"', '\\"')


def show(P, ctx=0):
    """Print with minimal parentheses. ctx: 0 sum position, 1 par position,
    2 unary position (a U)."""
    t = P[0]
    if t == "sum":
        s = "%s + %s" % (show(P[1], 1), show(P[2], 0))
        return s if ctx == 0 else "(%s)" % s
    if t == "par":
        s = "%s | %s" % (show(P[1], 2), show(P[2], 1))
        return s if ctx <= 1 else "(%s)" % s
    return show_unary(P, lambda X: show(X, 2))


def show_unary(P, sub):
    t = P[0]
    if t == "nil":
        return "0"
    if t == "nu":
        return "nu %s . %s" % (P[1], sub(P[2]))
    if t == "rep":
        return "! %s" % sub(P[1])
    if t == "pop":
        return "pop %s as %s . %s" % (P[1], P[2], sub(P[3]))
    if t == "popafter":
        return "pop [%s] %s as %s after %s . %s" % (P[1], P[2], P[3], P[4], sub(P[5]))
    if t == "bind":
        return "bind [%s] %s to %s . %s" % (P[1], P[2], P[3], sub(P[4]))
    if t == "transform":
        return "transform %s with %s . %s" % (P[1], P[2], sub(P[3]))
    if t == "refuse":
        return "refuse [%s] %s because %s . %s" % (P[1], P[2], q(P[3]), sub(P[4]))
    if t == "collapse":
        return "collapse [%s, %s] %s . %s" % (P[1], P[2], P[3], sub(P[4]))
    if t == "verify":
        return "verify [%s] %s using %s then %s else %s" % (P[1], P[2], P[3], sub(P[4]), sub(P[5]))
    if t == "await":
        return "await [%s] %s %s . %s" % (P[1], P[2], P[3], sub(P[4]))
    if t == "awaitdl":
        return "await [%s] %s %s within [%s] %s then %s else %s" % (
            P[1], P[2], P[3], P[4], P[5], sub(P[6]), sub(P[7]))
    raise ValueError(t)


def show_redundantly_parenthesized(P):
    """A member of Concrete(P) with a redundant pair of parentheses around
    every subterm, binary terms and the root included."""
    t = P[0]
    if t in ("sum", "par"):
        op = " + " if t == "sum" else " | "
        return "((%s)%s(%s))" % (show_redundantly_parenthesized(P[1]), op,
                                 show_redundantly_parenthesized(P[2]))
    return "(%s)" % show_unary(P, lambda X: "(%s)" % show_redundantly_parenthesized(X))


# ------------------------------------------------------------------ enumeration

C, D = "#c", "#d"
A, B = "@a", "@b"


@lru_cache(maxsize=None)
def processes(size):
    """All ASTs with exactly `size` constructors over a fixed tiny alphabet of
    atoms (parsing depends only on token kinds)."""
    if size == 1:
        return (("nil",),)
    out = []
    for k in range(1, size - 1):
        for L in processes(k):
            for R in processes(size - 1 - k):
                out.append(("sum", L, R))
                out.append(("par", L, R))
                out.append(("verify", A, C, "g", L, R))
                out.append(("awaitdl", A, C, "?w", B, "~t", L, R))
    for P in processes(size - 1):
        out += [("nu", C, P), ("rep", P), ("pop", "q", C, P),
                ("popafter", A, "q", C, D, P), ("bind", A, C, "x", P),
                ("transform", C, "f", P), ("refuse", A, C, 'r "quoted"', P),
                ("collapse", A, "%k", C, P), ("await", A, C, "?w", P)]
    return tuple(out)


NAMED_CASES = [
    ("prefix scope", "pop q as #c . 0 | 0",
     ("par", ("pop", "q", "#c", ("nil",)), ("nil",))),
    ("prefix over parallel needs parentheses", "pop q as #c . (0 | 0)",
     ("pop", "q", "#c", ("par", ("nil",), ("nil",)))),
    ("parallel binds tighter than choice", "0 | 0 + 0",
     ("sum", ("par", ("nil",), ("nil",)), ("nil",))),
    ("choice is right associative", "0 + 0 + 0",
     ("sum", ("nil",), ("sum", ("nil",), ("nil",)))),
    ("nested prefixes", "pop q as #c . bind [@a] #c to x . transform #c with f . 0",
     ("pop", "q", "#c", ("bind", "@a", "#c", "x", ("transform", "#c", "f", ("nil",))))),
    ("restriction over parallel", 'nu #c . (refuse [@a] #c because "r" . 0 | 0)',
     ("nu", "#c", ("par", ("refuse", "@a", "#c", "r", ("nil",)), ("nil",)))),
    ("replicated generative pop", '! pop q as #c . refuse [@a] #c because "r" . 0',
     ("rep", ("pop", "q", "#c", ("refuse", "@a", "#c", "r", ("nil",))))),
    ("deadline form", 'await [@a] #c ?w within [@b] ~t then 0 else refuse [@a] #c because "late" . 0',
     ("awaitdl", "@a", "#c", "?w", "@b", "~t", ("nil",), ("refuse", "@a", "#c", "late", ("nil",)))),
    ("rule-indexed collapse", "collapse [@a, %alloc] #c . 0",
     ("collapse", "@a", "%alloc", "#c", ("nil",))),
    ("verification branches are unary", 'verify [@a] #c using g then 0 else 0 | 0',
     ("par", ("verify", "@a", "#c", "g", ("nil",), ("nil",)), ("nil",))),
    ("escaped reason", r'refuse [@a] #c because "said \"no\"" . 0',
     ("refuse", "@a", "#c", 'said "no"', ("nil",))),
]

MALFORMED = [
    ("explicit refusal requires an RS token; source values are rejected", "refuse [@a] #c because cert . 0"),
    ("unterminated reason", 'refuse [@a] #c because "r . 0'),
    ("invalid character", "0 & 0"),
    ("keyword in a VAL position", "transform #c with then . 0"),
    ("missing continuation after the dot", "pop q as #c ."),
    ("empty parenthesized process", "()"),
    ("extra else", "verify [@a] #c using g then 0 else 0 else 0"),
    ("verify requires both branches", "verify [@a] #c using g then 0"),
    ("malformed rule index", "collapse [@a, k] #c . 0"),
    ("obligation in a commitment position", "bind [@a] ?w to x . 0"),
    ("deadline lacking its timeout principal", "await [@a] #c ?w within ~t then 0 else 0"),
    ("deadline requires its else branch", "await [@a] #c ?w within [@b] ~t then 0"),
    ("bind requires a principal", "bind #c to x . 0"),
    ("compensating pop requires a principal", "pop q as #c after #d . 0"),
    ("commitment and principal sorts are distinct", "bind [#c] @a to x . 0"),
    ("unbalanced parentheses", "(0 | 0"),
    ("trailing tokens", "0 0"),
]


def main(max_size):
    print("Disposition parser checks")
    print("  Lexical  unique tokenization: argued in the book (disjoint first characters)")
    print("  General  P-ParserLL1       %s" % (
        "holds: the table generated from GRAMMAR has no conflicts, so every token "
        "sequence in L(GRAMMAR) has exactly one derivation" if not CONFLICTS
        else "FAILS: %s" % CONFLICTS[:3]))
    sizes = list(range(1, max_size + 1))
    asts = [P for n in sizes for P in processes(n)]
    distinct = len(set(asts))
    bad_unique, bad_round, bad_norm = [], [], []
    for P in asts:
        s = show(P)
        if count_derivations(lex(s)) != 1:
            bad_unique.append(s)
        try:
            padded = show_redundantly_parenthesized(P)
            if parse(s) != P or parse(padded) != P:
                bad_round.append(s)
            if show(parse(s)) != s or parse(show(parse(padded))) != parse(padded):
                bad_norm.append(s)
        except (ParseError, LexError) as e:
            bad_round.append("%s  (%s)" % (s, e))
    print("  Bounded  constructor size <= %d: %d ASTs generated, %d distinct" %
          (max_size, len(asts), distinct))
    print("           P-ParserUnique      %s" % ("holds" if not bad_unique else "FAILS e.g. %s" % bad_unique[0]))
    print("           P-ParserRoundTrip   %s  (parse(show P) = P and parse(pad P) = P)" %
          ("holds" if not bad_round else "FAILS e.g. %s" % bad_round[0]))
    print("           P-ParserNormalize   %s  (show(parse(show P)) = show P; "
          "parse(show(parse s)) = parse s)" % ("holds" if not bad_norm else "FAILS e.g. %s" % bad_norm[0]))
    named_ok = 0
    for name, src, expected in NAMED_CASES:
        try:
            got = parse(src)
            ok = (got == expected and count_derivations(lex(src)) == 1
                  and parse(show(got)) == got)
        except (ParseError, LexError):
            ok = False
        named_ok += ok
        print("             %-4s %-40s %s" % ("ok" if ok else "FAIL", name, src))
    print("  Named    P-ParserNamed       %s over %d cases with expected ASTs" %
          ("holds" if named_ok == len(NAMED_CASES) else "FAILS", len(NAMED_CASES)))
    rejected = 0
    for why, src in MALFORMED:
        try:
            parse(src)
            ok = False
        except (ParseError, LexError):
            ok = True
        rejected += ok
        print("             %-4s %s" % ("ok" if ok else "ACCEPTED", why))
    print("  Reject   P-ParserRejects     %s over %d malformed inputs" %
          ("holds" if rejected == len(MALFORMED) else "FAILS", len(MALFORMED)))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
