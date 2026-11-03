#!/usr/bin/env python3
"""inc19 probe task 3: SAT encoding experiment for "Maker wins within d claims
from frontier position 1036" (the h=16 re-proof target).

RUN HERE (depth 2, fully adversarial, EXACT):
  win-in-2 := exists Maker m1 such that for EVERY Breaker reply b (all free
  cells) Maker's m2 completes a placement of M ∪ {p, m1} missed only by m2.
  Exact clause scheme: let PI = live placements meeting M∪{p} with
  |π \ (M∪{p})| <= 2 (the only placements finishable in 2 Maker claims).
  For each free cell b:  clause_b = OR of
      x_c                        for 1-away π with c = π\..., b ∉ π
      x_c1 ∨ x_c2                for 2-away π = {c1,c2}+M, b ∉ π
  (x_c = "Maker's first claim is c", exactly-one).  Sound because a completing
  m1 must lie in some π ∈ PI, and b ∉ π guarantees the m2 cell stays free.

Cross-validated against direct threat enumeration (won-after-m1 OR >= 2
distinct level-1 threat cells — the standard double-threat criterion, which is
also what the AND/OR searcher's len(t)>=2 branch checks).

Depth-3+: not solvable within the probe budget (expansion tree = the task-2
AND/OR tree; measured node counts there).  A QDIMACS generator skeleton for
∃m1 ∀b1 ∃m2 … ∃m16 is included below for the campaign's QBF probe.
"""
import itertools
import json
import sys
from collections import defaultdict

sys.path.insert(0, "/tmp/snaky/inc19/probe")
from size_search import PLACEMENTS, BY_CELL, idx, FORMS  # noqa: E402

from pysat.formula import IDPool  # noqa: E402
from pysat.solvers import Cadical153  # noqa: E402


def main():
    pos = json.load(open("/tmp/snaky/inc19/probe/positions.json"))["1036a"]
    M0 = frozenset(idx(tuple(c)) for c in pos["maker_M"]) | {idx(tuple(pos["maker_p"]))}
    B0 = frozenset(idx(tuple(c)) for c in pos["breaker_B"])
    free = sorted(set(range(289)) - M0 - B0)

    own = [pi for pi in range(len(PLACEMENTS))
           if PLACEMENTS[pi].isdisjoint(B0) and (PLACEMENTS[pi] & M0)]
    PI = []
    for pi in own:
        miss = sorted(PLACEMENTS[pi] - M0)
        if len(miss) <= 2:
            PI.append(miss)
    relevant = sorted(set(c for miss in PI for c in miss))
    one_away = [m for m in PI if len(m) == 1]
    two_away = [m for m in PI if len(m) == 2]
    print(f"finishable placements: 1-away={len(one_away)} 2-away={len(two_away)} "
          f"candidate m1 cells={len(relevant)} free={len(free)}")

    def won(cells):
        cells = frozenset(cells)
        return any(PLACEMENTS[pi] <= cells for pi in own)

    # ---- ground truth by direct enumeration ----
    def threats_after(m1):
        M1 = M0 | {m1}
        t = defaultdict(int)
        for pi in own:
            if PLACEMENTS[pi] & {m1} or PLACEMENTS[pi] <= M0:
                pass
            miss = PLACEMENTS[pi] - M1
            if len(miss) == 1:
                t[next(iter(miss))] += 1
        return t

    win_m1 = []
    for m1 in relevant:
        M1 = M0 | {m1}
        if won(M1):
            win_m1.append(m1)
            continue
        t = threats_after(m1)
        if len(t) >= 2:
            win_m1.append(m1)
    print(f"ground truth: win-in-2 m1 cells = {len(win_m1)} "
          f"{[(c % 17, c // 17) for c in win_m1[:6]]}")

    # ---- SAT encoding ----
    pool = IDPool()
    x = {c: pool.id(("m1", c)) for c in relevant}
    cls = []
    for a, b in itertools.combinations(relevant, 2):
        cls.append([-x[a], -x[b]])          # at-most-one m1
    cls.append([x[c] for c in relevant])    # at-least-one m1
    for b in free:
        lit = []
        for miss in one_away:
            c = miss[0]
            if c != b:
                lit.append(x[c])
        for miss in two_away:
            if b not in miss:
                lit.extend(x[c] for c in miss)
        cls.append(lit)
    print(f"SAT: vars={pool.top} clauses={len(cls)} "
          f"literals={sum(len(c) for c in cls)}")

    with Cadical153(bootstrap_with=cls) as s:
        sat = s.solve()
        wits = []
        if sat:
            model = s.get_model()
            val = {v + 1: (model[v] > 0) for v in range(len(model))}
            wits = [c for c in relevant if val[x[c]]]
    ans = "WIN-IN-2" if sat else "NO WIN-IN-2"
    print(f"SAT answer: {ans}; witness m1 = {[(c % 17, c // 17) for c in wits]}")
    print(f"cross-validation: {'AGREE' if bool(win_m1) == sat else 'MISMATCH'}")

    # ---- machinery validation on synthetic controls ----
    # compare SAT vs DIRECT enumeration on two synthetic positions (4/6 and
    # 3/6 cells of a snaky placement).  No hand-picked expectation: the two
    # methods must simply agree.
    form = FORMS[0]
    pts4 = [(x + 1, y + 5) for x, y in form]
    cells4 = {idx(p) for p in pts4} - {idx(pts4[4]), idx(pts4[5])}
    cells3 = set(sorted({idx((x + 1, y + 5)) for x, y in form})[:3])

    def direct_win2(Mc, Bs):
        own = [pi for pi in range(len(PLACEMENTS))
               if PLACEMENTS[pi].isdisjoint(Bs) and (PLACEMENTS[pi] & Mc)]
        fr = sorted(set(range(289)) - Mc - Bs)
        PI = [sorted(PLACEMENTS[pi] - Mc) for pi in own if len(PLACEMENTS[pi] - Mc) <= 2]
        rel = sorted(set(c for miss in PI for c in miss))

        def threats_after(m1):
            M1 = Mc | {m1}
            t = set()
            for pi in own:
                miss = PLACEMENTS[pi] - M1
                if len(miss) == 1:
                    t.add(next(iter(miss)))
            return t

        for m1 in rel:
            if any(PLACEMENTS[pi] <= Mc | {m1} for pi in own):
                return True, m1
            if len(threats_after(m1)) >= 2:
                return True, m1
        return False, None

    def control(Mc, use_sat):
        Bs = frozenset({idx((15, 0)), idx((16, 0)), idx((0, 16))})
        if not use_sat:
            return direct_win2(Mc, Bs)[0]
        own = [pi for pi in range(len(PLACEMENTS))
               if PLACEMENTS[pi].isdisjoint(Bs) and (PLACEMENTS[pi] & Mc)]
        PI = [sorted(PLACEMENTS[pi] - Mc) for pi in own if len(PLACEMENTS[pi] - Mc) <= 2]
        rel = sorted(set(c for miss in PI for c in miss))
        fr = sorted(set(range(289)) - Mc - Bs)
        p2 = IDPool()
        xx = {c: p2.id(c) for c in rel}
        cc = [[-xx[a], -xx[b]] for a, b in itertools.combinations(rel, 2)]
        cc.append([xx[c] for c in rel] if rel else [-1])
        for b in fr:
            lit = []
            for miss in PI:
                if len(miss) == 1 and miss[0] != b:
                    lit.append(xx[miss[0]])
                elif len(miss) == 2 and b not in miss:
                    lit.extend(xx[c] for c in miss)
            cc.append(lit)
        with Cadical153(bootstrap_with=cc) as s:
            return s.solve()

    for name, Mc in (("4/6", cells4), ("3/6", cells3)):
        d = control(Mc, use_sat=False)
        s = control(Mc, use_sat=True)
        print(f"control {name} of a placement: direct={d} SAT={s} "
              f"{'AGREE' if d == s else 'MISMATCH'}")

    # ---- depth-d projection ----
    print("""
depth-d expansion cost (exact adversarial, reply-enumerated):
  the depth-d formula is the AND/OR tree of size_truncations.py times ~10
  literals/node; no stand-alone SAT win — the tree IS the encoding.
QBF alternative (∃ m_i, ∀ b_i, i=1..16, leaf = won(M ∪ m's) with placements
  disjoint from B): ~67·16 exist-var + 283·16 univ-var + ~2k board-var base;
  no QBF solver installed on this host; solve behaviour at depth 16 unknown —
  this stays the campaign's one bounded experiment per SCOPE B2.""")


def qdimacs_skeleton(d):
    """Print the ∃∀ alternation structure for win-in-d (documentation)."""
    print(f"QDIMACS win-in-{d}: "
          + " ".join(f"e m{i} / a b{i}" for i in range(1, d + 1)))


if __name__ == "__main__":
    main()
