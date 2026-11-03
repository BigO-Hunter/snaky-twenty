#!/usr/bin/env python3
"""inc19 probe task 2: size the h=16 re-proof search at frontier position 1036
(and static numbers for 1608/1701).

Definitions (maker-breaker snaky on the 17x17 window):
  placement = 6-cell translate of one of snaky's 8 orientations, inside the board
  live      = placement holding no Breaker cell
  Maker wins in k claims: Maker to move, completes some placement within k Maker
  moves (Breaker replies between), i.e. exactly the card table's h value.

Measured here:
  A. statics: |live|, overlap distribution with Maker's set, relevant cell set
     (union of live placements meeting Maker), touching cells (Breaker replies
     that can hurt = free cells in live placements meeting Maker), D4 orbit of
     the position.
  B. bounded AND/OR growth: depth-limited expansion — OR = free cells in live
     placements meeting Maker ("relevant moves"); AND = forced block if a
     level-1 threat exists, else ALL touching replies; memo + D4 canonical
     keys.  Nodes per ply measured to the depth the budget allows, growth rate
     per ply pair reported.
Stdlib only; time-capped sections so every run stays far under 20 min.
"""
import json
import sys
import time
from collections import Counter, defaultdict

R = C = 17
CELLS = R * C

ORIENT = [(1, 0, 0, 1), (-1, 0, 0, 1), (0, -1, 1, 0), (0, 1, 1, 0),
          (-1, 0, 0, -1), (1, 0, 0, -1), (0, 1, -1, 0), (0, -1, -1, 0)]
BASE = [(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)]
FORMS = []
for a, b, c, d in ORIENT:
    pts = sorted((a * x + b * y, c * x + d * y) for x, y in BASE)
    mx, my = min(p[0] for p in pts), min(p[1] for p in pts)
    form = tuple(sorted((p[0] - mx, p[1] - my) for p in pts))
    if form not in FORMS:
        FORMS.append(form)

idx = lambda p: p[1] * C + p[0]
pt = lambda i: (i % C, i // C)

PLACEMENTS = []  # list of frozenset of cell indices
for f in FORMS:
    fx = [p[0] for p in f]
    fy = [p[1] for p in f]
    for x0 in range(0 - min(fx), C - max(fx)):
        for y0 in range(0 - min(fy), R - max(fy)):
            PLACEMENTS.append(frozenset(idx((x + x0, y + y0)) for x, y in f))
PLACEMENTS = sorted(set(PLACEMENTS))
BY_CELL = defaultdict(list)
for pi, s in enumerate(PLACEMENTS):
    for c in s:
        BY_CELL[c].append(pi)

# 8 symmetries of the square board [0,16]^2, center-pivoted (cell = y*C + x)
def _mk(f):
    # lookup table: entry[c] = image of cell c (cell = y*C + x)
    return tuple(f(x, y)[1] * C + f(x, y)[0]
                 for y in range(R) for x in range(C))


def d4_cell(g, c):
    return g[c]


D4 = []
for name, f in [
    ("id", lambda x, y: (x, y)),
    ("r90", lambda x, y: (C - 1 - y, x)),
    ("r180", lambda x, y: (C - 1 - x, R - 1 - y)),
    ("r270", lambda x, y: (y, R - 1 - x)),
    ("fx", lambda x, y: (C - 1 - x, y)),
    ("fy", lambda x, y: (x, R - 1 - y)),
    ("fd", lambda x, y: (y, x)),
    ("fa", lambda x, y: (C - 1 - y, R - 1 - x)),
]:
    D4.append(tuple(_mk(f)))


def canon(M, B):
    """D4-canonical key of a position; None if some transform leaves the board
    (cannot happen for full-board positions, all transforms preserve 17x17)."""
    best = None
    Ms, Bs = frozenset(M), frozenset(B)
    for m in D4:
        M2 = frozenset(d4_cell(m, c) for c in Ms)
        B2 = frozenset(d4_cell(m, c) for c in Bs)
        key = (tuple(sorted(M2)), tuple(sorted(B2)))
        if best is None or key < best:
            best = key
    return best


def statics(name, pos):
    M = set(idx(tuple(c)) for c in pos["maker_M"]) | {idx(tuple(pos["maker_p"]))}
    B = set(idx(tuple(c)) for c in pos["breaker_B"])
    live = [i for i, s in enumerate(PLACEMENTS) if s.isdisjoint(B)]
    live_set = set(live)
    touch_M = [i for i in live if PLACEMENTS[i] & M]
    relevant = set()
    for i in touch_M:
        relevant |= PLACEMENTS[i]
    relevant_free = relevant - M - B
    touching = relevant_free  # Breaker replies that touch Maker's structure
    overlap = Counter(len(PLACEMENTS[i] & M) for i in touch_M)
    # best single cell for Maker: max # of placements it completes toward
    cellgain = Counter()
    for c in relevant_free:
        cellgain[c] = len(set(BY_CELL[c]) & set(touch_M))
    # D4 stabilizer of the raw position (incl. board frame)
    Ms, Bs = frozenset(M), frozenset(B)
    stab = []
    for m in D4:
        M2 = frozenset(d4_cell(m, c) for c in Ms)
        B2 = frozenset(d4_cell(m, c) for c in Bs)
        if M2 == Ms and B2 == Bs:
            stab.append(m)
    print(f"--- {name}: |M∪p|={len(M)} |B|={len(B)}")
    print(f"    placements total={len(PLACEMENTS)} live={len(live)} "
          f"live∩Maker={len(touch_M)}")
    print(f"    overlap hist (Maker cells per live placement): "
          f"{dict(sorted(overlap.items()))}")
    print(f"    relevant free cells (Maker ply-1 candidates): {len(relevant_free)}")
    print(f"    touching cells (Breaker replies that matter): {len(touching)}")
    print(f"    best ply-1 cell reaches {max(cellgain.values()) if cellgain else 0} "
          f"live placements")
    print(f"    D4 stabilizer size: {len(stab)}")
    return {"live": len(live), "live_M": len(touch_M),
            "relevant": len(relevant_free), "touching": len(touching),
            "stab": len(stab)}


def threat_tree(name, pos, deadline, node_cap=2_000_000):
    """Depth-limited AND/OR expansion, nodes per ply.  OR moves: relevant free
    cells.  AND moves: forced level-1 block if any, else all touching cells.
    Memoized on D4-canonical (M,B).  Terminal: Maker owns a placement (WIN),
    or 0 moves left (LOSS for this truncation)."""
    M0 = frozenset(idx(tuple(c)) for c in pos["maker_M"]) | {idx(tuple(pos["maker_p"]))}
    B0 = frozenset(idx(tuple(c)) for c in pos["breaker_B"])

    def live_touch(M, B):
        """live placements meeting M, and the touching free cells."""
        acc = set()
        for c in M:
            for pi in BY_CELL[c]:
                if PLACEMENTS[pi].isdisjoint(B):
                    acc.add(pi)
        rel = set()
        for pi in acc:
            rel |= PLACEMENTS[pi]
        return rel - M - B, acc

    def threats(M, B, acc):
        """level-1 threats: live placements with exactly one non-Maker cell;
        returns the dict empty-cell -> #placements, or WIN flag."""
        t = defaultdict(int)
        for pi in acc:
            miss = PLACEMENTS[pi] - M
            if len(miss) == 1:
                t[next(iter(miss))] += 1
        return t

    nodes = Counter()
    memo = {}
    t0 = time.time()
    aborted = [False]

    def or_node(M, B, k, depth):
        """Maker to move, k claims left.  Returns 'W' win / 'L' not-proven."""
        if time.time() > deadline or sum(nodes.values()) > node_cap:
            aborted[0] = True
            raise TimeoutError
        key = (canon(M, B), k)
        if key in memo:
            nodes[depth] += 0
            return memo[key]
        nodes[depth] += 1
        own = set()
        for c in M:
            for pi in BY_CELL[c]:
                if PLACEMENTS[pi].isdisjoint(B):
                    own.add(pi)
        if any(PLACEMENTS[pi] <= M for pi in own):
            memo[key] = "W"
            return "W"
        if k == 0:
            memo[key] = "L"
            return "L"
        touching, _ = live_touch(M, B)
        result = "L"
        for m in touching:
            M2 = M | {m}
            r = and_node(M2, B, k - 1, depth + 1)
            if r == "W":
                result = "W"
                break
        memo[key] = result
        return result

    def and_node(M, B, k, depth):
        """Breaker to move.  Forced to block level-1 threats; if two disjoint
        threat cells exist Maker wins anyway -> 'W'.  Else all touching replies,
        Maker needs 'W' against EVERY one."""
        if time.time() > deadline or sum(nodes.values()) > node_cap:
            aborted[0] = True
            raise TimeoutError
        own = set()
        for c in M:
            for pi in BY_CELL[c]:
                if PLACEMENTS[pi].isdisjoint(B):
                    own.add(pi)
        if any(PLACEMENTS[pi] <= M for pi in own):
            return "W"  # Breaker to move but Maker already owns a placement:
            # cannot happen in legal alternation; guarded anyway
        t = threats(M, B, own)
        if len(t) >= 2:
            nodes[depth] += 1
            return "W"  # double threat: Breaker blocks one, Maker takes other
        if len(t) == 1:
            w = next(iter(t))
            nodes[depth] += 1
            return or_node(M, B | {w}, k, depth + 1)
        if k == 0:
            nodes[depth] += 1
            return "L"
        touching, _ = live_touch(M, B)
        # dominated-reply reduction: replies outside `touching` cannot touch any
        # live placement meeting M (they kill nothing Maker needs) -> treated as
        # one canonical "far" reply (R1/R2 monotonicity)
        nodes[depth] += 1
        for b in touching:
            if and_child_loses(M, B | {b}, k, depth):
                return "L"
        return or_node(M, B | frozenset(), k, depth + 1)  # the "far" reply

    def and_child_loses(M, B, k, depth):
        try:
            return or_node(M, B, k, depth + 1) == "L"
        except TimeoutError:
            raise

    root_touching, _ = live_touch(M0, B0)
    print(f"--- {name}: threat/AND-OR truncation (root relevant moves "
          f"{len(root_touching)})")
    verdict = "?"
    try:
        verdict = or_node(M0, B0, 16, 0)
    except TimeoutError:
        pass
    el = time.time() - t0
    tot = sum(nodes.values())
    print(f"    verdict so far: {verdict}  nodes={tot} in {el:.1f}s "
          f"({tot / max(el, 1e-9):,.0f}/s) aborted={aborted[0]}")
    for d in sorted(nodes):
        if nodes[d]:
            print(f"    ply {d}: {nodes[d]} nodes")
    # growth factor between consecutive measured OR levels
    ors = [nodes[d] for d in sorted(nodes) if d % 2 == 0 and nodes[d] > 1]
    if len(ors) >= 2:
        gs = [b / a for a, b in zip(ors, ors[1:])]
        print(f"    OR-level growth factors: {['%.1f' % g for g in gs]}")
    return tot, verdict, aborted[0]


def main():
    pos = json.load(open("/tmp/snaky/inc19/probe/positions.json"))
    st = {}
    for name in ("1036a", "1608", "1701"):
        st[name] = statics(name, pos[name])

    # main sizing target: 1036 (shared card, serves both forcing lines)
    t_end = time.time() + 240  # 4 min cap, far under the 20-min ceiling
    tot, verdict, ab = threat_tree("1036a", pos["1036a"], t_end)

    print("\n=== sizing summary ===")
    for name, s in st.items():
        print(f"{name}: relevant={s['relevant']} touching={s['touching']} "
              f"stab={s['stab']}")
    print(f"truncation nodes={tot} verdict={verdict} aborted={ab}")


if __name__ == "__main__":
    main()
