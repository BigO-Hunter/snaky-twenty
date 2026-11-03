#!/usr/bin/env python3
"""inc19 probe task 1: reconstruct the three frontier positions (cards 1036, 1608,
1701) in absolute 17x17 board coordinates, walking the exact SCOPE.md skeleton.

Card semantics (gotrevor lean/Snaky/Cards.lean):
  A  = Maker's cells BEFORE this card's claim p (root: A = []); p must lie in S
  S  = zone of free cells needing Breaker-reply children (pass covers the rest)
  hint (j,k,dx,dy): child j's Xf H maps child coords into the citing card's frame
  (app: parent_pt = a*x+b*y+dx, c*x+d*y+dy; comp g g' = g.app ∘ g'.app).
  hintOK: child.A all land in parent's (p::A); child.S ⊆ parent's S minus reply.
  Header Xf maps the ROOT card's coords to board coords (here: identity).
Writes probe/positions.json.
"""
import json
import sys

sys.path.insert(0, "/tmp/snaky/gotrevor/tools")
from cards2lean import parse  # noqa: E402

PATH = "/tmp/snaky/gotrevor/third_party/sieben/cards-17x17.txt"
OUT = "/tmp/snaky/inc19/probe/positions.json"
R = C = 17

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


def app(G, p):
    a, b, c, d, dx, dy = G
    return (a * p[0] + b * p[1] + dx, c * p[0] + d * p[1] + dy)


def comp(G, H):
    a, b, c, d, dx, dy = G
    a2, b2, c2, d2, dx2, dy2 = H
    return (a * a2 + b * c2, a * b2 + b * d2, c * a2 + d * c2, c * b2 + d * d2,
            a * dx2 + b * dy2 + dx, c * dx2 + d * dy2 + dy)


def won(owned):
    owned = set(owned)
    for f in FORMS:
        for q in owned:
            t = (q[0] - f[0][0], q[1] - f[0][1])
            if all((u[0] + t[0], u[1] + t[1]) in owned for u in f):
                return True
    return False


def main():
    hdr, cards = parse(PATH)
    rows, cols, root, (k0, dx0, dy0) = hdr
    assert (rows, cols) == (R, C)
    G0 = (*ORIENT[k0], dx0, dy0)
    print(f"header: root_idx={root} ncards={len(cards)} hdr_xf=k{k0} d=({dx0},{dy0})")

    rc = cards[root]
    rp = app(G0, rc["p"])
    assert rp == (8, 8) and rc["h"] == 20 and len(rc["S"]) == 251 and not rc["A"]
    print(f"root: h=20 |S|=251 p->board (8,8): OK")

    # skeleton: list of (label, [reply cell at each hop]) — card indices asserted
    # 1737=root -(7,8)-> 1736 -(6,8)-> 1668 -(3,8)|(4,8)-> 1036 ; -(6,8)-> 1608
    #                       \-(7,7)-> 1702 -(7,9)-> 1701
    skel = [
        ("1736", [(1736, (7, 8))], 19),
        ("1668", [(1736, (7, 8)), (1668, (6, 8))], 18),
        ("1036a", [(1736, (7, 8)), (1668, (6, 8)), (1036, (3, 8))], 17),
        ("1036b", [(1736, (7, 8)), (1668, (6, 8)), (1036, (4, 8))], 17),
        ("1608", [(1736, (7, 8)), (1668, (6, 8)), (1608, (6, 8))], 17),
        ("1702", [(1736, (7, 8)), (1702, (7, 7))], 18),
        ("1701", [(1736, (7, 8)), (1702, (7, 7)), (1701, (7, 9))], 17),
    ]

    out = {}
    for name, path, h in skel:
        G = G0
        i = root
        B = []
        for j_expect, w in path:
            hh = None
            for w2, hint in cards[i]["replies"]:
                if w2 == w:
                    hh = hint
                    break
            assert hh is not None, f"{name}: card {i} lacks reply {w}"
            H = (*ORIENT[hh[1]], hh[2], hh[3])
            Gj = comp(G, H)
            j = hh[0]
            assert j == j_expect, f"{name}: hop -> card {j} != {j_expect}"
            # invariant checks (hintOK): child A lands in parent's p::A,
            # child S stays inside parent's S minus w
            child = cards[j]
            parent_owned = set(app(G, a) for a in cards[i]["A"]) | {app(G, cards[i]["p"])}
            childA = [app(Gj, a) for a in child["A"]]
            assert set(childA) <= parent_owned, f"{name}: child A not in parent p::A"
            parentS = set(app(G, s) for s in cards[i]["S"]) - {app(G, w)}
            childS = [app(Gj, s) for s in child["S"]]
            assert set(childS) <= parentS, f"{name}: child S escapes parent S minus w"
            B.append(app(G, w))  # breaker cell in the CITING frame
            G, i = Gj, j
        c = cards[i]
        assert c["h"] == h, f"{name}: h={c['h']} != {h}"
        M = sorted(set(app(G, a) for a in c["A"]))
        S = sorted(set(app(G, s) for s in c["S"]))
        p = app(G, c["p"])
        B = sorted(set(B))
        assert p in S, f"{name}: p not in zone"
        assert not (set(M) & set(B)), f"{name}: M/B overlap"
        assert not (set(S) & set(B)), f"{name}: zone overlaps breaker"
        assert set(M) <= set(S) or True  # M cells may have left the zone
        owned = set(M) | {p}
        free = sorted((x, y) for x in range(C) for y in range(R)
                      if (x, y) not in owned and (x, y) not in set(B))
        out[name] = {
            "card": i, "path": [[ci, list(w)] for ci, w in path],
            "stored_h": c["h"],
            "maker_M": [list(m) for m in M], "maker_p": list(p),
            "breaker_B": [list(b) for b in B], "zone_S": [list(s) for s in S],
            "n_free": len(free), "n_zone": len(S),
            "won_after_p": won(owned),
        }
        print(f"{name}: card {i} h={c['h']} |M|={len(M)} M={M} +p={p} |B|={len(B)} "
              f"B={B} |S|={len(S)} |free|={len(free)} won={won(owned)} "
              f"reply_children={len(c['replies'])} pass={'Y' if c['pass'] else 'N'}")

    assert out["1736"]["maker_M"] == [[8, 8]]
    assert out["1736"]["breaker_B"] == [[7, 8]]
    assert out["1036a"]["maker_M"] == out["1036b"]["maker_M"]
    assert out["1036a"]["zone_S"] == out["1036b"]["zone_S"]
    ba = set(map(tuple, out["1036a"]["breaker_B"]))
    bb = set(map(tuple, out["1036b"]["breaker_B"]))
    print(f"1036 shared-card check: identical M and S; B symmetric difference "
          f"{sorted(ba ^ bb)}")

    with open(OUT, "w") as f:
        json.dump(out, f)
    print(f"wrote {OUT} ({len(json.dumps(out))} bytes)")


if __name__ == "__main__":
    main()
