#!/usr/bin/env python3
"""inc19 probe: what does the STORED h=17 proof do from card 1036?
Walk the deepest tight children from 1036 for ~8 plies in absolute coordinates
to see the shape of a 17-claim win — informs whether a 16-claim re-proof can
reuse its opening.
"""
import sys

sys.path.insert(0, "/tmp/snaky/gotrevor/tools")
from cards2lean import parse  # noqa: E402
from reconstruct import app, comp, ORIENT  # noqa: E402

PATH = "/tmp/snaky/gotrevor/third_party/sieben/cards-17x17.txt"


def main():
    hdr, cards = parse(PATH)
    rows, cols, root, (k0, dx0, dy0) = hdr
    G = (*ORIENT[k0], dx0, dy0)
    i = root
    # descend the skeleton to card 1036 (edge via reply (3,8) from 1668)
    for target, w in [(1736, (7, 8)), (1668, (6, 8)), (1036, (3, 8))]:
        for w2, h in cards[i]["replies"]:
            if w2 == w:
                G = comp(G, (*ORIENT[h[1]], h[2], h[3]))
                i = h[0]
                break
        assert i == target
    print(f"at card {i} (h={cards[i]['h']})")

    # greedy walk: at each card, follow the tight child (h == parent h - 1) with
    # the largest subtree proxy = its own stored h tightness; ties -> first.
    M, B = set(), set()
    for step in range(9):
        c = cards[i]
        p_abs = app(G, c["p"])
        M.add(p_abs)
        # choose the tight reply child with smallest h (deepest line)
        best = None
        for w2, h in sorted(c["replies"]):
            j = h[0]
            if cards[j]["h"] == c["h"] - 1:
                best = (w2, h)
                break
        if best is None:
            pass_child = c["pass"]
            if pass_child:
                best = ("pass", pass_child)
            else:
                print(f"ply {step}: card {i} h={c['h']} p={p_abs} — no tight child "
                      f"(won leaf or branching frontier)")
                break
        w2, h = best
        b_abs = app(G, w2) if w2 != "pass" else None
        if b_abs:
            B.add(b_abs)
        G = comp(G, (*ORIENT[h[1]], h[2], h[3]))
        i = h[0]
        mtxt = " ".join(f"({a[0]},{a[1]})" for a in sorted(M))
        btxt = " ".join(f"({a[0]},{a[1]})" for a in sorted(B))
        print(f"ply {step+1}: -> card {i} h={cards[i]['h']} "
              f"breaker_reply={b_abs} "
              f"via {'pass' if w2 == 'pass' else 'reply'}")
        print(f"   M = {mtxt}")
        print(f"   B = {btxt}")


if __name__ == "__main__":
    main()
