#!/usr/bin/env python3
"""inc19 probe task 2b: exact node counts of complete k-truncations.

For k = 4, 6, ... run the AND/OR search to completion ("can Maker win within k
claims from the card-1036 position in the reply-reduced game") and record the
exact node count.  Growth per +2 claims anchors the full k=16 estimate.

Reductions (documented, conservative):
  - OR moves restricted to cells of live placements meeting the current Maker
    set (threat-space / R2-analog restriction; excludes far fresh starts);
  - AND moves = all touching free cells + one canonical "far" reply (pass);
    the real game has ~215 more Breaker replies per rest, so these counts are
    LOWER bounds on the real proof/refutation sizes in both directions.
Node counts are exact for the reduced game: L-verdict = full refutation tree,
W-verdict = full winning-strategy tree (within the restrictions).
"""
import json
import sys
import time
from collections import Counter, defaultdict

sys.path.insert(0, "/tmp/snaky/inc19/probe")
from size_search import PLACEMENTS, BY_CELL, canon, idx  # noqa: E402


def run(pos, k, node_cap=8_000_000, seconds=900):
    M0 = frozenset(idx(tuple(c)) for c in pos["maker_M"]) | {idx(tuple(pos["maker_p"]))}
    B0 = frozenset(idx(tuple(c)) for c in pos["breaker_B"])
    nodes = Counter()
    memo = {}
    budget = {"n": 0, "t0": time.time(), "cap": node_cap, "sec": seconds,
              "hit": False}

    class TO(Exception):
        pass

    def live_touch(M, B):
        acc = set()
        for c in M:
            for pi in BY_CELL[c]:
                if PLACEMENTS[pi].isdisjoint(B):
                    acc.add(pi)
        rel = set()
        for pi in acc:
            rel |= PLACEMENTS[pi]
        return rel - M - B, acc

    def tick(depth):
        budget["n"] += 1
        nodes[depth] += 1
        if budget["n"] > budget["cap"] or time.time() - budget["t0"] > budget["sec"]:
            raise TO

    def own_live(M, B):
        own = set()
        for c in M:
            for pi in BY_CELL[c]:
                if PLACEMENTS[pi].isdisjoint(B):
                    own.add(pi)
        return own

    def won_now(M, own):
        return any(PLACEMENTS[pi] <= M for pi in own)

    def threats(M, own):
        t = defaultdict(int)
        for pi in own:
            miss = PLACEMENTS[pi] - M
            if len(miss) == 1:
                t[next(iter(miss))] += 1
        return t

    def or_node(M, B, k, d):
        key = (canon(M, B), k)
        if key in memo:
            return memo[key]
        tick(d)
        own = own_live(M, B)
        if won_now(M, own):
            memo[key] = "W"
            return "W"
        if k == 0:
            memo[key] = "L"
            return "L"
        touching, _ = live_touch(M, B)
        res = "L"
        for m in touching:
            if and_node(M | {m}, B, k - 1, d + 1) == "W":
                res = "W"
                break
        memo[key] = res
        return res

    def and_node(M, B, k, d):
        tick(d)
        own = own_live(M, B)
        if won_now(M, own):
            return "W"
        t = threats(M, own)
        if len(t) >= 2:
            return "W"
        if len(t) == 1:
            return or_node(M, B | {next(iter(t))}, k, d + 1)
        if k == 0:
            return "L"
        touching, _ = live_touch(M, B)
        for b in touching:
            if or_node(M, B | {b}, k, d + 1) == "L":
                return "L"
        return or_node(M, B, k, d + 1)  # far replies collapsed to pass

    try:
        v = or_node(M0, B0, k, 0)
        return v, sum(nodes.values()), dict(sorted(nodes.items())), False
    except TO:
        return "?", sum(nodes.values()), dict(sorted(nodes.items())), True


def main():
    pos = json.load(open("/tmp/snaky/inc19/probe/positions.json"))["1036a"]
    print("k  verdict  nodes      seconds  aborted")
    rows = []
    for k in (4, 6, 8, 10, 12, 14):
        t0 = time.time()
        v, n, per, ab = run(pos, k, node_cap=4_000_000, seconds=600)
        el = time.time() - t0
        rows.append((k, v, n, el, ab))
        print(f"{k}  {v}  {n:>9,}  {el:8.1f}  {ab}")
        sys.stdout.flush()
        if ab:
            break
    comp = [r for r in rows if not r[4]]
    if len(comp) >= 2:
        print("\ngrowth per +2 claims (complete truncations):")
        for a, b in zip(comp, comp[1:]):
            if a[2] and b[2]:
                print(f"  k={a[0]}->{b[0]}: x{b[2] / a[2]:.1f}")
        last = comp[-1]
        if last[2]:
            per2 = last[2] ** (16 / last[0]) if last[2] > 1 else 0
            print(f"  naive extrapolation to k=16 from k={last[0]}: "
                  f"~10^{(16 / last[0]) * (last[2] and __import__('math').log10(last[2])):.1f}")


if __name__ == "__main__":
    main()
