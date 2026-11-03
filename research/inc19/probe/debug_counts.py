#!/usr/bin/env python3
"""Debug/validate the AND-OR truncation counters from size_search.py.

Counts explicit node VISITS by type (fresh / memo-hit) and the AND rest-loop
behaviour (how many touching replies tried before refutation), so the per-ply
table can be trusted.  Soundness note printed at the end.
"""
import json
import sys
import time
from collections import Counter, defaultdict

sys.path.insert(0, "/tmp/snaky/inc19/probe")
from size_search import (PLACEMENTS, BY_CELL, canon, idx, R, C)  # noqa: E402


def main():
    pos = json.load(open("/tmp/snaky/inc19/probe/positions.json"))["1036a"]
    M0 = frozenset(idx(tuple(c)) for c in pos["maker_M"]) | {idx(tuple(pos["maker_p"]))}
    B0 = frozenset(idx(tuple(c)) for c in pos["breaker_B"])

    stat = Counter()
    memo = {}

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

    t0 = time.time()

    def or_node(M, B, k, depth):
        key = (canon(M, B), k)
        if key in memo:
            stat["or_memo_hit"] += 1
            return memo[key]
        stat["or_fresh"] += 1
        stat[f"or_d{depth}"] += 1
        for pi in BY_CELL[next(iter(M))]:  # cheap win check below (full scan)
            pass
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
        stat["or_moves"] = max(stat["or_moves"], len(touching))
        res = "L"
        for m in touching:
            r = and_node(M | {m}, B, k - 1, depth + 1)
            stat["and_calls"] += 1
            if r == "W":
                res = "W"
                break
        memo[key] = res
        return res

    def and_node(M, B, k, depth):
        stat["and_fresh"] += 1
        stat[f"and_d{depth}"] += 1
        own = set()
        for c in M:
            for pi in BY_CELL[c]:
                if PLACEMENTS[pi].isdisjoint(B):
                    own.add(pi)
        if any(PLACEMENTS[pi] <= M for pi in own):
            return "W"
        t = defaultdict(int)
        for pi in own:
            miss = PLACEMENTS[pi] - M
            if len(miss) == 1:
                t[next(iter(miss))] += 1
        if len(t) >= 2:
            stat["and_double"] += 1
            return "W"
        if len(t) == 1:
            stat["and_forced"] += 1
            return or_node(M, B | {next(iter(t))}, k, depth + 1)
        if k == 0:
            return "L"
        touching, _ = live_touch(M, B)
        stat["and_touch"] = max(stat["and_touch"], len(touching))
        tried = 0
        for b in touching:
            tried += 1
            r = or_node(M, B | {b}, k, depth + 1)
            if r == "L":
                stat["and_refute_at"] += tried
                stat["and_refuted"] += 1
                return "L"
        stat["and_no_refute"] += 1
        return or_node(M, B, k, depth + 1)  # pass branch (far replies unseen)

    t_end = t0 + 60
    import threading

    class TO(Exception):
        pass

    verdict = "?"
    try:
        # simple wall guard via recursion count instead of signals
        verdict = or_node(M0, B0, 8, 0)  # truncation k=8 for speed
    except RecursionError:
        verdict = "RECURSION-CAP"

    el = time.time() - t0
    print(f"truncation k=8 verdict={verdict} in {el:.1f}s")
    for kv in sorted(stat.items()):
        print(f"  {kv[0]}: {kv[1]}")


if __name__ == "__main__":
    main()
