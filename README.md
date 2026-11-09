# SNAKY Bound-20 submission package

Filing package for the Big O Speedrun Snaky challenge (bigospeedrun/verifier,
issue #106): Maker forces a Snaky within 20 own claims against every legal
Breaker sequence — full `Bound 20` (win + exact card counts + disjointness).

## Layout (maintainer contract, 2026-11-02 18:53Z)

The ONLY source root is `Submission/`:

- `Submission/SnakyStatement.lean` — the maintainer's self-contained statement
  file, copied **byte-for-byte** from
  `bigospeedrun/verifier@1f893c0a3e4828675be3a8d268df0fddaa0fe9ba`
  `challenges/other-snaky/VerifierStatement.lean`
  (sha256 `49e630b3bab9a3d1006b373edd85cf196eba0f45bdb878e0126db16776ed780b`).
- `Submission.lean` (repo root) — solution module; exports exactly
  `theorem Race.bound : BigOSpeedrun.Snaky.Bound 20`.
- `Submission/{Game,Cards,CardsSound,Bounded,Controls}.lean` — the vendored
  gotrevor card world (Apache-2.0, see NOTICE).
- `Submission/Gen17/*.lean` — the 1,738-card verified table
  (`decide +kernel`, no `native_decide`).
- `Submission/{Plane,Plane17,PlanePolicy,PlaneBound}.lean` — the plane bridge
  (G1/G2) and the `Bound` bookkeeping pack (G3).

## Pins

Toolchain `leanprover/lean4:v4.34.1`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` (the rev of
`profiles/lake-manifest.json` in the verifier repo at the statement commit).

Build locally: `lake update && lake exe cache get && lake build Submission`.

---

## Why this repo is up

Reproducible verified bounds: the snaky Bound-20 filing package keeps the board's first Lean Verified row independently rebuildable against byte-exact pins.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Bound 20 is filed and verified. Open work: independent rebuilds against the byte-exact pins; Bound-21+ exploration (Bound-19 lives in snaky-nineteen).

## License

Licensed under Apache-2.0 — see [LICENSE](LICENSE)., with vendored portions named in [NOTICE](NOTICE.md) keeping their upstream licenses
