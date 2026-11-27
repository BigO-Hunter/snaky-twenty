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

## Folded staging sibling — `conditional/`

`conditional/` is the former `snaky-conditional` repo (source commit
`6bc844850b43fbbc92a0a21ba84531d015634b79`), merged with full history. It was the
same-result Bound-20 *staging* tree — `Race.bound` from `Snaky.race_bound_20` against a
vendored statement, meant to be swapped byte-for-byte for the maintainer's posted
statement on filing day. That purpose is consumed: Bound-20 was filed from this repo's
root `Submission/` against the byte-exact `SnakyStatement.lean`. It is kept for its
reusable technique, not as a second submission:

- `Submission/SnakyConditional.lean` — Prototype→Conditional **def-bridge** (namespace
  transport lemmas `playState_eq` / `makerAt_eq` / `legal_eq` / `hasSnaky_eq`).
- `Submission/Padding.lean` — **Bound-35 transport**: pads the verified Bound-20 win to
  horizon 35 (`Snaky.race_bound_35`) via the r-genericity counter shift.
- `verify.sh` + `AxiomCheck.lean` — **6-check harness** (build green, zero sorry, axioms
  exactly 3, `-DautoImplicit=false`, statement byte-exact sha256, bare-import audit).
- `target/` — corpus target statement + sha256 witness; `.gitattributes` (`* -text`)
  pins line endings byte-exact.

Build/audit from its own directory: `cd conditional && lake build Submission.SnakyConditional`
(same v4.34.1 / Mathlib d13f23b7 pins).

---

## Why this repo is up

Reproducible verified bounds: the snaky Bound-20 filing package keeps the board's first Lean Verified row independently rebuildable against byte-exact pins.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Bound 20 is filed and verified. Open work: independent rebuilds against the byte-exact pins; Bound-21+ exploration (Bound-19 lives in snaky-nineteen).

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE) ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf)). Vendored third-party material keeps its upstream license — see [NOTICE](NOTICE.md).
