# SCOPE — snaky Bound 19 (darkhipo inc19) — 2026-11-02

Files: this, `OUTREACH_DRAFT.md` (DO NOT SEND), `profile_gen17.py`, `tighten.py`.

## Path A — outreach: DRAFTED, not sent

`OUTREACH_DRAFT.md`: asks shjvandekamp to license Result19 (any license) or
authorize collaboration; we bridge their kernel-checked table to the board's
Bound-19 shape (total fresh Policy + legality bookkeeping + exact counts — the
G2/G3 delta already solved for 20); first Lean Verified 19 row with their name +
repo attribution. Credibility = our smoke-run Bound 20. Send the hour LV-20
lands. Response 2–4 d; our bridge after grant ≈ 1–2 d.

## Path B — own constructor

### B0 (height-bookkeeping shortcut): DEAD — proved by experiment

Recomputed every card's true height (`t=1` if A+p holds a placement, else
`1+max t(children)`): **stored heights are exactly tight** (0 slack; histograms
identical; root tight = 20). No re-storing yields 19; gotrevor's "kernel rejects
bound 19" is this table's true bound.

### B1 (delta): the 20→19 gap is THREE positions — measured

Root card 1737 (p=center (8,8), S=251) is h=20 solely via the center-adjacent
replies {(7,8),(8,7),(8,9)} ((9,8) symmetry-covered) → card 1736 (h=19,
M={(8,8)}, B={(7,8)}; 94% of the table — 1,629/1,738 cards — in its subtree).
1736's 224 children: only 2 force h=18 ((6,8)→1668, (7,7)→1702). 1668's 168
children: 3 force h=17 ((3,8),(4,8)→1036 shared, (6,8)→1608); 1702: 1
((7,9)→1701). All other children ≤ needed.

**Frontier = re-prove cards {1036, 1608, 1701} at h=16** (now 17). If all three
drop, heights cascade: 1668/1702→17, 1736→18, root→19. Reconstruct frontier
positions in absolute coordinates by composing hint transforms along the paths.

### B2 (search formulation + state space)

AND/OR tree per frontier position: OR=Maker claim, AND=Breaker reply, objective =
snaky within 16 more claims; canonicalize under the one surviving symmetry
(horizontal reflection) + transposition on (M,B); λ-search threat-space pruning
(the method of gotrevor's 15x15 search; their search repo is NOT public — we
write our own).

- **Naive**: branching ~100–150, depth 32 plies ⇒ ~10^60–10^70 nodes/position —
  infeasible by ~55 orders of magnitude.
- **λ-search estimate**: precedent compression (15x15 certificate = 1.46×10^8
  node-positions; these subproblems are smaller, ~2 plies shallower) ⇒
  **10^6–10^8 node-positions per position**; feasible in a compiled (Rust/Go)
  prover, hours–days each. Stdlib Python here ~1.4×10^5 verify-pos/s and 10–100×
  slower searching — adequate only at the low end; recommend compiled.
- **QBF alternative**: corrective encoding (SAT 2020, the 9x9 method):
  ∃Maker ∀Breaker, ~1,664 placements × 32 plies ⇒ ~10^5 vars/10^6 clauses.
  Encodable quickly, solve time at depth 16–18 unpredictable — one bounded
  experiment, not the main line.
- A bounded frontier failure is **inconclusive**; ladder: re-prove 1736@18 via
  different children → different opening / wider window (full re-search; cf.
  shjvandekamp 3,468 cards vs gotrevor 1,738 / 38,357 edges; brief-relayed
  "61,040 replies" — unverified, no fetch).

### Formalization reuse map

Table-agnostic (any new table): `cardStrategy`, `cardStrategy_fresh`
(PlanePolicy.lean:144/147); `plane_sound_aux` (Plane.lean:159);
`wonPlane_to_hasSnaky`; G3 pack `playState_fst_card/snd_card/disjoint/
disjoint_final` (already N-parameterized); `cardOK`/`rootOK`/`CTree.sound_in`;
pipelines `tools/cards2lean.py`, `checker/check.py`, Lean `cardcheck`.
Table-specific (regenerate): `Gen19/` data + chunk `tK_ok` decides
(`cards2lean.py --name=Gen19`); `Gen19.root_height ≤ 19` (decide);
`plane_snaky_wins_in_19` (Plane17.lean:17 analog); `cardStrategy_wins_20`→`_19`
(PlanePolicy.lean:379 — literal-20 edits only; induction runs on N−k); G3
instantiation at N=19. Post-search formalization ≈ 1–2 d (~2× Gen17's 81 modules).

## Effort + sequencing

- **A**: 0 d spent; +2–4 d (their response dominates). Dominant — short-circuits B.
- **B**: prover 2–5 d eng + 1–3 d runs (uncertain) + 1–2 d formalization ⇒
  +7–14 d, matching the brief.
- **Sequencing**: send A the hour LV-20 lands; start B2 frontier prover in
  parallel regardless (also strengthens A — the frontier analysis is our
  collaboration contribution). If both land, file A's table; B stays as
  corroboration (clean-room: B never reads A's material).

## Top-3 risks

1. **Clean-room breach**: license=null — only README-level counts (3,468 cards,
   kernel-checked, 1,181 modules) may inform us. Boundary held (nothing fetched).
2. **Frontier re-search fails**: h=16 may be unattainable; days of compute →
   inconclusive, ladder escalates steeply. Mitigate: bound each run, parallel QBF
   probe, escalate in order.
3. **Integration**: 2× kernel modules under pins; one-canonical-package
   coordination hazard (G3 note); cascade must be re-verified by cardcheck AND
   kernel, not our Python alone.
