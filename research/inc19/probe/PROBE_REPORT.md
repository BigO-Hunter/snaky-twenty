# PROBE_REPORT — inc19 Path-B frontier sizing (2026-11-02)

## 1. Frontier positions (absolute 17×17 coords, Maker to move)

Reconstructed by composing hint `Xf`s along the SCOPE skeleton; every step
checked against `hintOK` invariants (child A ⊆ parent p::A, child S ⊆ S∖{w});
card counts match SCOPE (root p=(8,8) |S|=251 h=20; 1736 has 224 children; 1668
168). Machine-readable: `positions.json`.

| card | Maker M (before claim) | claim p | Breaker B | zone S | free |
|---|---|---|---|---|---|
| 1036 (shared) | (8,8),(8,9),(11,8) | (11,9) | (7,8),(8,10),(13,8) — or (12,8) | 118 | 282 |
| 1608 | same M | (11,9) | (7,8),(8,10),(10,8) | 157 | 282 |
| 1701 | (8,8),(8,9),(8,10) | (11,8) | (7,8),(7,10),(9,9) | 94 | 282 |

1036's two citing replies give identical M and S; B differs exactly in
{(12,8) vs (13,8)} — the card is genuinely shared. Stored h=17 on all three;
target h=16.

## 2. Search sizing (`size_search.py`, `size_truncations.py`)

Static: 1,664 placements total, 1,528–1,536 live, 72–85 live∩Maker; **max
overlap 3 → no placement finishable within 2 Maker claims** (SAT-confirmed);
relevant free cells 67 (ply-1 candidates, all three positions); Breaker
touching replies 67; **D4 stabilizer trivial at all three** → no root symmetry
reduction; canonicalization merges only move-order revisits.

AND/OR growth (reductions: Breaker limited to touching+pass ≈67–150 replies;
Maker restricted to cells of live placements meeting Maker; memo on
D4-canonical states):

| truncation | verdict | nodes | time | complete? |
|---|---|---|---|---|
| k=4 | L (true answer) | >4.0×10⁶ | 257 s @15.5k/s | **NO** |

Measured per-OR-level growth ≈ **×134** (67 moves × ~2 reply children).
Projection: reduced k=16 ≈ **10¹⁷–10¹⁸ nodes**; full-reply game ×~4 AND
branching. Compiled at 10⁷ nodes/s ⇒ 10⁹–10¹⁰ s — centuries. The λ-search /
threat-space layer must supply **≥9 orders** of compression. The 15×15
precedent (1.46×10⁸ positions vs ~10⁴⁸ naive) proves such compression exists
for snaky — but gotrevor's search repo is not public, and reproducing it is the
campaign's whole risk.

Stored-strategy check (`stored_shape.py`): from 1036 the tight line decays
h=17→8 in 9 plies **with no slack** (gradual row-y=6 buildup, Breaker
absorbing adjacent blocks). A 16-claim re-proof must beat the stored defense
by a full claim — genuinely new search, not re-storage.

## 3. Encoding experiment (`encode_sat.py`)

Exact depth-2 adversarial SAT built and solved with CaDiCaL (pysat, pip
installed): per-Breaker-reply clauses over finishable placements (1-away →
x_c; 2-away → x_c1∨x_c2, with b∉π). Cross-validated vs direct double-threat
enumeration: **AGREE** on the real position (no win-in-2 — zero ≤2-away
placements) and on two synthetic controls. Depth-16: the expansion tree IS the
task-2 tree (~10¹⁷ nodes × ~10 literals) — no stand-alone SAT win. QBF
∃m₁∀b₁…∃m₁₆ (~10³ exist + ~4.5×10³ univ vars) is encodable in ~1 day but no
QBF solver on this host; depth-16 solve behaviour unknown — not decisive.

## 4. Verdict: NO-GO for Path B as scoped (+7–14 d)

- Most tractable position: **1036** (shared card: one proof serves two forcing
  lines; zone 118).
- The 10⁶–10⁸ node-positions/position estimate requires the λ-compression to
  work essentially first-try; the naive layer is 10⁹–10¹⁰× too slow to fall
  back on, so "prover 2–5 d + runs 1–3 d" is risk-priced on unmeasured prover
  quality.
- Honest path if B must continue: Rust/Go λ-prover (3–6 wk eng), then a
  **calibration run at k=6/k=8** to measure the achieved compression factor
  before any depth-16 commitment.
- Revised recommendation: outreach-only (Path A) remains the deterministic
  path; keep this probe's `positions.json`, encodings, and sizing scripts as
  the reusable B artifacts (SCOPE reuse map unchanged).

Scripts: `reconstruct.py`, `size_search.py`, `size_truncations.py`,
`encode_sat.py`, `stored_shape.py`. Stdlib except pysat (task 3).
