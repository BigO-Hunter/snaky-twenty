import Submission.PlaneBound

/-!
# Padding: extend the verified Bound-20 win to horizon 35 (R2125608282)

The corpus target `SnakyConditional` is `BigOSpeedrun.Snaky.Bound 35` — the *weakest*
horizon of the statement we already won at Bound 20 (issue #114, `Snaky.race_bound_20`,
verified).  `HasSnaky` is monotone in the Maker pile, so a win that secures a Snaky by
Maker claim 20 still wins at horizon 35: the extra 15 claims are padding.

The only real content is the **r-genericity** bridge.  The winning policy
`Snaky.snaky_plane_bound_win` (σ₂₀ = `cardStrategy Gen17.getK`) is proved at horizon 20,
where the card-witness height ticks down in lockstep with the remaining-move counter
`20 - k`.  Replayed *verbatim* at horizon 35 the policy would be handed the larger counter
`35 - k` and the card countdown would desynchronise.  So the horizon-35 policy is the
**padded** σ₂₀: on the first 20 Maker claims it shifts the counter down by 15 (`σ₂₀ (r-15)`)
so the proven game is replayed move-for-move, and on the remaining 15 claims it plays a
fresh cell (an extra stone never hurts).

This file proves `Snaky.race_bound_35 : BigOSpeedrun.Snaky.Bound 35`.  The bookkeeping
conjuncts (card counts, disjointness) are the generic-in-N lemmas of `Submission.PlaneBound`;
only `HasSnaky` needs the win plus monotonicity.  The transport into the byte-exact corpus
namespace `OAI.SnakyConditional` happens in `Submission.SnakyConditional`.
-/

namespace Snaky

open OAI.SnakyPrototype
open OAI.SnakyPrototype.OrdinaryStrategy

/-- Pad a policy to horizon 35: replay the shortened 20-game on the first 20 Maker claims
(shifting the remaining-move counter down by 15 so the 20-horizon policy is called exactly
as in the proven game), then fill the remaining 15 claims with fresh cells. -/
noncomputable def pad (σ : Policy Cell) : Policy Cell :=
  fun r M B => if 15 < r then σ (r - 15) M B else freshFin M B

/-- The padded policy stays fresh.  On the replayed prefix it defers to `σ` (fresh by
hypothesis); on the filler tail it plays `freshFin` (fresh by `freshFin_fresh`). -/
theorem pad_fresh {σ : Policy Cell} (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) :
    ∀ r M B, pad σ r M B ∉ M ∧ pad σ r M B ∉ B := by
  intro r M B
  show (if 15 < r then σ (r - 15) M B else freshFin M B) ∉ M ∧
    (if 15 < r then σ (r - 15) M B else freshFin M B) ∉ B
  by_cases hs : 15 < r
  · rw [if_pos hs]
    exact hσ (r - 15) M B
  · rw [if_neg hs]
    exact freshFin_fresh M B

/-- Maker's pile only grows with the round index. -/
theorem playState_mono_fst_le (σ : Policy Cell) (N : ℕ) (β : ℕ → Cell) :
    ∀ {k k'}, k ≤ k' → (playState σ N β ∅ ∅ k).1 ⊆ (playState σ N β ∅ ∅ k').1 := by
  intro k k' h
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (Finset.subset_insert _ _)

/-- **r-genericity (prefix replay).**  On the first 20 Maker claims the padded policy `pad σ`
at horizon 35 reproduces `σ` at horizon 20 move-for-move: it hands `σ` the shifted counter
`35 - k - 15 = 20 - k`.  The two `playState` traces agree for every `k ≤ 20`. -/
theorem playState_pad_prefix (σ : Policy Cell) (β : ℕ → Cell) :
    ∀ k ≤ 20, playState (pad σ) 35 β ∅ ∅ k = playState σ 20 β ∅ ∅ k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < 20 := Nat.lt_of_succ_le hk
    have hag : playState (pad σ) 35 β ∅ ∅ k = playState σ 20 β ∅ ∅ k := ih (Nat.le_of_succ_le hk)
    have hlt : 15 < 35 - k := by omega
    have hshift : (35 - k) - 15 = 20 - k := by omega
    have hmove : pad σ (35 - k) (playState σ 20 β ∅ ∅ k).1 (playState σ 20 β ∅ ∅ k).2
        = σ (20 - k) (playState σ 20 β ∅ ∅ k).1 (playState σ 20 β ∅ ∅ k).2 := by
      show (if 15 < 35 - k then σ ((35 - k) - 15) _ _ else freshFin _ _) = _
      rw [if_pos hlt, hshift]
    simp only [playState]
    rw [hag, hmove]

/-- **makerAt agreement on the prefix.**  For `k < 20` the padded policy's `makerAt` at
horizon 35 equals `σ`'s `makerAt` at horizon 20. -/
theorem makerAt_pad_prefix (σ : Policy Cell) (β : ℕ → Cell) :
    ∀ k < 20, makerAt (pad σ) 35 β ∅ ∅ k = makerAt σ 20 β ∅ ∅ k := by
  intro k hk
  have hstate : playState (pad σ) 35 β ∅ ∅ k = playState σ 20 β ∅ ∅ k :=
    playState_pad_prefix σ β k (by omega)
  have hlt : 15 < 35 - k := by omega
  have hshift : (35 - k) - 15 = 20 - k := by omega
  show pad σ (35 - k) (playState (pad σ) 35 β ∅ ∅ k).1 (playState (pad σ) 35 β ∅ ∅ k).2
    = σ (20 - k) (playState σ 20 β ∅ ∅ k).1 (playState σ 20 β ∅ ∅ k).2
  rw [hstate]
  show (if 15 < 35 - k then σ ((35 - k) - 15) _ _ else freshFin _ _) = _
  rw [if_pos hlt, hshift]

/-- **Legality lifts across the prefix.**  A Breaker sequence legal against the padded policy
at horizon 35 is legal against `σ` at horizon 20 (the prefix traces and `makerAt` agree). -/
theorem legal_pad_prefix {σ : Policy Cell} (β : ℕ → Cell) :
    LegalRepliesBeforeFinal (pad σ) 35 β ∅ ∅ → LegalRepliesBeforeFinal σ 20 β ∅ ∅ := by
  intro hleg k hk
  have hk35 : k + 1 < 35 := by omega
  have h := hleg k hk35
  rw [← playState_pad_prefix σ β k (by omega), ← makerAt_pad_prefix σ β k (by omega)]
  exact h

/-- **The `HasSnaky` win survives padding to horizon 35.**  From a fresh policy that forces
a Snaky by claim 20 against every legal Breaker sequence, the padded policy forces a Snaky by
claim 35: the first 20 claims replay the winning game (prefix agreement), the last 15 only
grow the Maker pile, and `HasSnaky` is monotone. -/
theorem pad_wins_35 {σ : Policy Cell}
    (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (hwins : ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 20 β ∅ ∅ →
      HasSnaky (playState σ 20 β ∅ ∅ 20).1) :
    ∀ β : ℕ → Cell, LegalRepliesBeforeFinal (pad σ) 35 β ∅ ∅ →
      HasSnaky (playState (pad σ) 35 β ∅ ∅ 35).1 := by
  intro β hleg
  have hsnaky20 : HasSnaky (playState (pad σ) 35 β ∅ ∅ 20).1 := by
    rw [playState_pad_prefix σ β 20 (Nat.le_refl 20)]
    exact hwins β (legal_pad_prefix β hleg)
  have hsub : (playState (pad σ) 35 β ∅ ∅ 20).1 ⊆ (playState (pad σ) 35 β ∅ ∅ 35).1 :=
    playState_mono_fst_le (pad σ) 35 β (by omega : (20:ℕ) ≤ 35)
  exact hasSnaky_mono hsnaky20 hsub

/-- **G-35: the full `BigOSpeedrun.Snaky.Bound 35`.**  σ = the 15-padded `cardStrategy
Gen17.getK` from the verified Bound-20 win.  Freshness is `pad_fresh`; the winning conjunct
is `pad_wins_35`; the card/disjointness conjuncts are the generic-in-N bookkeeping of
`Submission.PlaneBound` applied at `N = 35`. -/
theorem race_bound_35 : BigOSpeedrun.Snaky.Bound 35 := by
  obtain ⟨σ₂₀, hσ₂₀, hwin₂₀⟩ := Snaky.snaky_plane_bound_win
  refine ⟨pad σ₂₀, pad_fresh hσ₂₀, ?_⟩
  intro β hleg
  have hσf : ∀ r M B, pad σ₂₀ r M B ∉ M ∧ pad σ₂₀ r M B ∉ B := pad_fresh hσ₂₀
  have hleg' := hleg
  simp only [LegalRepliesBeforeFinal, makerAt] at hleg'
  refine ⟨pad_wins_35 hσ₂₀ hwin₂₀ β hleg, ?_, ?_, fun k hk => ⟨?_, ?_⟩⟩
  · -- Maker's 35th pile has exactly 35 stones
    rw [playState_fst_card (fun r M B => (hσf r M B).1) 35 β ∅ ∅ 35, Finset.card_empty]
  · -- the winning pile is disjoint from Breaker's pile after claim 34
    exact playState_disjoint_final (fun r M B => (hσf r M B).2) 35 β ∅ ∅ (by omega)
      (fun j hj => playState_disjoint (fun r M B => (hσf r M B).2) 35 β ∅ ∅
        (Finset.disjoint_empty_left ∅) hleg' j hj)
  · -- every intermediate position is disjoint
    exact playState_disjoint (fun r M B => (hσf r M B).2) 35 β ∅ ∅
      (Finset.disjoint_empty_left ∅) hleg' k hk
  · -- Breaker's k-th pile has exactly k stones
    rw [playState_snd_card (fun j hj => (hleg' j hj).2) k hk, Finset.card_empty]
    exact Nat.zero_add k

end Snaky
