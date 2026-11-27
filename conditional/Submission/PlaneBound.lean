import Submission.SnakyStatement
import Submission.PlanePolicy

/-!
# G3/G4 — the full `Bound 20` in the board's exact shape

G2 (`Snaky.PlanePolicy`) supplies the policy half: `cardStrategy Gen17.getK` is total and
fresh everywhere, and wins at claim 20 against every legal Breaker sequence.  This file adds
the `playState` bookkeeping conjuncts of `Bound` — card counts and disjointness — which are
pure bookkeeping: Maker's freshness makes his pile grow by exactly one stone per round, and
Breaker legality (`LegalRepliesBeforeFinal`) does the same for hers while keeping the two
piles disjoint.  Instantiate with `σ = cardStrategy Gen17.getK`:

* `race_bound_20 : BigOSpeedrun.Snaky.Bound 20` — the challenge target.
-/
namespace Snaky

open OAI.SnakyPrototype
open OAI.SnakyPrototype.OrdinaryStrategy

/-! ## One round of `playState`, zeta-expanded -/

/-- Maker's stones after round `k + 1`. -/
theorem playState_succ_fst {σ : Policy Cell} {N : ℕ} {β : ℕ → Cell} {M₀ B₀ : Finset Cell}
    (k : ℕ) :
    (playState σ N β M₀ B₀ (k + 1)).1 =
      insert (σ (N - k) (playState σ N β M₀ B₀ k).1 (playState σ N β M₀ B₀ k).2)
        (playState σ N β M₀ B₀ k).1 := rfl

/-- Breaker's stones after round `k + 1`. -/
theorem playState_succ_snd {σ : Policy Cell} {N : ℕ} {β : ℕ → Cell} {M₀ B₀ : Finset Cell}
    (k : ℕ) :
    (playState σ N β M₀ B₀ (k + 1)).2 = insert (β k) (playState σ N β M₀ B₀ k).2 := rfl

/-! ## Card counts -/

/-- Maker's pile grows by exactly one stone per round: σ never re-plays into `M`. -/
theorem playState_fst_card {σ : Policy Cell}
    (hσ : ∀ (r : ℕ) (M B : Finset Cell), σ r M B ∉ M)
    (N : ℕ) (β : ℕ → Cell) (M₀ B₀ : Finset Cell) :
    ∀ k : ℕ, (playState σ N β M₀ B₀ k).1.card = M₀.card + k := by
  intro k
  induction k with
  | zero => simp [playState]
  | succ k ih =>
      rw [playState_succ_fst, Finset.card_insert_of_notMem (hσ (N - k) _ _), ih]
      omega

/-- Breaker's pile grows by exactly one stone per round while `k + 1 < N` (her reply at the
last round is unrestricted and never counted). -/
theorem playState_snd_card {σ : Policy Cell} {N : ℕ} {β : ℕ → Cell} {M₀ B₀ : Finset Cell}
    (hleg : ∀ k : ℕ, k + 1 < N → β k ∉ (playState σ N β M₀ B₀ k).2) :
    ∀ k : ℕ, k < N → (playState σ N β M₀ B₀ k).2.card = B₀.card + k := by
  intro k
  induction k with
  | zero => intro _; simp [playState]
  | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      rw [playState_succ_snd, Finset.card_insert_of_notMem (hleg k hk), ih hk']
      omega

/-! ## Disjointness -/

/-- While Breaker replies legally, the two piles stay disjoint. -/
theorem playState_disjoint {σ : Policy Cell}
    (hσ : ∀ (r : ℕ) (M B : Finset Cell), σ r M B ∉ B)
    (N : ℕ) (β : ℕ → Cell) (M₀ B₀ : Finset Cell) (h₀ : Disjoint M₀ B₀)
    (hleg : ∀ k : ℕ, k + 1 < N →
      β k ∉ insert (σ (N - k) (playState σ N β M₀ B₀ k).1 (playState σ N β M₀ B₀ k).2)
        (playState σ N β M₀ B₀ k).1 ∧
      β k ∉ (playState σ N β M₀ B₀ k).2) :
    ∀ k : ℕ, k < N → Disjoint (playState σ N β M₀ B₀ k).1 (playState σ N β M₀ B₀ k).2 := by
  intro k
  induction k with
  | zero => intro _; exact h₀
  | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      obtain ⟨hleg1, hleg2⟩ := hleg k hk
      rw [playState_succ_fst, playState_succ_snd, Finset.disjoint_insert_left]
      refine ⟨?_, ?_⟩
      · -- σ's move is not Breaker's reply nor on Breaker's pile
        intro hmem
        rcases Finset.mem_insert.1 hmem with heq | hmemB
        · rw [heq] at hleg1
          exact hleg1 (Finset.mem_insert_self _ _)
        · exact hσ (N - k) _ _ hmemB
      · -- Breaker's reply is not on Maker's pile (nor on Maker's old pile, by IH)
        rw [Finset.disjoint_insert_right]
        exact ⟨fun h => hleg1 (Finset.mem_insert_of_mem h), ih hk'⟩

/-- The winning claim is disjoint from Breaker's penultimate pile: σ's last move is fresh for
Breaker (no legality needed), and the penultimate position was already disjoint. -/
theorem playState_disjoint_final {σ : Policy Cell}
    (hσ : ∀ (r : ℕ) (M B : Finset Cell), σ r M B ∉ B)
    (N : ℕ) (β : ℕ → Cell) (M₀ B₀ : Finset Cell) (hN : 0 < N)
    (hd : ∀ j : ℕ, j < N →
      Disjoint (playState σ N β M₀ B₀ j).1 (playState σ N β M₀ B₀ j).2) :
    Disjoint (playState σ N β M₀ B₀ N).1 (playState σ N β M₀ B₀ (N - 1)).2 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [playState_succ_fst, Finset.disjoint_insert_left]
  exact ⟨hσ _ _ _, hd m (by omega)⟩

/-! ## The challenge target -/

/-- **G3**: the full `Bound 20` of the board's `Statement.lean`, with
σ = `cardStrategy Gen17.getK` (G2's total, fresh, winning policy) and the
`Disjoint`/card-count conjuncts discharged by `playState` bookkeeping from σ's freshness
and Breaker legality. -/
theorem race_bound_20 : BigOSpeedrun.Snaky.Bound 20 := by
  refine ⟨cardStrategy Gen17.getK, fun r M B => cardStrategy_fresh Gen17.getK r M B,
    fun β hleg => ?_⟩
  have hσ := cardStrategy_fresh Gen17.getK
  have hleg2 := hleg
  simp only [LegalRepliesBeforeFinal, makerAt] at hleg2
  refine ⟨cardStrategy_wins_20 Gen17.getK (CTree.all_get Gen17.tree_ok) 1737 ⟨1, 0, 0, 1, 0, 0⟩
      (planeRootOK_of_rootOK Gen17.root_ok) Gen17.root_height β hleg, ?_, ?_,
    fun k hk => ⟨?_, ?_⟩⟩
  · -- Maker's 20th pile has exactly 20 stones
    rw [playState_fst_card (fun r M B => (hσ r M B).1) 20 β ∅ ∅ 20, Finset.card_empty]
  · -- the winning pile is disjoint from Breaker's pile after claim 19
    exact playState_disjoint_final (fun r M B => (hσ r M B).2) 20 β ∅ ∅ (by omega)
      (fun j hj => playState_disjoint (fun r M B => (hσ r M B).2) 20 β ∅ ∅
        (Finset.disjoint_empty_left ∅) hleg2 j hj)
  · -- every intermediate position is disjoint
    exact playState_disjoint (fun r M B => (hσ r M B).2) 20 β ∅ ∅
      (Finset.disjoint_empty_left ∅) hleg2 k hk
  · -- Breaker's k-th pile has exactly k stones
    rw [playState_snd_card (fun j hj => (hleg2 j hj).2) k hk, Finset.card_empty]
    exact Nat.zero_add k

end Snaky
