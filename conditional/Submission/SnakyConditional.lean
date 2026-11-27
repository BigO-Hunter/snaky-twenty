import Mathlib
import Submission.Padding

namespace OAI.SnakyConditional

abbrev Cell := ℤ × ℤ
def snaky : Finset Cell := {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}
def orient (r : Fin 8) (p : Cell) : Cell :=
  match r.val with
  | 0 => (p.1, p.2)
  | 1 => (p.2, p.1)
  | 2 => (p.1, -p.2)
  | 3 => (-p.2, p.1)
  | 4 => (-p.1, p.2)
  | 5 => (p.2, -p.1)
  | 6 => (-p.1, -p.2)
  | _ => (-p.2, -p.1)
def placement (r : Fin 8) (t p : Cell) : Cell := orient r p + t
def HasSnaky (M : Finset Cell) : Prop :=
  ∃ (r : Fin 8) (t : Cell), snaky.image (placement r t) ⊆ M

namespace OrdinaryStrategy

variable {α : Type*} [DecidableEq α]

abbrev Policy (α : Type*) := ℕ → Finset α → Finset α → α
def playState (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) :
    ℕ → Finset α × Finset α
  | 0 => (M₀, B₀)
  | k + 1 =>
      let state := playState σ N β M₀ B₀ k
      (insert (σ (N - k) state.1 state.2) state.1, insert (β k) state.2)
def makerAt (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) (k : ℕ) : α :=
  let state := playState σ N β M₀ B₀ k
  σ (N - k) state.1 state.2
def LegalRepliesBeforeFinal (σ : Policy α) (N : ℕ) (β : ℕ → α)
    (M₀ B₀ : Finset α) : Prop :=
  ∀ k, k + 1 < N →
    β k ∉ insert (makerAt σ N β M₀ B₀ k) (playState σ N β M₀ B₀ k).1 ∧
    β k ∉ (playState σ N β M₀ B₀ k).2
end OrdinaryStrategy

open OrdinaryStrategy

/- BRIDGE (R2125608282): the corpus defs above are letter-for-letter identical to the
   vendored `OAI.SnakyPrototype` defs that the verified Bound-20 proof tree
   (`Submission/`, from darkhipo/snaky-twenty) is stated against — only the namespace
   differs.  These lemmas transport that tree's `BigOSpeedrun.Snaky.Bound 35` result into
   this namespace.  They are NOT part of the byte-exact challenge statement. -/

theorem playState_eq :
    ∀ (σ : Policy Cell) (N : ℕ) (β : ℕ → Cell) (M₀ B₀ : Finset Cell) (k : ℕ),
      OAI.SnakyPrototype.OrdinaryStrategy.playState σ N β M₀ B₀ k
        = playState σ N β M₀ B₀ k := by
  intro σ N β M₀ B₀ k
  induction k with
  | zero => rfl
  | succ k ih => simp only [OAI.SnakyPrototype.OrdinaryStrategy.playState, playState, ih]

theorem makerAt_eq :
    ∀ (σ : Policy Cell) (N : ℕ) (β : ℕ → Cell) (M₀ B₀ : Finset Cell) (k : ℕ),
      OAI.SnakyPrototype.OrdinaryStrategy.makerAt σ N β M₀ B₀ k
        = makerAt σ N β M₀ B₀ k := by
  intro σ N β M₀ B₀ k
  simp only [OAI.SnakyPrototype.OrdinaryStrategy.makerAt, makerAt, playState_eq]

theorem legal_eq :
    ∀ (σ : Policy Cell) (N : ℕ) (β : ℕ → Cell) (M₀ B₀ : Finset Cell),
      OAI.SnakyPrototype.OrdinaryStrategy.LegalRepliesBeforeFinal σ N β M₀ B₀
        ↔ LegalRepliesBeforeFinal σ N β M₀ B₀ := by
  intro σ N β M₀ B₀
  simp only [OAI.SnakyPrototype.OrdinaryStrategy.LegalRepliesBeforeFinal,
    LegalRepliesBeforeFinal, makerAt_eq, playState_eq]

theorem hasSnaky_eq (M : Finset Cell) :
    OAI.SnakyPrototype.HasSnaky M ↔ HasSnaky M := Iff.rfl

theorem snaky_winning_strategy_with_legal_states :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (playState σ 35 β ∅ ∅ 35).1 ∧
        (playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
        Disjoint (playState σ 35 β ∅ ∅ 35).1 (playState σ 35 β ∅ ∅ 34).2 ∧
        ∀ k, k < 35 →
          Disjoint (playState σ 35 β ∅ ∅ k).1 (playState σ 35 β ∅ ∅ k).2 ∧
          (playState σ 35 β ∅ ∅ k).2.card = k := by
  -- reuse the verified Bound-20 win, padded to horizon 35 (Snaky.race_bound_35)
  obtain ⟨σ, hfresh, hwin⟩ := Snaky.race_bound_35
  refine ⟨σ, hfresh, ?_⟩
  intro β hleg
  have hlegP : OAI.SnakyPrototype.OrdinaryStrategy.LegalRepliesBeforeFinal σ 35 β ∅ ∅ :=
    (legal_eq σ 35 β ∅ ∅).mpr hleg
  have hP := hwin β hlegP
  obtain ⟨hS, hC, hD, hK⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [playState_eq] at hS
    exact (hasSnaky_eq _).mp hS
  · simp only [playState_eq] at hC
    exact hC
  · simp only [playState_eq] at hD
    exact hD
  · intro k hk
    have h := hK k hk
    simp only [playState_eq] at h
    exact h

end OAI.SnakyConditional
