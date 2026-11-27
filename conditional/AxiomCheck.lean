-- Independent replay (R2125608282): axiom audit + bare-import dry-run of the completed
-- SnakyConditional target.  Run: lake env lean -DautoImplicit=false AxiomCheck.lean
-- This file imports the solution module and prints axioms with NO `open` — a bare-import
-- audit that proves the entry needs no namespace opens and only the 3 standard axioms.
import Submission.SnakyConditional

#print axioms OAI.SnakyConditional.snaky_winning_strategy_with_legal_states

-- statement-shape pin: the proved theorem really is the corpus challenge statement (the
-- `example` type-checks only if the entry's type is exactly the challenge proposition).
example : ∃ σ : OAI.SnakyConditional.OrdinaryStrategy.Policy OAI.SnakyConditional.Cell,
    (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
    ∀ β : ℕ → OAI.SnakyConditional.Cell,
      OAI.SnakyConditional.OrdinaryStrategy.LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
      OAI.SnakyConditional.HasSnaky
          (OAI.SnakyConditional.OrdinaryStrategy.playState σ 35 β ∅ ∅ 35).1 ∧
      (OAI.SnakyConditional.OrdinaryStrategy.playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
      Disjoint (OAI.SnakyConditional.OrdinaryStrategy.playState σ 35 β ∅ ∅ 35).1
          (OAI.SnakyConditional.OrdinaryStrategy.playState σ 35 β ∅ ∅ 34).2 ∧
      ∀ k, k < 35 →
        Disjoint (OAI.SnakyConditional.OrdinaryStrategy.playState σ 35 β ∅ ∅ k).1
            (OAI.SnakyConditional.OrdinaryStrategy.playState σ 35 β ∅ ∅ k).2 ∧
        (OAI.SnakyConditional.OrdinaryStrategy.playState σ 35 β ∅ ∅ k).2.card = k :=
  OAI.SnakyConditional.snaky_winning_strategy_with_legal_states
