import Submission.Plane17
import Submission.SnakyStatement

/-!
# G2 — the plane win in the board's vocabulary (`Policy`, `playState`, `HasSnaky`)

`Snaky.Plane17.plane_snaky_wins_in_20` is a game-tree statement.  This file repackages it in
`OAI.SnakyPrototype.OrdinaryStrategy`'s `playState` form against the challenge `Model`:

* `cardStrategy get` — an explicit **total** policy: play the placed card's prescribed cell when
  some verified card of height ≤ rounds-left is placed with a fresh `p`; otherwise play any
  fresh cell (the "extra stone" of the card proof).  Freshness everywhere:
  `cardStrategy_fresh`.
* `cardStrategy_wins_20` — against every `LegalRepliesBeforeFinal` Breaker sequence, the final
  Maker set contains a Snaky: `HasSnaky (playState … 20).1`.

The invariant is the card induction of `Snaky.Plane`: at round `k` either a snaky is already on
board or a verified card of height `≤ 20 - k` is placed.  The final Breaker reply (`β 19`) is
deliberately unrestricted and never needed: a height-1 verified card is already won after the
move (its pass hint would point at a height-0 card, contradicting `cardOK`'s `1 ≤ h`).

What remains for G3/G4: the `Disjoint`/card-count conjuncts of `Bound` (they follow from this
policy's freshness and Breaker legality by a standard `playState` induction) and the packaging
against the board's byte-identical `Model` (already vendored here as `Snaky.PlaneModel`).
-/
namespace Snaky

open OAI.SnakyPrototype
open OAI.SnakyPrototype.OrdinaryStrategy

/-! ## Fresh cells on the plane, as sets -/

/-- A finite pair of plane stone sets misses a cell. -/
theorem exists_fresh_fin (M B : Finset Cell) : ∃ x : Cell, x ∉ M ∧ x ∉ B := by
  refine Classical.byContradiction (p := ∃ x : Cell, x ∉ M ∧ x ∉ B) fun hno => ?_
  have hall : ∀ j : Nat,
      j < (M.toList ++ B.toList).length + 1 → ((j : Int), 0) ∈ M.toList ++ B.toList := by
    intro j hj
    refine Classical.byContradiction fun hm => hno ⟨(((j : Int), 0) : Cell), ?_, ?_⟩
    · exact fun hb => hm (List.mem_append.2 (Or.inl (Finset.mem_toList.mpr hb)))
    · exact fun hw => hm (List.mem_append.2 (Or.inr (Finset.mem_toList.mpr hw)))
  have h := row_le_length hall
  omega

/-- A canonical fresh plane cell for the position `(M, B)`. -/
noncomputable def freshFin (M B : Finset Cell) : Cell := (exists_fresh_fin M B).choose

theorem freshFin_fresh (M B : Finset Cell) :
    freshFin M B ∉ M ∧ freshFin M B ∉ B := Exists.choose_spec (exists_fresh_fin M B)

/-! ## The board's win predicate, from the card world's `wonPlane` -/

/-- Each orientation of Snaky (as normalized by the card world) is a Model placement: some
`orient r` followed by a translation. -/
private theorem mem_orientations_model (f : List Cell) (hf : f ∈ orientations snaky) :
    ∃ (r : Fin 8) (s : Cell),
      (snaky.all fun p => decide (OAI.SnakyPrototype.orient r p + s ∈ f)) = true := by
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨⟨0, by decide⟩, (0, 0), by decide⟩
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨⟨3, by decide⟩, (1, 0), by decide⟩
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨⟨6, by decide⟩, (4, 1), by decide⟩
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨⟨5, by decide⟩, (0, 4), by decide⟩
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨⟨2, by decide⟩, (0, 1), by decide⟩
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨⟨1, by decide⟩, (0, 0), by decide⟩
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨⟨4, by decide⟩, (4, 0), by decide⟩
  rcases List.mem_singleton.1 hf with rfl
  exact ⟨⟨7, by decide⟩, (1, 4), by decide⟩

/-- `wonPlane` on a set's cells is exactly the board's `HasSnaky` (G1's second half, as far as
G2 needs it). -/
theorem wonPlane_to_hasSnaky {M : Finset Cell} (hw : wonPlane M.toList = true) :
    OAI.SnakyPrototype.HasSnaky M := by
  unfold wonPlane at hw
  simp only [List.any_eq_true, List.all_eq_true, List.contains_iff_mem] at hw
  obtain ⟨f, hf, q0, -, hfin⟩ := hw
  obtain ⟨t, hin⟩ : ∃ t, ∀ u ∈ f, shift t u ∈ M.toList :=
    ⟨(q0.1 - (f.headD (0, 0)).1, q0.2 - (f.headD (0, 0)).2), fun u hu => by
      have := hfin u hu; simpa [shift] using this⟩
  obtain ⟨r, s, hcorr⟩ := mem_orientations_model f hf
  refine ⟨r, t + s, ?_⟩
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
  have hpm : p ∈ snaky := by
    unfold OAI.SnakyPrototype.snaky at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 : OAI.SnakyPrototype.orient r p + s ∈ f :=
    of_decide_eq_true (List.all_eq_true.mp hcorr p hpm)
  have h2 : shift t (OAI.SnakyPrototype.orient r p + s) ∈ M.toList := hin _ h1
  have hEq : shift t (OAI.SnakyPrototype.orient r p + s)
      = OAI.SnakyPrototype.orient r p + (t + s) := by
    apply Prod.ext
    · simp only [shift, Prod.fst_add]; omega
    · simp only [shift, Prod.snd_add]; omega
  rw [← hpx, ← Finset.mem_toList]
  show OAI.SnakyPrototype.orient r p + (t + s) ∈ M.toList
  rw [← hEq]
  exact h2

/-- `HasSnaky` is monotone. -/
theorem hasSnaky_mono {M M' : Finset Cell} (h : OAI.SnakyPrototype.HasSnaky M) (hs : M ⊆ M') :
    OAI.SnakyPrototype.HasSnaky M' := by
  obtain ⟨r, t, hsub⟩ := h
  exact ⟨r, t, fun x hx => hs (hsub hx)⟩

theorem planeRootOK_exists {get : Nat → Option Card} {i : Nat} {g : Xf}
    (hroot : planeRootOK get i g = true) :
    ∃ c, get i = some c ∧ c.A = [] ∧ g.isOrient = true := by
  unfold planeRootOK at hroot
  split at hroot
  · rename_i c hc
    have h' : (c.A.isEmpty && g.isOrient) = true := hroot
    rw [Bool.and_eq_true] at h'
    exact ⟨c, hc, List.isEmpty_iff.1 h'.1, h'.2⟩
  · simp at hroot

/-! ## The card strategy -/

/-- A verified card of height ≤ `r`, placed (in the plane invariant of `Snaky.Plane`) at the
position `(M, B)` under symmetry `xf`. -/
structure CardWitness (get : Nat → Option Card) (r : ℕ) (M B : Finset Cell) : Type where
  card : Card
  xf : Xf
  hj : ∃ j, get j = some card
  hok : cardOK get card = true
  hh : card.h ≤ r
  hio : xf.isOrient = true
  hpl : PlanePlaced card xf M.toList B.toList

/-- Some placed card's prescribed cell is still free. -/
def FreshWitness (get : Nat → Option Card) (r : ℕ) (M B : Finset Cell) : Prop :=
  ∃ w : CardWitness get r M B, w.xf.app w.card.p ∉ M

open Classical in
/-- The card strategy: play the picked card's prescribed cell when some placed verified card has
a free prescription; otherwise play any fresh cell (an extra stone never hurts).  Total, and
fresh at every call by `cardStrategy_fresh`. -/
noncomputable def cardStrategy (get : Nat → Option Card) : Policy Cell := fun r M B =>
  if h : FreshWitness get r M B then h.choose.xf.app h.choose.card.p else freshFin M B

theorem cardStrategy_fresh (get : Nat → Option Card) (r : ℕ) (M B : Finset Cell) :
    cardStrategy get r M B ∉ M ∧ cardStrategy get r M B ∉ B := by
  unfold cardStrategy
  split
  · rename_i h
    refine ⟨Exists.choose_spec h, ?_⟩
    have hpS : h.choose.card.p ∈ h.choose.card.S := by
      have hok' : cardOK get h.choose.card = true := h.choose.hok
      unfold cardOK at hok'
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok'
      exact hok'.1.2
    have hb := h.choose.hpl.2 h.choose.card.p hpS
    rw [Finset.mem_toList] at hb
    exact hb
  · exact freshFin_fresh M B

/-- After Black's move `m`, the moved card's stones sit inside `insert m M`.  For the picked
witness the prescribed cell *is* the move; for any other witness the prescribed cell was already
Black's (that is exactly what ¬`FreshWitness` says). -/
private theorem stones_of_strategy (get : Nat → Option Card) (r : ℕ) (M B : Finset Cell)
    (w : CardWitness get r M B) (hfw : ¬ FreshWitness get r M B) :
    ∀ q ∈ w.card.p :: w.card.A, w.xf.app q ∈ insert (cardStrategy get r M B) M := by
  unfold cardStrategy
  rw [dif_neg hfw]
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hqA
  · exact Finset.mem_insert_of_mem
      (Classical.byContradiction fun hmem => hfw ⟨w, hmem⟩)
  · exact Finset.mem_insert_of_mem (Finset.mem_toList.mp (w.hpl.1 q hqA))

private theorem stones_of_picked (get : Nat → Option Card) (r : ℕ) (M B : Finset Cell)
    (wp : CardWitness get r M B) :
    ∀ q ∈ wp.card.p :: wp.card.A, wp.xf.app q ∈ insert (wp.xf.app wp.card.p) M := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hqA
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_toList.mp (wp.hpl.1 q hqA))

/-! ## One round of the strategy -/

/-- A valid hint placed on `w`'s card yields the next card witness, one round and one height
lower, at the position after Black's move `m` and White's reply `w'`.  (Type-valued: the next
card and symmetry are chosen classically from the hint's verified existence.) -/
private noncomputable def hint_step (get : Nat → Option Card)
    (hall : ∀ j c, get j = some c → cardOK get c = true)
    (r : ℕ) (M B : Finset Cell) (w : CardWitness get r M B) (hr : 1 ≤ r)
    (m : Cell) (hstones : ∀ q ∈ w.card.p :: w.card.A, w.xf.app q ∈ insert m M)
    (w' : Cell) (hw' : w' ∉ insert m M)
    (hn : Hint) (Rg : Pt → Bool)
    (hRg : ∀ s, Rg s = true → s ∈ w.card.S ∧ w.xf.app s ≠ w')
    (hhint : hintOK get w.card.h (w.card.p :: w.card.A) Rg hn = true) :
    CardWitness get (r - 1) (insert m M) (insert w' B) := by
  have hspec : ∃ p : Card × Xf, get hn.1 = some p.1 ∧ p.1.h < w.card.h ∧ p.2.isOrient = true ∧
      (∀ a ∈ p.1.A, p.2.app a ∈ (insert m M).toList) ∧
      (∀ s ∈ p.1.S, p.2.app s ∉ (insert w' B).toList) := by
    obtain ⟨c', hj', hlt', hor, hA', hS'⟩ := hintOK_spec hhint
    refine ⟨(c', w.xf.comp hn.2), hj', hlt', ?_, ?_, ?_⟩
    · exact Xf.isOrient_comp w.hio hor
    · intro a ha
      show (w.xf.comp hn.2).app a ∈ (insert m M).toList
      rw [Xf.app_comp]
      exact Finset.mem_toList.mpr (hstones _ (hA' a ha))
    · intro s hs
      have happ : ((c', w.xf.comp hn.2) : Card × Xf).2.app s = (w.xf.comp hn.2).app s := rfl
      rw [happ, Xf.app_comp, Finset.mem_toList, Finset.mem_insert, not_or]
      obtain ⟨hsS, hne⟩ := hRg _ (hS' s hs)
      exact ⟨hne, fun hmem => w.hpl.2 _ hsS (Finset.mem_toList.mpr hmem)⟩
  refine ⟨(Classical.choose hspec).1, (Classical.choose hspec).2,
    ⟨hn.1, (Classical.choose_spec hspec).1⟩,
    hall _ _ (Classical.choose_spec hspec).1, ?_, (Classical.choose_spec hspec).2.2.1,
    ⟨(Classical.choose_spec hspec).2.2.2.1, (Classical.choose_spec hspec).2.2.2.2⟩⟩
  have hhh := (Classical.choose_spec hspec).2.1
  have hle := w.hh
  omega

/-- One round: Black plays `cardStrategy … (M, B)`; if White's reply `w'` is legal (not in
Black's new stones), then either a snaky is already on board or the card invariant survives one
round and one height lower. -/
theorem witness_step (get : Nat → Option Card)
    (hall : ∀ j c, get j = some c → cardOK get c = true)
    (r : ℕ) (M B : Finset Cell) (hwit : CardWitness get r M B) (hr : 1 ≤ r)
    (m : Cell) (hm : cardStrategy get r M B = m)
    (w' : Cell) (hw' : w' ∉ insert m M) :
    OAI.SnakyPrototype.HasSnaky (insert m M) ∨
      ∃ w₂ : CardWitness get (r - 1) (insert m M) (insert w' B), True := by
  have hok := hwit.hok
  unfold cardOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem] at hok
  obtain ⟨⟨h1, hpS⟩, hrest⟩ := hok
  have step : ∀ (w : CardWitness get r M B)
      (hstones : ∀ q ∈ w.card.p :: w.card.A, w.xf.app q ∈ insert m M),
      ∀ (hn : Hint) (Rg : Pt → Bool),
        (∀ s, Rg s = true → s ∈ w.card.S ∧ w.xf.app s ≠ w') →
        hintOK get w.card.h (w.card.p :: w.card.A) Rg hn = true →
        CardWitness get (r - 1) (insert m M) (insert w' B) :=
    fun w hstones hn Rg => hint_step get hall r M B w hr m hstones w' hw' hn Rg
  -- whose card do we follow: the picked one (if the first branch fired) else `hwit`
  by_cases hf : FreshWitness get r M B
  · -- fresh pick: follow the picked card, whose prescribed cell *is* the move
    unfold cardStrategy at hm
    rw [dif_pos hf] at hm
    have hstones := stones_of_picked get r M B hf.choose
    rw [hm] at hstones
    have hokw : cardOK get hf.choose.card = true := hf.choose.hok
    unfold cardOK at hokw
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem]
      at hokw
    obtain ⟨⟨-, hpSw⟩, hrestw⟩ := hokw
    rcases hrestw with hwon | ⟨hpass, hreps⟩
    · exact Or.inl (wonPlane_to_hasSnaky (wonPlane_congr hwon hf.choose.hio
        (fun q hq => Finset.mem_toList.mpr (hstones q hq))))
    · by_cases hex : ∃ w0 ∈ hf.choose.card.S, hf.choose.xf.app w0 = w'
      · obtain ⟨w0, hw0S, rfl⟩ := hex
        have hw0 : w0 ∉ hf.choose.card.p :: hf.choose.card.A :=
          fun hmem => hw' (hstones w0 hmem)
        have hrr := List.all_eq_true.1 hreps w0 hw0S
        have hw0' : (hf.choose.card.p :: hf.choose.card.A).contains w0 = false := by
          simpa [List.contains_iff_mem] using hw0
        unfold replyOK at hrr
        rw [hw0', Bool.false_or] at hrr
        split at hrr
        · rename_i hn _
          refine Or.inr ⟨step hf.choose hstones hn _ (fun s hs => ?_) hrr, True.intro⟩
          simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at hs
          refine ⟨hs.1, fun e => hs.2 (Xf.app_inj hf.choose.hio e)⟩
        · simp at hrr
      · unfold passOK at hpass
        split at hpass
        · rename_i hn _
          refine Or.inr ⟨step hf.choose hstones hn _ (fun s hs => ?_) hpass, True.intro⟩
          rw [List.contains_iff_mem] at hs
          exact ⟨hs, fun e => hex ⟨s, hs, e⟩⟩
        · simp at hpass
  · -- the extra-stone branch: `hwit`'s prescribed cell was already Black's
    have hstones := stones_of_strategy get r M B hwit hf
    rw [hm] at hstones
    rcases hrest with hwon | ⟨hpass, hreps⟩
    · exact Or.inl (wonPlane_to_hasSnaky (wonPlane_congr hwon hwit.hio
        (fun q hq => Finset.mem_toList.mpr (hstones q hq))))
    · by_cases hex : ∃ w0 ∈ hwit.card.S, hwit.xf.app w0 = w'
      · obtain ⟨w0, hw0S, rfl⟩ := hex
        have hw0 : w0 ∉ hwit.card.p :: hwit.card.A := fun hmem => hw' (hstones w0 hmem)
        have hrr := List.all_eq_true.1 hreps w0 hw0S
        have hw0' : (hwit.card.p :: hwit.card.A).contains w0 = false := by
          simpa [List.contains_iff_mem] using hw0
        unfold replyOK at hrr
        rw [hw0', Bool.false_or] at hrr
        split at hrr
        · rename_i hn _
          refine Or.inr ⟨step hwit hstones hn _ (fun s hs => ?_) hrr, True.intro⟩
          simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at hs
          refine ⟨hs.1, fun e => hs.2 (Xf.app_inj hwit.hio e)⟩
        · simp at hrr
      · unfold passOK at hpass
        split at hpass
        · rename_i hn _
          refine Or.inr ⟨step hwit hstones hn _ (fun s hs => ?_) hpass, True.intro⟩
          rw [List.contains_iff_mem] at hs
          exact ⟨hs, fun e => hex ⟨s, hs, e⟩⟩
        · simp at hpass

/-- The last Maker claim (round budget 1): a verified card of height ≤ 1 is already won after
the move — its pass hint would point at a height-0 card, contradicting `cardOK`'s `1 ≤ h`.  No
Breaker legality is used, matching the unrestricted final reply. -/
theorem witness_step_final (get : Nat → Option Card)
    (hall : ∀ j c, get j = some c → cardOK get c = true)
    (M B : Finset Cell) (hwit : CardWitness get 1 M B) :
    OAI.SnakyPrototype.HasSnaky (insert (cardStrategy get 1 M B) M) := by
  unfold cardStrategy
  split
  · -- fresh pick: the followed card is the picked one, whose prescribed cell *is* the move
    rename_i h
    have hstones := stones_of_picked get 1 M B h.choose
    have hok := h.choose.hok
    unfold cardOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem]
      at hok
    obtain ⟨⟨-, -⟩, hrest⟩ := hok
    rcases hrest with hwon | ⟨hpass, hreps⟩
    · exact wonPlane_to_hasSnaky (wonPlane_congr hwon h.choose.hio
        (fun q hq => Finset.mem_toList.mpr (hstones q hq)))
    · -- any hint points at a height-0 card, which cannot pass `cardOK`
      exfalso
      unfold passOK at hpass
      split at hpass
      · rename_i hn _
        obtain ⟨c', hj', hlt', -, -, -⟩ := hintOK_spec hpass
        have hok' : cardOK get c' = true := hall _ _ hj'
        have h1' : 1 ≤ c'.h := by
          unfold cardOK at hok'
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem] at hok'
          exact hok'.1.1
        have hlt := hlt'
        have hhh := h.choose.hh
        omega
      · simp at hpass
  · -- extra stone: `hwit`'s prescribed cell was already Black's
    rename_i h
    have hstones : ∀ q ∈ hwit.card.p :: hwit.card.A, hwit.xf.app q ∈ insert (freshFin M B) M := by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hqA
      · exact Finset.mem_insert_of_mem
          (Classical.byContradiction fun hmem => h ⟨hwit, hmem⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_toList.mp (hwit.hpl.1 q hqA))
    have hok := hwit.hok
    unfold cardOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem]
      at hok
    obtain ⟨⟨-, -⟩, hrest⟩ := hok
    rcases hrest with hwon | ⟨hpass, hreps⟩
    · exact wonPlane_to_hasSnaky (wonPlane_congr hwon hwit.hio
        (fun q hq => Finset.mem_toList.mpr (hstones q hq)))
    · exfalso
      unfold passOK at hpass
      split at hpass
      · rename_i hn _
        obtain ⟨c', hj', hlt', -, -, -⟩ := hintOK_spec hpass
        have hok' : cardOK get c' = true := hall _ _ hj'
        have h1' : 1 ≤ c'.h := by
          unfold cardOK at hok'
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem] at hok'
          exact hok'.1.1
        have hlt := hlt'
        have hhh := hwit.hh
        omega
      · simp at hpass

/-! ## The 20-round theorem -/

/-- **G2 (playState form): following the card strategy, every legal plane Breaker sequence
loses within 20 Maker claims** — at Maker's 20th claim the set contains a Snaky in the board's
exact sense. -/
theorem cardStrategy_wins_20 (get : Nat → Option Card)
    (hall : ∀ j c, get j = some c → cardOK get c = true)
    (i : Nat) (g₀ : Xf) (hroot : planeRootOK get i g₀ = true)
    (hk : (get i).all (fun c => decide (c.h ≤ 20)) = true)
    (β : ℕ → Cell) (hlegal : LegalRepliesBeforeFinal (cardStrategy get) 20 β ∅ ∅) :
    OAI.SnakyPrototype.HasSnaky (playState (cardStrategy get) 20 β ∅ ∅ 20).1 := by
  obtain ⟨c₀, hc₀, hA₀, hio₀⟩ := planeRootOK_exists hroot
  have hk₀ : c₀.h ≤ 20 := by
    rw [hc₀] at hk
    simpa only [Option.all_some, decide_eq_true_eq] using hk
  have hleg := hlegal
  simp only [LegalRepliesBeforeFinal, makerAt] at hleg
  have key : ∀ k, k ≤ 20 →
      OAI.SnakyPrototype.HasSnaky (playState (cardStrategy get) 20 β ∅ ∅ k).1 ∨
        ∃ w : CardWitness get (20 - k)
            (playState (cardStrategy get) 20 β ∅ ∅ k).1
            (playState (cardStrategy get) 20 β ∅ ∅ k).2, True := by
    intro k
    induction k with
    | zero =>
      intro _
      refine Or.inr ⟨⟨c₀, g₀, ⟨i, hc₀⟩, hall _ _ hc₀, hk₀, hio₀, ?_⟩, True.intro⟩
      constructor
      · intro a ha
        rw [hA₀] at ha
        nomatch ha
      · intro s _ hs
        simp only [playState, Finset.toList_empty] at hs
        nomatch hs
    | succ k ih =>
      intro hk20
      have hble : k < 20 := Nat.lt_of_succ_le hk20
      rcases ih (Nat.le_of_succ_le hk20) with hwin | ⟨w, -⟩
      · left
        simp only [playState]
        refine hasSnaky_mono hwin ?_
        intro x hx
        exact Finset.mem_insert_of_mem hx
      · by_cases hlast : k = 19
        · left
          subst hlast
          simp only [playState]
          exact witness_step_final get hall
            (playState (cardStrategy get) 20 β ∅ ∅ 19).1
            (playState (cardStrategy get) 20 β ∅ ∅ 19).2 w
        · have hlt : k + 1 < 20 := by omega
          obtain ⟨h1, -⟩ := hleg k hlt
          rcases witness_step get hall (20 - k)
              (playState (cardStrategy get) 20 β ∅ ∅ k).1
              (playState (cardStrategy get) 20 β ∅ ∅ k).2 w (by omega)
              (cardStrategy get (20 - k) (playState (cardStrategy get) 20 β ∅ ∅ k).1
                (playState (cardStrategy get) 20 β ∅ ∅ k).2) rfl (β k) h1
            with hwin | hex
          · left
            simp only [playState]
            exact hwin
          · right
            obtain ⟨w₂, -⟩ := hex
            exact ⟨w₂, True.intro⟩
  have hkey := key 20 (Nat.le_refl 20)
  refine Or.elim hkey (fun hwin => hwin) (fun hex => ?_)
  exfalso
  obtain ⟨w, _⟩ := hex
  have h1 : 1 ≤ w.card.h := by
    have hok := w.hok
    unfold cardOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      List.contains_iff_mem] at hok
    exact hok.1.1
  have hhh := w.hh
  omega

/-! ## The G2 deliverable in the board's exact shape -/

/-- **G2**: a total, fresh policy on the plane following the verified Gen17 card table wins
within 20 Maker claims against every legal Breaker sequence.  The freshness conjunct is the
first half of `Bound 20`'s policy obligation; the `Disjoint`/card-count conjuncts remain for
G3/G4. -/
theorem snaky_plane_bound_win :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 20 β ∅ ∅ →
        OAI.SnakyPrototype.HasSnaky (playState σ 20 β ∅ ∅ 20).1 :=
  ⟨cardStrategy Gen17.getK, fun r M B => cardStrategy_fresh Gen17.getK r M B, fun β hβ =>
    cardStrategy_wins_20 Gen17.getK (CTree.all_get Gen17.tree_ok) 1737 ⟨1, 0, 0, 1, 0, 0⟩
      (planeRootOK_of_rootOK Gen17.root_ok) Gen17.root_height β hβ⟩

end Snaky
