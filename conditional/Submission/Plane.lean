import Submission.CardsSound

/-!
# G2 — plane-lift of the card-soundness induction

`Snaky.CardsSound` re-derives Nándor Sieben's card tree into a win on a finite `R × C` board.
Every finite ingredient exists only to (a) guarantee a free cell (the `2 * h ≤ R * C` counting
bound) and (b) convert `wonPlane` into indexed `placements`.  On the plane `ℤ × ℤ` both are free:
a fresh cell always exists (`exists_plane_free`), and `wonPlane` *is* the win predicate.

So the whole induction lifts by deleting bookkeeping:

* `wonPlane_congr` — plane lift of `won_image`: a board symmetry maps a won shape onto a won
  shape (same `decide`-checked `orient_image` fact, restated because the original is private).
* `PlanePlaced c g B W` — `g(A) ⊆ B`, `g(S) ∩ W = ∅`; no board, no counting bound.
* `PlaneWinsIn` / `PlaneLosesIn` — the bounded game tree of `Snaky.Bounded`, with plane cells
  `Pt` instead of indices `Nat` and `wonPlane B = true` as the won case.
* `plane_sound_aux` — `CardsSound.sound_aux` with `idx`/`onBoard`/`idx_lt`/`idx_inj`/
  `won_image`/`mem_placements` dropped; the "White outside `S` → pass hint" branch is unchanged
  and already covers replies arbitrarily far away.
* `planeRootOK` — `rootOK` minus the board-fit and `2 * h ≤ R * C` conjuncts.

The card *data* is untouched: any `get` with `cardOK`-verified cards (e.g. the Gen17 table)
gives a plane win within the root height.  `Snaky.Plane17` instantiates this with the
1,738-card table; `Snaky.PlanePolicy` rephrases the result against the board's
`OAI.SnakyPrototype` vocabulary (`HasSnaky`, `playState`).
-/
namespace Snaky

/-! ## Plane free cells -/

theorem row_le_length {L : List Pt} :
    ∀ {n : Nat}, (∀ j : Nat, j < n → ((j : Int), 0) ∈ L) → n ≤ L.length
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    have hn : (((n : Nat) : Int), 0) ∈ L := h n (Nat.lt_succ_self n)
    have hrest := row_le_length (L := L.erase (((n : Nat) : Int), 0)) (n := n) (fun j hj => by
      have hne : (((j : Int), 0) : Pt) ≠ (((n : Int), 0) : Pt) := by
        intro he
        simp only [Prod.mk.injEq] at he
        exact Nat.ne_of_lt hj (Int.natCast_inj.mp he.1)
      exact List.mem_erase_of_ne hne |>.2 (h j (Nat.lt_succ_of_lt hj)))
    rw [List.length_erase_of_mem hn] at hrest
    have : 0 < L.length := List.length_pos_of_mem hn
    omega

/-- The plane always has a free cell: a finite pair of stone lists misses some cell. -/
theorem exists_plane_free (B W : List Pt) : ∃ x : Pt, x ∉ B ∧ x ∉ W := by
  refine Classical.byContradiction (p := ∃ x : Pt, ¬x ∈ B ∧ ¬x ∈ W) fun hno => ?_
  have hall : ∀ j : Nat, j < (B ++ W).length + 1 → ((j : Int), 0) ∈ B ++ W := by
    intro j hj
    refine Classical.byContradiction fun hm => hno ⟨(((j : Int), 0) : Pt), ?_, ?_⟩
    · exact fun hb => hm (List.mem_append.2 (Or.inl hb))
    · exact fun hw => hm (List.mem_append.2 (Or.inr hw))
  have h := row_le_length hall
  omega

/-! ## Symmetry invariance of the plane win -/

/-- Same fact as `CardsSound`'s private `orient_image` (restated: the original is private). -/
private theorem orient_image_plane : ∀ m ∈ orients, ∀ f ∈ orientations snaky,
    ∃ f' ∈ orientations snaky,
      f.map (mApp m) = f'.map (shift ((mApp m (f.headD (0, 0))).1 - (f'.headD (0, 0)).1,
        (mApp m (f.headD (0, 0))).2 - (f'.headD (0, 0)).2)) := by
  decide

private theorem orientations_ne (f : List Pt) (hf : f ∈ orientations snaky) : f ≠ [] := by
  have hall : (orientations snaky).all (fun g => decide (g ≠ [])) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hall f hf)

private theorem headD_mem {d : Pt} {l : List Pt} (h : l ≠ []) : l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self

/-- An orientation of Snaky translated onto `L` makes `wonPlane L` true (unpacks `wonPlane`'s
anchored form). -/
theorem wonPlane_of_orient_shift {L f : List Pt} (hf : f ∈ orientations snaky) {t : Pt}
    (hsub : ∀ u ∈ f, shift t u ∈ L) : wonPlane L = true := by
  have hne : f ≠ [] := orientations_ne f hf
  have hhd : f.headD (0, 0) ∈ f := headD_mem hne
  unfold wonPlane
  rw [List.any_eq_true]
  refine ⟨f, hf, ?_⟩
  rw [List.any_eq_true]
  refine ⟨shift t (f.headD (0, 0)), hsub _ hhd, ?_⟩
  simp only
  rw [List.all_eq_true]
  intro u hu
  have huL := hsub u hu
  simp only [List.contains_iff_mem] at huL ⊢
  simp only [shift] at huL ⊢
  have hEq : (u.1 + ((f.headD (0, 0)).1 + t.1 - (f.headD (0, 0)).1),
      u.2 + ((f.headD (0, 0)).2 + t.2 - (f.headD (0, 0)).2)) = (u.1 + t.1, u.2 + t.2) := by
    rw [Prod.mk.injEq]
    constructor <;> omega
  rw [hEq]
  exact huL

/-- Plane lift of `won_image`: pushing a won shape through a board symmetry keeps it won.
This replaces the finite proof's detour through `placements`/`idx`. -/
theorem wonPlane_congr {L L' : List Pt} (hw : wonPlane L = true) {g : Xf}
    (hg : g.isOrient = true) (hon : ∀ q ∈ L, g.app q ∈ L') : wonPlane L' = true := by
  unfold wonPlane at hw
  simp only [List.any_eq_true, List.all_eq_true, List.contains_iff_mem] at hw
  obtain ⟨f, hf, q0, -, hfin⟩ := hw
  obtain ⟨t, hin⟩ : ∃ t, ∀ u ∈ f, shift t u ∈ L :=
    ⟨(q0.1 - (f.headD (0, 0)).1, q0.2 - (f.headD (0, 0)).2), fun u hu => by
      have := hfin u hu; simpa [shift] using this⟩
  rw [Xf.isOrient_iff] at hg
  obtain ⟨f', hf', himg⟩ := orient_image_plane _ hg f hf
  generalize hc : ((mApp (g.a, g.b, g.c, g.d) (f.headD (0, 0))).1 - (f'.headD (0, 0)).1,
      (mApp (g.a, g.b, g.c, g.d) (f.headD (0, 0))).2 - (f'.headD (0, 0)).2) = c at himg
  have hlist : f.map (fun u => g.app (shift t u)) =
      f'.map (shift (shift (g.dx, g.dy) (shift (mApp (g.a, g.b, g.c, g.d) t) c))) := by
    have hfun : (fun u => g.app (shift t u)) =
        (shift (g.dx, g.dy) ∘ shift (mApp (g.a, g.b, g.c, g.d) t)) ∘ mApp (g.a, g.b, g.c, g.d) := by
      funext u; simp [Xf.app_eq, mApp_shift]
    rw [hfun, ← List.map_map, himg, List.map_map]
    congr 1; funext v; simp [shift_shift]
  refine wonPlane_of_orient_shift
    (t := shift (g.dx, g.dy) (shift (mApp (g.a, g.b, g.c, g.d) t) c)) hf' ?_
  intro u hu
  have hmem : shift (shift (g.dx, g.dy) (shift (mApp (g.a, g.b, g.c, g.d) t) c)) u ∈
      f.map (fun u => g.app (shift t u)) := by
    rw [hlist]; exact List.mem_map_of_mem hu
  obtain ⟨u0, hu0, he⟩ := List.mem_map.1 hmem
  rw [← he]
  exact hon _ (hin u0 hu0)

/-! ## The plane game tree -/

mutual
/-- `PlaneWinsIn n B W`: Black to move at the plane position `(B, W)`, forcing a `wonPlane`
shape within `n` of her own moves.  The plane analogue of `BlackWinsIn`. -/
inductive PlaneWinsIn : Nat → List Pt → List Pt → Prop
  | move (n : Nat) (B W : List Pt) (b : Pt) (hB : b ∉ B) (hW : b ∉ W)
      (h : PlaneLosesIn n (b :: B) W) : PlaneWinsIn (n + 1) B W

/-- `PlaneLosesIn n B W`: Black has just moved; she already owns a `wonPlane` shape, or a free
cell exists and every White reply loses within `n` more Black moves.  No board-size guard is
needed: `hfree` is witnessed on the plane by `exists_plane_free`. -/
inductive PlaneLosesIn : Nat → List Pt → List Pt → Prop
  | won (n : Nat) (B W : List Pt) (hw : wonPlane B = true) : PlaneLosesIn n B W
  | reply (n : Nat) (B W : List Pt) (hfree : ∃ w, w ∉ B ∧ w ∉ W)
      (h : ∀ w, w ∉ B → w ∉ W → PlaneWinsIn n B (w :: W)) : PlaneLosesIn n B W
end

/-- Plane placement invariant for card `c` under `g`: `g(A)` inside Black's stones, `g(S)`
missing from White's.  `CardsSound.Placed` minus `onBoard` and the counting bound. -/
def PlanePlaced (c : Card) (g : Xf) (B W : List Pt) : Prop :=
  (∀ a ∈ c.A, g.app a ∈ B) ∧ (∀ s ∈ c.S, g.app s ∉ W)

/-! ## The induction -/

/-- **Plane soundness of the card checker, with the move bound**: the plane lift of
`CardsSound.sound_aux`.  Card data, hints and the reply/pass case analysis are unchanged; only
index bookkeeping is gone. -/
theorem plane_sound_aux {get : Nat → Option Card}
    (hall : ∀ j c, get j = some c → cardOK get c = true) :
    ∀ (n : Nat) (c : Card), (∃ j : Nat, get j = some c) → c.h ≤ n → ∀ g : Xf,
      g.isOrient = true → ∀ B W : List Pt, PlanePlaced c g B W → PlaneWinsIn n B W := by
  intro n
  induction n with
  | zero =>
    intro c ⟨j, hj⟩ hch
    have hok := hall _ _ hj
    unfold cardOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  | succ n ih =>
    intro c ⟨j, hj⟩ hch g hg B W ⟨hAinv, hSinv⟩
    have hok := hall _ _ hj
    unfold cardOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem]
      at hok
    obtain ⟨⟨h1, hpS⟩, hrest⟩ := hok
    have hpW : g.app c.p ∉ W := hSinv c.p hpS
    -- Black's move: `g(p)` if free, else any free cell (the extra stone never hurts)
    obtain ⟨b, hbB, hbW, hcov⟩ : ∃ b : Pt, b ∉ B ∧ b ∉ W ∧ g.app c.p ∈ b :: B := by
      by_cases hpB : g.app c.p ∈ B
      · obtain ⟨x, hxB, hxW⟩ := exists_plane_free B W
        exact ⟨x, hxB, hxW, List.mem_cons_of_mem _ hpB⟩
      · exact ⟨_, hpB, hpW, List.mem_cons_self⟩
    apply PlaneWinsIn.move n B W b hbB hbW
    have hBl : ∀ q ∈ c.p :: c.A, g.app q ∈ b :: B := by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hqA
      · exact hcov
      · exact List.mem_cons_of_mem _ (hAinv q hqA)
    rcases hrest with hwon | ⟨hpass, hreps⟩
    · -- the win case: push the card's won shape through the symmetry `g`
      exact PlaneLosesIn.won n (b :: B) W (wonPlane_congr hwon hg fun q hq => hBl q hq)
    · apply PlaneLosesIn.reply
      · exact exists_plane_free (b :: B) W
      intro w hwB hwW
      -- one White move answered by hint `hn` with region test `Rg`
      have step : ∀ (hn : Hint) (Rg : Pt → Bool),
          (∀ s, Rg s = true → s ∈ c.S ∧ g.app s ≠ w) →
          hintOK get c.h (c.p :: c.A) Rg hn = true →
          PlaneWinsIn n (b :: B) (w :: W) := by
        intro hn Rg hRg hhint
        obtain ⟨c', hj', hlt', hor, hA', hS'⟩ := hintOK_spec hhint
        refine ih c' ⟨_, hj'⟩ (by omega) (g.comp hn.2) (Xf.isOrient_comp hg hor) _ _
          ⟨?_, ?_⟩
        · intro a ha
          rw [Xf.app_comp]
          exact hBl _ (hA' a ha)
        · intro s hs
          rw [Xf.app_comp, List.mem_cons, not_or]
          obtain ⟨hsS, hne⟩ := hRg _ (hS' s hs)
          exact ⟨hne, hSinv _ hsS⟩
      by_cases hex : ∃ w0 ∈ c.S, g.app w0 = w
      · -- White replied inside `g(S)`: the reply table answers
        obtain ⟨w0, hw0S, rfl⟩ := hex
        have hw0 : w0 ∉ c.p :: c.A := fun hm => hwB (hBl w0 hm)
        have hr := List.all_eq_true.1 hreps w0 hw0S
        have hw0' : (c.p :: c.A).contains w0 = false := by
          simpa [List.contains_iff_mem] using hw0
        unfold replyOK at hr
        rw [hw0', Bool.false_or] at hr
        split at hr
        · rename_i hn _
          refine step hn _ (fun s hs => ?_) hr
          simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at hs
          refine ⟨hs.1, fun e => hs.2 (Xf.app_inj hg e)⟩
        · simp at hr
      · -- White passed (outside `g(S)`): the pass hint answers — any distance, no board
        unfold passOK at hpass
        split at hpass
        · rename_i hn _
          refine step hn _ (fun s hs => ?_) hpass
          rw [List.contains_iff_mem] at hs
          exact ⟨hs, fun e => hex ⟨s, hs, e⟩⟩
        · simp at hpass

/-! ## The plane root -/

/-- Plane analogue of `rootOK`: the root card has `A = []` and `g` is a symmetry.  The board-fit
and `2 * h ≤ R * C` conjuncts are exactly what the plane does not need. -/
def planeRootOK (get : Nat → Option Card) (i : Nat) (g : Xf) : Bool :=
  match get i with
  | some c => c.A.isEmpty && g.isOrient
  | none => false

/-- A finite-board root is a plane root. -/
theorem planeRootOK_of_rootOK {get : Nat → Option Card} {R C i : Nat} {g : Xf}
    (h : rootOK get R C i g = true) : planeRootOK get i g = true := by
  unfold rootOK at h
  unfold planeRootOK
  revert h
  generalize hj : get i = o
  cases o with
  | none => intro h; exact Bool.noConfusion h
  | some c =>
    intro h
    have h' : ((c.A.isEmpty && g.isOrient &&
        c.S.all fun s => decide (onBoard R C (g.app s))) && decide (2 * c.h ≤ R * C)) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
    show (c.A.isEmpty && g.isOrient) = true
    rw [Bool.and_eq_true]
    exact ⟨h'.1.1.1, h'.1.1.2⟩

/-- **Plane soundness of the card checker, with the move bound**: the plane lift of
`CardsSound.cards_sound_in`. -/
theorem plane_cards_sound_in {get : Nat → Option Card} {i k : Nat} {g : Xf}
    (hall : ∀ j c, get j = some c → cardOK get c = true)
    (hroot : planeRootOK get i g = true)
    (hk : (get i).all (fun c => decide (c.h ≤ k)) = true) :
    PlaneWinsIn k [] [] := by
  unfold planeRootOK at hroot
  revert hroot hk
  generalize hj : get i = o
  cases o with
  | none => intro hroot _; exact Bool.noConfusion hroot
  | some c =>
    intro hroot hk
    have hroot' : (c.A.isEmpty && g.isOrient) = true := hroot
    simp only [Bool.and_eq_true] at hroot'
    obtain ⟨hA, hg⟩ := hroot'
    have hk' : decide (c.h ≤ k) = true := hk
    have hAvac : ∀ a ∈ c.A, g.app a ∈ ([] : List Pt) := by
      rw [List.isEmpty_iff.1 hA]
      intro a ha
      nomatch ha
    exact plane_sound_aux hall k c ⟨i, hj⟩ (decide_eq_true_eq.mp hk') g hg [] []
      ⟨hAvac, fun s _ hs => List.not_mem_nil hs⟩

end Snaky
