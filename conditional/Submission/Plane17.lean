import Submission.Plane
import Submission.Gen17.All
import Submission.Result17

/-!
# G2 instantiation: the 17×17 card table wins on the open plane

The same 1,738-card table (Nándor Sieben's 20-move proof sequence, converted to cards and
kernel-checked as `Snaky.Gen17`) that proves `snaky_wins_17x17_in_20` proves the *plane* win:
the board-fit and counting conjuncts of `rootOK` were the only 17×17-specific hypotheses, and
`Snaky.Plane.planeRootOK_of_rootOK` drops them.
-/
namespace Snaky

/-- **G2 (tree form): the Gen17 card table forces Snaky on the open plane `ℤ × ℤ` within 20
Black (Maker) moves, against any Breaker play.** -/
theorem plane_snaky_wins_in_20 : PlaneWinsIn 20 [] [] :=
  plane_cards_sound_in (CTree.all_get Gen17.tree_ok) (planeRootOK_of_rootOK Gen17.root_ok)
    Gen17.root_height

end Snaky
