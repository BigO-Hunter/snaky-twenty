import Submission.SnakyStatement
import Submission.PlaneBound

/-!
# Submission root — the challenge target

The verifier checks exactly this theorem (maintainer spec, issue #106).  `Race.bound` is
proved from `Snaky.race_bound_20`; the statement `BigOSpeedrun.Snaky.Bound` is vendored in
`Submission/SnakyStatement.lean` — on filing day that file is replaced byte-for-byte by the
maintainer's posted statement file and this tree is re-verified green.
-/

/-- The challenge target: Maker forces a Snaky within 20 own claims against every legal
Breaker sequence, with exact card counts and disjointness. -/
theorem Race.bound : BigOSpeedrun.Snaky.Bound 20 := Snaky.race_bound_20
