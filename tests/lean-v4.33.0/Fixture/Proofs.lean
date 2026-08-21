import Fixture.Basic

/-!
Theorems whose proofs reach further than their statements do — the difference
between the dependency graph's answer and the review document's — plus one
unfinished proof, so taint has something to propagate from.
-/

namespace Fixture

/-- Reached from `sum_le`'s proof only: its statement never names this. -/
theorem sum_comm (p : Point) : p.sum = p.y + p.x := Nat.add_comm p.x p.y

/-- Statement names `Point.sum`; the proof additionally pulls in `sum_comm`. -/
theorem sum_le (p : Point) : p.x ≤ p.sum := by
  rw [sum_comm]
  exact Nat.le_add_left p.x p.y

/-- Deliberately unfinished: this decl, and everything downstream of it, must
come back tainted. -/
theorem sum_pos (p : Point) (h : 0 < p.x) : 0 < p.sum := by
  sorry

/-- Downstream of a `sorry`, so tainted without carrying one itself. -/
theorem double_sum_pos (p : Point) (h : 0 < p.x) : 0 < (double p).sum :=
  sum_pos (double p) (by rw [double_x]; omega)

end Fixture
