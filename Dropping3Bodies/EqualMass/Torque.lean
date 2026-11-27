module

public import Dropping3Bodies.EqualMass.GapIdentity
public import Mathlib.Tactic

@[expose] public section

/-!
Positive algebraic factorization used in the equal-mass pair-torque equation.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Positive coefficient in the inverse-cube side-difference factorization. -/
def inverseCubeGapFactor (x y : ℝ) : ℝ :=
  (x ^ 2 + x * y + y ^ 2) / ((x + y) * x ^ 3 * y ^ 3)

/-- D3B-S03; PAPER-20261029 `eq:factor`; exact factorization for positive sides. -/
theorem inverse_cube_gap_factorization {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ (-3 : ℤ) - y ^ (-3 : ℤ) =
      -inverseCubeGapFactor x y * (x ^ 2 - y ^ 2) := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  rw [zpow_neg, zpow_neg]
  unfold inverseCubeGapFactor
  field_simp [hxy, hx0, hy0]
  ring

/-- The coefficient is strictly positive for positive side lengths. -/
theorem inverseCubeGapFactor_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < inverseCubeGapFactor x y := by
  unfold inverseCubeGapFactor
  positivity

/-- On the isosceles boundary the factor has its continuous diagonal value. -/
theorem inverseCubeGapFactor_diag {x : ℝ} (hx : 0 < x) :
    inverseCubeGapFactor x x = 3 / (2 * x ^ 5) := by
  unfold inverseCubeGapFactor
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp [hx0]
  ring



end

end DroppingThreeBodies
