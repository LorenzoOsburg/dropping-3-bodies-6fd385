module

public import NBody.Configuration.Masses

@[expose] public section

namespace NBody

noncomputable section

/-- Singular homothetic collision exponent for a degree `-α` attractive
potential: radius scales like `|t-T|^p`. -/
def homotheticCollisionExponent (α : ℝ) : ℝ := 2 / (α + 2)

/-- The model kinetic/potential action density has singular exponent
`2α/(α+2)`. -/
def homotheticActionSingularityExponent (α : ℝ) : ℝ :=
  2 * α / (α + 2)

/-- For `0 < α < 2`, the model action singularity is a locally integrable
power (`exponent < 1`). This is the scalar integrability threshold; no claim
about arbitrary generalized trajectories is made here. -/
theorem homotheticActionSingularityExponent_lt_one
    {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    homotheticActionSingularityExponent α < 1 := by
  unfold homotheticActionSingularityExponent
  have hden : 0 < α + 2 := by linarith
  rw [div_lt_one hden]
  linarith

theorem homotheticActionSingularityExponent_nonneg
    {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ homotheticActionSingularityExponent α := by
  unfold homotheticActionSingularityExponent
  apply div_nonneg
  · positivity
  · linarith

end

end NBody
