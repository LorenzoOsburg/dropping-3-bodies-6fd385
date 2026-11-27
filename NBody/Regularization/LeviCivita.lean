module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace NBody

noncomputable section

/-- Levi-Civita position projection `x = z²` for the planar two-body problem. -/
def leviCivitaPosition (z : ℂ) : ℂ := z ^ 2

/-- Cotangent lift of the planar squaring map, `P = 2 conjugate(z) p`. -/
def leviCivitaMomentum (z p : ℂ) : ℂ := 2 * star z * p

/-- The regularized Kepler energy at physical energy `h`, multiplied by
`|z|²`. This polynomial extends across `z = 0`.

Reference convention: [MoeckelMontgomeryAuthor2012, §6, pp. 31–32]. -/
def leviCivitaRegularizedEnergy (μ k h : ℝ) (z P : ℂ) : ℝ :=
  ‖P‖ ^ 2 / (8 * μ) - k - h * ‖z‖ ^ 2

/-- A point on the regularized Kepler energy level above collision has nonzero
lifted momentum. Thus the lifted vector field does not stop at the collision
point on the zero-regularized-energy surface. -/
theorem leviCivita_collision_momentum_ne_zero
    {μ k h : ℝ} {z P : ℂ} (hk : 0 < k)
    (hz : z = 0) (hK : leviCivitaRegularizedEnergy μ k h z P = 0) : P ≠ 0 := by
  intro hP
  subst P
  simp [leviCivitaRegularizedEnergy, hz] at hK
  have : 0 < k := hk
  linarith

end

end NBody
