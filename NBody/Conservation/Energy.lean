module

public import NBody.Configuration.Masses
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

namespace NBody

noncomputable section

/-- Kinetic energy along a velocity curve. -/
def kineticEnergyCurve {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (v : ℝ → Config ι d) (t : ℝ) : ℝ :=
  kineticEnergy m (v t)

/-- Derivative of kinetic energy for a differentiable finite velocity family.
The unsimplified factor 2 records the direct norm-square chain rule. -/
theorem hasDerivAt_kineticEnergyCurve {ι : Type*} [Fintype ι]
    {d : ℕ} (m : ι → ℝ) {v : ℝ → Config ι d} {a : Config ι d} {t : ℝ}
    (hv : HasDerivAt v a t) :
    HasDerivAt (kineticEnergyCurve m v)
      ((1 / 2 : ℝ) * ∑ i, m i *
        (2 * inner ℝ (v t i) (a i))) t := by
  unfold kineticEnergyCurve kineticEnergy
  refine HasDerivAt.const_mul (1 / 2 : ℝ) ?_
  apply HasDerivAt.fun_sum (u := Finset.univ)
  intro i hi
  have hvi := (hasDerivAt_pi.1 hv) i
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    HasDerivAt.const_mul (m i) hvi.norm_sq

end

end NBody
