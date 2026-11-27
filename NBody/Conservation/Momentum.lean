module

public import NBody.LocalExistence
public import NBody.Configuration.Masses
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

namespace NBody

noncomputable section

/-- Total linear momentum of a velocity configuration. -/
def totalMomentum {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (v : Config ι d) : EuclideanSpace ℝ (Fin d) :=
  ∑ i, m i • v i

/-- Momentum along a phase curve. -/
def momentumCurve {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (z : ℝ → Phase ι d) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  totalMomentum m (z t).2

theorem hasDerivAt_momentumCurve {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} {G : ℝ} {m : ι → ℝ} {z : ℝ → Phase ι d} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalSolution G m z I) (ht : t ∈ I) :
    HasDerivAt (momentumCurve m z) (∑ i, m i • acceleration G m (z t).1 i) t := by
  unfold momentumCurve totalMomentum
  apply HasDerivAt.fun_sum (u := Finset.univ)
  intro i hi
  exact (solution_body_derivatives hsol ht i).2.const_smul (m i)

theorem hasDerivAt_momentumCurve_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {G : ℝ} {m : ι → ℝ}
    {z : ℝ → Phase ι d} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalSolution G m z I) (ht : t ∈ I) :
    HasDerivAt (momentumCurve m z) 0 t := by
  have h := hasDerivAt_momentumCurve hsol ht
  convert h using 1
  simpa using (weightedAcceleration_sum_eq_zero G m (z t).1).symm

theorem momentumCurve_eq_on_of_isPreconnected {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {G : ℝ} {m : ι → ℝ}
    {z : ℝ → Phase ι d} {I : Set ℝ} {a : ℝ}
    (hsol : ClassicalSolution G m z I) (hconn : IsPreconnected I)
    (ha : a ∈ I) : I.EqOn (momentumCurve m z) (fun _ => momentumCurve m z a) := by
  have hf : DifferentiableOn ℝ (momentumCurve m z) I := by
    intro t ht
    exact (hasDerivAt_momentumCurve_zero hsol ht).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ (fun _ : ℝ => momentumCurve m z a) I := by
    fun_prop
  have hderiv : ∀ t ∈ I,
      fderiv ℝ (momentumCurve m z) t =
        fderiv ℝ (fun _ : ℝ => momentumCurve m z a) t := by
    intro t ht
    rw [(hasDerivAt_momentumCurve_zero hsol ht).hasFDerivAt.fderiv]
    simp
  exact hsol.1.eqOn_of_fderiv_eq hconn hf hg hderiv ha rfl


/-- Mass-weighted position along a phase curve. -/
def weightedPositionCurve {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (z : ℝ → Phase ι d) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  weightedPosition m (z t).1

/-- Center-of-mass trajectory on a phase curve. -/
def centerOfMassCurve {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (z : ℝ → Phase ι d) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  centerOfMass m (z t).1

theorem hasDerivAt_weightedPositionCurve {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {G : ℝ} {m : ι → ℝ}
    {z : ℝ → Phase ι d} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalSolution G m z I) (ht : t ∈ I) :
    HasDerivAt (weightedPositionCurve m z) (momentumCurve m z t) t := by
  unfold weightedPositionCurve weightedPosition momentumCurve totalMomentum
  apply HasDerivAt.fun_sum (u := Finset.univ)
  intro i hi
  exact (solution_body_derivatives hsol ht i).1.const_smul (m i)

theorem hasDerivAt_centerOfMassCurve {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {G : ℝ} {m : ι → ℝ}
    {z : ℝ → Phase ι d} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalSolution G m z I) (ht : t ∈ I)
    :
    HasDerivAt (centerOfMassCurve m z)
      ((totalMass m)⁻¹ • momentumCurve m z t) t := by
  change HasDerivAt
    (fun s => (totalMass m)⁻¹ • weightedPositionCurve m z s)
    ((totalMass m)⁻¹ • momentumCurve m z t) t
  exact (hasDerivAt_weightedPositionCurve hsol ht).const_smul ((totalMass m)⁻¹)
theorem totalMomentum_conserved {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {G : ℝ} {m : ι → ℝ}
    {z : ℝ → Phase ι d} {I : Set ℝ} {a t : ℝ}
    (hsol : ClassicalSolution G m z I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) :
    totalMomentum m (z t).2 = totalMomentum m (z a).2 :=
  momentumCurve_eq_on_of_isPreconnected hsol hconn ha ht

end

end NBody
