module

public import Dropping3Bodies.Dynamics.Newton
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Dropping3Bodies.EqualMass.FrameCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

namespace DroppingThreeBodies

/-- Derivatives of each body's position and velocity extracted from the packed
    first-order phase-space equation. -/
theorem classicalNewton_body_vector_derivatives
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (fun τ => (z τ).1 i) ((z t).2 i) t ∧
      HasDerivAt (fun τ => (z τ).2 i) (unitAcceleration (z t).1 i) t := by
  have hphase := (hsol.2 t ht).2
  have hpos : HasDerivAt (fun τ => (z τ).1)
      ((unitNewtonField (z t)).1) t := by
    simpa [unitNewtonField] using hphase.hasFDerivAt.fst.hasDerivAt
  have hvel : HasDerivAt (fun τ => (z τ).2)
      ((unitNewtonField (z t)).2) t := by
    simpa [unitNewtonField] using hphase.hasFDerivAt.snd.hasDerivAt
  constructor
  · have h := (hasDerivAt_pi.1 hpos) i
    simpa [unitNewtonField] using h
  · have h := (hasDerivAt_pi.1 hvel) i
    simpa [unitNewtonField] using h

/-- Coordinate derivatives needed by the scalar curve calculus, obtained by
    applying continuous coordinate projections to the body vector derivatives. -/
theorem classicalNewton_body_coordinate_derivatives
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasCoordDerivAt (fun τ => (z τ).1 i) ((z t).2 i) t ∧
      HasCoordDerivAt (fun τ => (z τ).2 i) (unitAcceleration (z t).1 i) t := by
  obtain ⟨hq, hv⟩ := classicalNewton_body_vector_derivatives i hsol ht
  constructor
  · intro k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply hq
  · intro k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply hv

/-- Along a classical Newton solution, the squared-side rate is
    interval-integrable on every compact interval contained in its domain. -/
theorem classicalNewton_sideSqRate_intervalIntegrable
    {z : ℝ → Phase} {I : Set ℝ} {a b : ℝ}
    (hsol : ClassicalNewtonSolution z I)
    (hsegment : Set.uIcc a b ⊆ I) (i : Fin 3) :
    IntervalIntegrable
      (fun τ => 2 * dot2 (sideVector (z τ).1 i) (sideVector (z τ).2 i))
      MeasureTheory.volume a b := by
  have hzcont : ContinuousOn z (Set.uIcc a b) := by
    intro τ hτ
    exact ((hsol.2 τ (hsegment hτ)).2).continuousAt.continuousWithinAt
  exact intervalIntegrable_sideSqRate_of_continuousOn i hzcont.fst hzcont.snd

/-- The integrated squared-side rate equals the endpoint change along any
    classical Newton solution on an interval contained in its domain. -/
theorem classicalNewton_sideSq_integral_eq_sub
    {z : ℝ → Phase} {I : Set ℝ} {a b : ℝ}
    (hsol : ClassicalNewtonSolution z I)
    (hsegment : Set.uIcc a b ⊆ I) (i : Fin 3) :
    ∫ τ in a..b,
      2 * dot2 (sideVector (z τ).1 i) (sideVector (z τ).2 i) =
      sideSq (z b).1 i - sideSq (z a).1 i := by
  have hderiv : ∀ τ ∈ Set.uIcc a b,
      HasBodyCoordDerivAt (fun j t => (z t).1 j)
        (fun j => (z τ).2 j) τ := by
    intro τ hτ j k
    exact (classicalNewton_body_coordinate_derivatives j hsol
      (hsegment hτ)).1 k
  have hint := classicalNewton_sideSqRate_intervalIntegrable hsol hsegment i
  exact intervalIntegral_sideSqRate_eq_sub i hderiv hint
end DroppingThreeBodies
