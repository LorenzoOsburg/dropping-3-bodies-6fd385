module

public import Dropping3Bodies.Dynamics.ConservationAlgebra
public import Dropping3Bodies.Dynamics.SolutionDerivatives
public import Dropping3Bodies.EqualMass.FrameCalculus
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

set_option maxHeartbeats 500000

/-!
Differential identities for total momentum and angular momentum along body curves.
-/

open scoped Topology

namespace DroppingThreeBodies

noncomputable section

/-- Total angular momentum along body position and velocity curves. -/
def angularMomentumCurve (q v : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  totalAngularMomentum (fun i => q i t) (fun i => v i t)

/-- Restrict bodywise coordinate differentiability to one body's planar curve. -/
def bodyCoordDerivAt (q : Fin 3 → ℝ → Point) (v : Fin 3 → Point)
    (i : Fin 3) (t : ℝ) : Prop :=
  HasCoordDerivAt (fun τ => q i τ) (v i) t

theorem bodyCoordDerivAt_of_all {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point}
    {t : ℝ} (h : HasBodyCoordDerivAt q v t) (i : Fin 3) :
    bodyCoordDerivAt q v i t := by
  intro k
  exact h i k

/-- Product-rule derivative of total angular momentum on a general curve. -/
theorem hasDerivAt_angularMomentumCurve
    {q v : Fin 3 → ℝ → Point} {dq dv : Fin 3 → Point} {t : ℝ}
    (hq : HasBodyCoordDerivAt q dq t) (hv : HasBodyCoordDerivAt v dv t) :
    HasDerivAt (angularMomentumCurve q v)
      (∑ i : Fin 3, frameAreaRate (q i t) (v i t) (dq i) (dv i)) t := by
  have h0 : HasDerivAt (frameAreaCurve (fun τ => q 0 τ) (fun τ => v 0 τ))
      (frameAreaRate (q 0 t) (v 0 t) (dq 0) (dv 0)) t := by
    exact hasDerivAt_frameAreaCurve
      (bodyCoordDerivAt_of_all hq 0) (bodyCoordDerivAt_of_all hv 0)
  have h1 : HasDerivAt (frameAreaCurve (fun τ => q 1 τ) (fun τ => v 1 τ))
      (frameAreaRate (q 1 t) (v 1 t) (dq 1) (dv 1)) t := by
    exact hasDerivAt_frameAreaCurve
      (bodyCoordDerivAt_of_all hq 1) (bodyCoordDerivAt_of_all hv 1)
  have h2 : HasDerivAt (frameAreaCurve (fun τ => q 2 τ) (fun τ => v 2 τ))
      (frameAreaRate (q 2 t) (v 2 t) (dq 2) (dv 2)) t := by
    exact hasDerivAt_frameAreaCurve
      (bodyCoordDerivAt_of_all hq 2) (bodyCoordDerivAt_of_all hv 2)
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : angularMomentumCurve q v =ᶠ[𝓝 t]
      (frameAreaCurve (fun τ => q 0 τ) (fun τ => v 0 τ) +
        (frameAreaCurve (fun τ => q 1 τ) (fun τ => v 1 τ) +
          frameAreaCurve (fun τ => q 2 τ) (fun τ => v 2 τ))) := by
    filter_upwards [] with τ
    simp [angularMomentumCurve, totalAngularMomentum, frameAreaCurve,
      Fin.sum_univ_succ]
  simpa [Fin.sum_univ_succ] using hs.congr_of_eventuallyEq hfun

/-- On a Newton trajectory whose position derivative is velocity, the
    angular-momentum derivative is the instantaneous total force torque. -/
theorem hasDerivAt_angularMomentumCurve_newton
    {q v : Fin 3 → ℝ → Point} {t : ℝ}
    (hq : HasBodyCoordDerivAt q (fun i => v i t) t)
    (hv : HasBodyCoordDerivAt v (fun i => unitAcceleration (fun j => q j t) i) t) :
    HasDerivAt (angularMomentumCurve q v)
      (unitTotalTorque (fun i => q i t)) t := by
  have h := hasDerivAt_angularMomentumCurve hq hv
  have hval : (∑ i : Fin 3,
      frameAreaRate (q i t) (v i t) (v i t)
        (unitAcceleration (fun j => q j t) i)) =
      unitTotalTorque (fun i => q i t) := by
    simp [frameAreaRate, unitTotalTorque, cross_self]
  exact h.congr_deriv hval

/-- Newton's pair forces imply a zero angular-momentum derivative at every
    classical instant. Interval constancy is a separate calculus step. -/
theorem hasDerivAt_angularMomentumCurve_newton_zero
    {q v : Fin 3 → ℝ → Point} {t : ℝ}
    (hq : HasBodyCoordDerivAt q (fun i => v i t) t)
    (hv : HasBodyCoordDerivAt v (fun i => unitAcceleration (fun j => q j t) i) t) :
    HasDerivAt (angularMomentumCurve q v) 0 t := by
  have h := hasDerivAt_angularMomentumCurve_newton hq hv
  rw [unitTotalTorque_eq_zero] at h
  exact h

/-- One coordinate of the sum of the three positions along body curves. -/
def totalPositionCoordinateCurve (q : Fin 3 → ℝ → Point) (k : Fin 2) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, q i t k

/-- The derivative of the coordinate sum of positions equals the total
    momentum coordinate for unit masses. -/
theorem hasDerivAt_totalPositionCoordinateCurve
    {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {k : Fin 2} {t : ℝ}
    (hq : HasBodyCoordDerivAt q v t) :
    HasDerivAt (totalPositionCoordinateCurve q k)
      (∑ i : Fin 3, v i k) t := by
  have h0 : HasDerivAt (fun τ => q 0 τ k) (v 0 k) t := hq 0 k
  have h1 : HasDerivAt (fun τ => q 1 τ k) (v 1 k) t := hq 1 k
  have h2 : HasDerivAt (fun τ => q 2 τ k) (v 2 k) t := hq 2 k
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : totalPositionCoordinateCurve q k =ᶠ[𝓝 t]
      ((fun τ => q 0 τ k) + ((fun τ => q 1 τ k) + (fun τ => q 2 τ k))) := by
    filter_upwards [] with τ
    simp [totalPositionCoordinateCurve, Fin.sum_univ_succ]
  simpa [Fin.sum_univ_succ] using hs.congr_of_eventuallyEq hfun

/-- If the total momentum coordinate vanishes throughout an open preconnected
    interval, that coordinate of the center-of-mass position is constant. -/
theorem totalPositionCoordinate_eq_on_of_totalMomentum_zero
    {q v : Fin 3 → ℝ → Point} {I : Set ℝ} {k : Fin 2}
    (hopen : IsOpen I) (hconn : IsPreconnected I)
    (hq : ∀ t ∈ I, HasBodyCoordDerivAt q (fun i => v i t) t)
    (hzero : ∀ t ∈ I, (∑ i : Fin 3, v i t k) = 0)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    totalPositionCoordinateCurve q k s = totalPositionCoordinateCurve q k t := by
  apply hopen.is_const_of_deriv_eq_zero hconn
  · intro x hx
    exact (hasDerivAt_totalPositionCoordinateCurve (k := k) (hq x hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_totalPositionCoordinateCurve (k := k) (hq x hx)).deriv]
    simpa using hzero x hx
  · exact hs
  · exact ht
/-- One coordinate of total linear momentum along a velocity curve. -/
def totalMomentumCoordinateCurve (v : Fin 3 → ℝ → Point) (k : Fin 2) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, v i t k

/-- The derivative of a total-momentum coordinate is the corresponding
    coordinate of the sum of accelerations. -/
theorem hasDerivAt_totalMomentumCoordinateCurve
    {v : Fin 3 → ℝ → Point} {a : Fin 3 → Point} {k : Fin 2} {t : ℝ}
    (hv : HasBodyCoordDerivAt v a t) :
    HasDerivAt (totalMomentumCoordinateCurve v k)
      (∑ i : Fin 3, a i k) t := by
  have h0 : HasDerivAt (fun τ => v 0 τ k) (a 0 k) t := hv 0 k
  have h1 : HasDerivAt (fun τ => v 1 τ k) (a 1 k) t := hv 1 k
  have h2 : HasDerivAt (fun τ => v 2 τ k) (a 2 k) t := hv 2 k
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : totalMomentumCoordinateCurve v k =ᶠ[𝓝 t]
      ((fun τ => v 0 τ k) + ((fun τ => v 1 τ k) + (fun τ => v 2 τ k))) := by
    filter_upwards [] with τ
    simp [totalMomentumCoordinateCurve, Fin.sum_univ_succ]
  simpa [Fin.sum_univ_succ] using hs.congr_of_eventuallyEq hfun

/-- On a Newton curve, each coordinate of total linear momentum has zero
    derivative, by pairwise cancellation of internal forces. -/
theorem hasDerivAt_totalMomentumCoordinateCurve_newton_zero
    {q v : Fin 3 → ℝ → Point} {t : ℝ} {k : Fin 2}
    (hv : HasBodyCoordDerivAt v
      (fun i => unitAcceleration (fun j => q j t) i) t) :
    HasDerivAt (totalMomentumCoordinateCurve v k) 0 t := by
  have h := hasDerivAt_totalMomentumCoordinateCurve (k := k) hv
  have hforce := unitAcceleration_sum_eq_zero (fun i => q i t)
  have hcoord :
      (∑ i : Fin 3, unitAcceleration (fun j => q j t) i k) = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using congrArg (fun p : Point => p k) hforce
  rw [hcoord] at h
  exact h

/-- The packed Newton solution yields the hypotheses needed by the angular
    momentum derivative identity at each point of its time set. -/
theorem hasDerivAt_angularMomentumCurve_classicalNewton_zero
    {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt
      (angularMomentumCurve (fun i τ => (z τ).1 i) (fun i τ => (z τ).2 i)) 0 t := by
  have hq : HasBodyCoordDerivAt (fun i τ => (z τ).1 i)
      (fun i => (z t).2 i) t := by
    intro i k
    exact (classicalNewton_body_coordinate_derivatives i hsol ht).1 k
  have hv : HasBodyCoordDerivAt (fun i τ => (z τ).2 i)
      (fun i => unitAcceleration (z t).1 i) t := by
    intro i k
    exact (classicalNewton_body_coordinate_derivatives i hsol ht).2 k
  exact hasDerivAt_angularMomentumCurve_newton_zero hq hv

/-- A zero derivative makes angular momentum constant on any open
    preconnected time interval. The Newton-specific zero derivative is supplied
    by `hasDerivAt_angularMomentumCurve_newton_zero`. -/
theorem angularMomentum_eq_on_of_zero_derivative
    {q v : Fin 3 → ℝ → Point} {I : Set ℝ}
    (hopen : IsOpen I) (hconn : IsPreconnected I)
    (hdiff : DifferentiableOn ℝ (angularMomentumCurve q v) I)
    (hzero : ∀ t ∈ I, HasDerivAt (angularMomentumCurve q v) 0 t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    angularMomentumCurve q v s = angularMomentumCurve q v t := by
  apply hopen.is_const_of_deriv_eq_zero hconn hdiff
  · intro x hx
    rw [(hzero x hx).deriv]
    simp
  · exact hs
  · exact ht

/-- The analogous interval-constancy principle for a coordinate of total
    linear momentum. -/
theorem totalMomentumCoordinate_eq_on_of_zero_derivative
    {v : Fin 3 → ℝ → Point} {k : Fin 2} {I : Set ℝ}
    (hopen : IsOpen I) (hconn : IsPreconnected I)
    (hdiff : DifferentiableOn ℝ (totalMomentumCoordinateCurve v k) I)
    (hzero : ∀ t ∈ I,
      HasDerivAt (totalMomentumCoordinateCurve v k) 0 t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    totalMomentumCoordinateCurve v k s = totalMomentumCoordinateCurve v k t := by
  apply hopen.is_const_of_deriv_eq_zero hconn hdiff
  · intro x hx
    rw [(hzero x hx).deriv]
    simp
  · exact hs
  · exact ht


/-- Angular momentum is constant on every preconnected open interval of a
    classical Newton solution. -/
theorem angularMomentum_eq_on_classicalNewtonSolution
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    angularMomentumCurve (fun i τ => (z τ).1 i) (fun i τ => (z τ).2 i) s =
      angularMomentumCurve (fun i τ => (z τ).1 i) (fun i τ => (z τ).2 i) t := by
  apply angularMomentum_eq_on_of_zero_derivative hsol.1 hconn
  · intro x hx
    exact (hasDerivAt_angularMomentumCurve_classicalNewton_zero hsol hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact hasDerivAt_angularMomentumCurve_classicalNewton_zero hsol hx
  · exact hs
  · exact ht

end

end DroppingThreeBodies