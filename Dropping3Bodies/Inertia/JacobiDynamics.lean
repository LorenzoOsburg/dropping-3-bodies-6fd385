module

public import Dropping3Bodies.Inertia.JacobiNewton
public import Dropping3Bodies.Dynamics.GeneralEnergy
public import Dropping3Bodies.EqualMass.FrameCalculus
public import Mathlib.Tactic

@[expose] public section

/-! Coordinate derivatives of Jacobi matrices along body curves. -/

namespace DroppingThreeBodies

noncomputable section

/-- Jacobi matrix along a time-dependent configuration. -/
def jacobiMatrixCurve (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ := jacobiMatrix m (fun i => q i t)

/-- A single entry of the weighted body-position recovery matrix along a
    curve. -/
def jacobiRecoveryEntryCurve (m : Fin 3 → ℝ)
    (q : Fin 3 → ℝ → Point) (r c : Fin 2) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, m i * q i t r * jacobiBodyCoeff m i c

/-- Differentiating the finite weighted recovery sum differentiates only the
    body coordinates; the inverse Jacobi coefficients are constant. -/
theorem hasDerivAt_jacobiRecoveryEntryCurve
    (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point) (v : Fin 3 → Point)
    (t : ℝ) (r c : Fin 2)
    (hq : HasBodyCoordDerivAt q v t) :
    HasDerivAt (fun s => jacobiRecoveryEntryCurve m q r c s)
      (∑ i : Fin 3, m i * v i r * jacobiBodyCoeff m i c) t := by
  have h0 := (hq 0 r).const_mul (m 0 * jacobiBodyCoeff m 0 c)
  have h1 := (hq 1 r).const_mul (m 1 * jacobiBodyCoeff m 1 c)
  have h2 := (hq 2 r).const_mul (m 2 * jacobiBodyCoeff m 2 c)
  have hsum := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : (fun s => jacobiRecoveryEntryCurve m q r c s) =ᶠ[nhds t]
      ((fun s => (m 0 * jacobiBodyCoeff m 0 c) * q 0 s r) +
        ((fun s => (m 1 * jacobiBodyCoeff m 1 c) * q 1 s r) +
          (fun s => (m 2 * jacobiBodyCoeff m 2 c) * q 2 s r))) := by
    filter_upwards [] with s
    simp [jacobiRecoveryEntryCurve, Fin.sum_univ_succ, mul_assoc]
    ring
  simpa [jacobiRecoveryEntryCurve, Fin.sum_univ_succ,
    mul_assoc, mul_left_comm, mul_comm] using hsum.congr_of_eventuallyEq hfun

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Mass-normalized Jacobi coordinates and their inverse", `eq:Qrecovery`.
    Project-derived derivative of the componentwise recovery identity. -/
theorem hasDerivAt_jacobiMatrixCurve_entry
    (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point) (v : Fin 3 → Point)
    (t : ℝ) (r c : Fin 2)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hq : HasBodyCoordDerivAt q v t) :
    HasDerivAt (fun s => jacobiMatrixCurve m q s r c)
      (jacobiMatrix m v r c) t := by
  have hrec := hasDerivAt_jacobiRecoveryEntryCurve m q v t r c hq
  have hfun : (fun s => jacobiMatrixCurve m q s r c) =ᶠ[nhds t]
      (fun s => jacobiRecoveryEntryCurve m q r c s) := by
    filter_upwards [] with s
    simpa [jacobiMatrixCurve, jacobiRecoveryEntryCurve,
      jacobiBodyRecoveryMatrix, jacobiBodyCoeff] using
      (congrFun (congrFun (jacobiBodyRecoveryMatrix_eq_jacobiMatrix
        m (fun i => q i s) hm0 hm1 hm2) r) c).symm
  have htarget :
      (∑ i : Fin 3, m i * v i r * jacobiBodyCoeff m i c) =
        jacobiMatrix m v r c := by
    simpa [jacobiBodyRecoveryMatrix, jacobiBodyCoeff] using
      congrFun (congrFun (jacobiBodyRecoveryMatrix_eq_jacobiMatrix
        m v hm0 hm1 hm2) r) c
  rw [← htarget]
  exact hrec.congr_of_eventuallyEq hfun

/-- Along a general-mass Newton solution, the derivative of the Jacobi
    position matrix is the Jacobi matrix formed from the velocities. -/
theorem generalNewton_jacobiPositionMatrix_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    HasDerivAt
      (fun s => jacobiMatrixCurve m (fun i τ => (z τ).1 i) s)
      (jacobiMatrix m (fun i => (z t).2 i)) t := by
  have hq : HasBodyCoordDerivAt (fun i s => (z s).1 i)
      (fun i => (z t).2 i) t := by
    intro i k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (generalNewton_body_vector_derivatives i hsol ht).1
  apply hasDerivAt_pi.2
  intro r
  apply hasDerivAt_pi.2
  intro c
  exact hasDerivAt_jacobiMatrixCurve_entry m
    (fun i τ => (z τ).1 i) (fun i => (z t).2 i) t r c hm0 hm1 hm2 hq

/-- Along a general-mass Newton solution, the derivative of the Jacobi
    velocity matrix is the Jacobi matrix formed from the accelerations. -/
theorem generalNewton_jacobiVelocityMatrix_deriv
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    HasDerivAt
      (fun s => jacobiMatrixCurve m (fun i τ => (z τ).2 i) s)
      (jacobiMatrix m (fun i => generalAcceleration G m (z t).1 i)) t := by
  have hv : HasBodyCoordDerivAt (fun i s => (z s).2 i)
      (fun i => generalAcceleration G m (z t).1 i) t := by
    intro i k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (generalNewton_body_vector_derivatives i hsol ht).2
  apply hasDerivAt_pi.2
  intro r
  apply hasDerivAt_pi.2
  intro c
  exact hasDerivAt_jacobiMatrixCurve_entry m
    (fun i τ => (z τ).2 i)
    (fun i => generalAcceleration G m (z t).1 i) t r c hm0 hm1 hm2 hv

/-- The derivative of the Jacobi velocity matrix equals `-Q K`; together
    with the position derivative theorem this is the solution-level equation
    `Q¨ = -Q K`. Source: [DroppingMontgomery2026], frozen 2026-10-29,
    Section "Newton's equations as a matrix equation", `eq:matrixNewton`.
    The solution-level deduction is project-derived from the first-order ODE. -/
theorem generalNewton_jacobiMatrix_secondDerivative
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    HasDerivAt
      (fun s => jacobiMatrixCurve m (fun i τ => (z τ).2 i) s)
      (-(jacobiMatrix m (z t).1 * jacobiForceMatrix G m (z t).1)) t := by
  have hacc := jacobiMatrix_acceleration_eq_jacobiAccelerationMatrix
    G m (z t).1 hm0 hm1 hm2
  have hforce := jacobiAccelerationMatrix_eq_neg_mul_forceMatrix
    G m (z t).1 hm0 hm1 hm2
  have htarget :
      jacobiMatrix m (fun i => generalAcceleration G m (z t).1 i) =
        -(jacobiMatrix m (z t).1 * jacobiForceMatrix G m (z t).1) :=
    hacc.trans hforce
  rw [← htarget]
  exact generalNewton_jacobiVelocityMatrix_deriv hsol ht hm0 hm1 hm2

end

end DroppingThreeBodies
