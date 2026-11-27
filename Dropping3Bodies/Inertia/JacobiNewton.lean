module

public import Dropping3Bodies.Inertia.Jacobi
public import Dropping3Bodies.Dynamics.GeneralNewton
public import Mathlib.Tactic
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-! Algebraic Jacobi force matrix and its positive quadratic form. -/

namespace DroppingThreeBodies

noncomputable section

/-- The symmetric force matrix in the planned Jacobi equation
    `Q¨ = -Q K`. Its three summands correspond to the unordered body pairs.
    Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:matrixNewton`. -/
def jacobiForceMatrix (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix (Fin 2) (Fin 2) ℝ := fun a b => G * (
      (m 0 * m 1 * inverseCubeDistance q 0 1) *
        jacobiPairCoeff01 m a * jacobiPairCoeff01 m b +
      (m 0 * m 2 * inverseCubeDistance q 0 2) *
        jacobiPairCoeff02 m a * jacobiPairCoeff02 m b +
      (m 1 * m 2 * inverseCubeDistance q 1 2) *
        jacobiPairCoeff12 m a * jacobiPairCoeff12 m b)

/-- Coefficient-level form of the three pair contributions to `wᵀ K w`. -/
def jacobiWeightedPairForceQuadratic
    (G α01 α02 α12 : ℝ) (m : Fin 3 → ℝ) (w : Fin 2 → ℝ) : ℝ :=
  G * (α01 * (jacobiCoeffDot (jacobiPairCoeff01 m) w) ^ 2 +
    α02 * (jacobiCoeffDot (jacobiPairCoeff02 m) w) ^ 2 +
    α12 * (jacobiCoeffDot (jacobiPairCoeff12 m) w) ^ 2)

/-- Expanding the two finite matrix sums gives the pairwise square formula
    `eq:Kpositive`. -/
theorem jacobiForceMatrix_quadratic_eq_pairForm
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) (w : Fin 2 → ℝ) :
    matrixQuadratic (jacobiForceMatrix G m q) w =
      jacobiWeightedPairForceQuadratic G
        (m 0 * m 1 * inverseCubeDistance q 0 1)
        (m 0 * m 2 * inverseCubeDistance q 0 2)
        (m 1 * m 2 * inverseCubeDistance q 1 2) m w := by
  simp [matrixQuadratic, jacobiForceMatrix, jacobiWeightedPairForceQuadratic,
    jacobiCoeffDot, Fin.sum_univ_succ]
  ring

/-- The force matrix is symmetric because it is a sum of symmetric outer
    products. -/
theorem jacobiForceMatrix_symmetric
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix.transpose (jacobiForceMatrix G m q) = jacobiForceMatrix G m q := by
  ext a b
  simp only [Matrix.transpose_apply]
  unfold jacobiForceMatrix
  ring

/-- Strict positive definiteness of the Jacobi force matrix for a
    collision-free configuration, positive masses, and positive G. The
    pair-vector independence is the project-derived proof of `eq:Kpositive`.
    Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:Kpositive`. -/
theorem jacobiForceMatrix_quadratic_pos
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hG : 0 < G) (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hcollision : CollisionFree q) (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    0 < matrixQuadratic (jacobiForceMatrix G m q) w := by
  rw [jacobiForceMatrix_quadratic_eq_pairForm]
  have h01 : 0 < m 0 * m 1 * inverseCubeDistance q 0 1 := by
    unfold inverseCubeDistance
    exact mul_pos (mul_pos hm0 hm1) (zpow_pos (dist_pos.mpr
      (hcollision 0 1 (by decide))) _)
  have h02 : 0 < m 0 * m 2 * inverseCubeDistance q 0 2 := by
    unfold inverseCubeDistance
    exact mul_pos (mul_pos hm0 hm2) (zpow_pos (dist_pos.mpr
      (hcollision 0 2 (by decide))) _)
  have h12 : 0 < m 1 * m 2 * inverseCubeDistance q 1 2 := by
    unfold inverseCubeDistance
    exact mul_pos (mul_pos hm1 hm2) (zpow_pos (dist_pos.mpr
      (hcollision 1 2 (by decide))) _)
  unfold jacobiWeightedPairForceQuadratic
  rcases exists_jacobiPairCoeff_dot_ne_zero m hm0 hm1 hm2 w hw with hdir | hdir
  · have hsq : 0 <
        (jacobiCoeffDot (jacobiPairCoeff01 m) w) ^ 2 := sq_pos_of_ne_zero hdir
    positivity
  · have hsq : 0 <
        (jacobiCoeffDot (jacobiPairCoeff02 m) w) ^ 2 := sq_pos_of_ne_zero hdir
    positivity

/-- Weighted acceleration matrix before pair regrouping. -/
def jacobiAccelerationMatrix
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix (Fin 2) (Fin 2) ℝ := fun r c =>
  ∑ i : Fin 3, m i * generalAcceleration G m q i r *
    jacobiBodyCoeff m i c

/-- The six ordered acceleration terms grouped into the three unordered
    Newton pairs, before replacing each pair by its Jacobi outer product. -/
def jacobiAccelerationPairSum
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (r c : Fin 2) : ℝ :=
  G * m 0 * m 1 * inverseCubeDistance q 0 1 *
      (q 1 - q 0) r *
        (jacobiBodyCoeff m 0 c - jacobiBodyCoeff m 1 c) +
  G * m 0 * m 2 * inverseCubeDistance q 0 2 *
      (q 2 - q 0) r *
        (jacobiBodyCoeff m 0 c - jacobiBodyCoeff m 2 c) +
  G * m 1 * m 2 * inverseCubeDistance q 1 2 *
      (q 2 - q 1) r *
        (jacobiBodyCoeff m 1 c - jacobiBodyCoeff m 2 c)

/-- Expanding only the general acceleration sum pairs its six directed force
    terms into three contributions; all Jacobi coefficients remain opaque.
    Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:matrixNewton`;
    project-derived finite regrouping. -/
theorem jacobiAccelerationMatrix_eq_pairSum
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) (r c : Fin 2) :
    jacobiAccelerationMatrix G m q r c =
      jacobiAccelerationPairSum G m q r c := by
  have h01 : inverseCubeDistance q 1 0 = inverseCubeDistance q 0 1 := by
    simp [inverseCubeDistance, dist_comm]
  have h02 : inverseCubeDistance q 2 0 = inverseCubeDistance q 0 2 := by
    simp [inverseCubeDistance, dist_comm]
  have h12 : inverseCubeDistance q 2 1 = inverseCubeDistance q 1 2 := by
    simp [inverseCubeDistance, dist_comm]
  simp [jacobiAccelerationMatrix, jacobiAccelerationPairSum,
    generalAcceleration, Fin.sum_univ_succ, h01, h02, h12]
  ring

/-- One Newton pair contribution after expressing its displacement in the
    Jacobi columns and its body-coefficient difference as `-c`. -/
theorem jacobiPairContribution_entry
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ)
    (weight : ℝ) (r s : Fin 2) (qDiff : Point)
    (dLeft dRight : Fin 2 → ℝ)
    (hdisp : qDiff r = jacobiCoeffDot c (fun k => Q r k))
    (hbody : dLeft s - dRight s = -c s) :
    weight * qDiff r * (dLeft s - dRight s) =
      -(∑ k : Fin 2, Q r k * (weight * c k * c s)) := by
  rw [hdisp, hbody]
  simp only [jacobiCoeffDot, Fin.sum_univ_succ]
  simp only [show (1 : Fin 2) = Fin.succ 0 by decide]
  ring

/-- The contribution of pair (0,1) is its negative Jacobi outer product.
    Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:matrixNewton` and
    `eq:Kpositive`; project-derived component identity. -/
theorem jacobiPair01_accelerationContribution_entry
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (r s : Fin 2) :
    (G * m 0 * m 1 * inverseCubeDistance q 0 1) *
        (q 1 - q 0) r *
        (jacobiBodyCoeff m 0 s - jacobiBodyCoeff m 1 s) =
      -(∑ k : Fin 2, jacobiMatrix m q r k *
        (G * m 0 * m 1 * inverseCubeDistance q 0 1 *
          jacobiPairCoeff01 m k * jacobiPairCoeff01 m s)) := by
  have hdisp : (q 1 - q 0) r =
      jacobiCoeffDot (jacobiPairCoeff01 m)
        (fun k => jacobiMatrix m q r k) := by
    have hrec := congrArg (fun p : Point => p r)
      (jacobiPairCoeff01_reconstructs m q hm0 hm1)
    simpa [jacobiCoeffDot, jacobiMatrix_col_zero,
      jacobiMatrix_col_one] using hrec.symm
  have hbody : jacobiBodyCoeff m 0 s - jacobiBodyCoeff m 1 s =
      -jacobiPairCoeff01 m s := by
    have hcoeff := congrFun
      (jacobiPairCoeff01_eq_bodyDifference m hm0 hm1 hm2) s
    rw [hcoeff]
    ring
  exact jacobiPairContribution_entry (jacobiMatrix m q)
    (jacobiPairCoeff01 m)
    (G * m 0 * m 1 * inverseCubeDistance q 0 1)
    r s (q 1 - q 0) (jacobiBodyCoeff m 0) (jacobiBodyCoeff m 1)
    hdisp hbody

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:matrixNewton` and
    `eq:Kpositive`; project-derived component identity. -/
theorem jacobiPair02_accelerationContribution_entry
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (r s : Fin 2) :
    (G * m 0 * m 2 * inverseCubeDistance q 0 2) *
        (q 2 - q 0) r *
        (jacobiBodyCoeff m 0 s - jacobiBodyCoeff m 2 s) =
      -(∑ k : Fin 2, jacobiMatrix m q r k *
        (G * m 0 * m 2 * inverseCubeDistance q 0 2 *
          jacobiPairCoeff02 m k * jacobiPairCoeff02 m s)) := by
  have hdisp : (q 2 - q 0) r =
      jacobiCoeffDot (jacobiPairCoeff02 m)
        (fun k => jacobiMatrix m q r k) := by
    have hrec := congrArg (fun p : Point => p r)
      (jacobiPairCoeff02_reconstructs m q hm0 hm1 hm2)
    simpa [jacobiCoeffDot, jacobiMatrix_col_zero,
      jacobiMatrix_col_one] using hrec.symm
  have hbody : jacobiBodyCoeff m 0 s - jacobiBodyCoeff m 2 s =
      -jacobiPairCoeff02 m s := by
    have hcoeff := congrFun
      (jacobiPairCoeff02_eq_bodyDifference m hm0 hm1 hm2) s
    rw [hcoeff]
    ring
  exact jacobiPairContribution_entry (jacobiMatrix m q)
    (jacobiPairCoeff02 m)
    (G * m 0 * m 2 * inverseCubeDistance q 0 2)
    r s (q 2 - q 0) (jacobiBodyCoeff m 0) (jacobiBodyCoeff m 2)
    hdisp hbody

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:matrixNewton` and
    `eq:Kpositive`; project-derived component identity. -/
theorem jacobiPair12_accelerationContribution_entry
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (r s : Fin 2) :
    (G * m 1 * m 2 * inverseCubeDistance q 1 2) *
        (q 2 - q 1) r *
        (jacobiBodyCoeff m 1 s - jacobiBodyCoeff m 2 s) =
      -(∑ k : Fin 2, jacobiMatrix m q r k *
        (G * m 1 * m 2 * inverseCubeDistance q 1 2 *
          jacobiPairCoeff12 m k * jacobiPairCoeff12 m s)) := by
  have hdisp : (q 2 - q 1) r =
      jacobiCoeffDot (jacobiPairCoeff12 m)
        (fun k => jacobiMatrix m q r k) := by
    have hrec := congrArg (fun p : Point => p r)
      (jacobiPairCoeff12_reconstructs m q hm0 hm1 hm2)
    simpa [jacobiCoeffDot, jacobiMatrix_col_zero,
      jacobiMatrix_col_one] using hrec.symm
  have hbody : jacobiBodyCoeff m 1 s - jacobiBodyCoeff m 2 s =
      -jacobiPairCoeff12 m s := by
    have hcoeff := congrFun
      (jacobiPairCoeff12_eq_bodyDifference m hm0 hm1 hm2) s
    rw [hcoeff]
    ring
  exact jacobiPairContribution_entry (jacobiMatrix m q)
    (jacobiPairCoeff12 m)
    (G * m 1 * m 2 * inverseCubeDistance q 1 2)
    r s (q 2 - q 1) (jacobiBodyCoeff m 1) (jacobiBodyCoeff m 2)
    hdisp hbody

/-- Configuration-level Newton identity for the Jacobi acceleration matrix.
    Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:matrixNewton`.
    This theorem supplies its pairwise force calculation; converting it to a
    twice differentiable solution curve is separate. -/
theorem jacobiAccelerationMatrix_eq_neg_mul_forceMatrix
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiAccelerationMatrix G m q =
      -(jacobiMatrix m q * jacobiForceMatrix G m q) := by
  ext r s
  rw [jacobiAccelerationMatrix_eq_pairSum]
  simp only [jacobiAccelerationPairSum]
  rw [jacobiPair01_accelerationContribution_entry G m q hm0 hm1 hm2 r s,
    jacobiPair02_accelerationContribution_entry G m q hm0 hm1 hm2 r s,
    jacobiPair12_accelerationContribution_entry G m q hm0 hm1 hm2 r s]
  simp [jacobiForceMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem jacobiMatrix_acceleration_eq_jacobiAccelerationMatrix
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiMatrix m (fun i => generalAcceleration G m q i) =
      jacobiAccelerationMatrix G m q := by
  have hrec := jacobiBodyRecoveryMatrix_eq_jacobiMatrix m
    (fun i => generalAcceleration G m q i) hm0 hm1 hm2
  ext r c
  change jacobiMatrix m (fun i => generalAcceleration G m q i) r c =
    jacobiBodyRecoveryMatrix m (fun i => generalAcceleration G m q i) r c
  exact (congrFun (congrFun hrec r) c).symm

end

end DroppingThreeBodies
