module

public import Dropping3Bodies.Geometry.Inertia
public import Mathlib.Tactic

@[expose] public section

/-! Mass constants and Jacobi coordinates for three positive masses. -/

namespace DroppingThreeBodies

noncomputable section

/-- Total mass of bodies zero and one. -/
def jacobiPairMass (m : Fin 3 → ℝ) : ℝ := m 0 + m 1

/-- First reduced Jacobi mass. -/
def jacobiMu (m : Fin 3 → ℝ) : ℝ := m 0 * m 1 / jacobiPairMass m

/-- Second reduced Jacobi mass. -/
def jacobiNu (m : Fin 3 → ℝ) : ℝ := m 2 * jacobiPairMass m / totalMass m

theorem jacobiPairMass_pos (m : Fin 3 → ℝ)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) : 0 < jacobiPairMass m := by
  simp [jacobiPairMass]
  positivity

theorem totalMass_pos_of_positive (m : Fin 3 → ℝ)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    0 < totalMass m := by
  simp [totalMass, Fin.sum_univ_succ]
  positivity

theorem jacobiMu_pos (m : Fin 3 → ℝ)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) : 0 < jacobiMu m := by
  exact div_pos (mul_pos hm0 hm1) (jacobiPairMass_pos m hm0 hm1)

theorem jacobiNu_pos (m : Fin 3 → ℝ)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    0 < jacobiNu m := by
  exact div_pos (mul_pos hm2 (jacobiPairMass_pos m hm0 hm1))
    (totalMass_pos_of_positive m hm0 hm1 hm2)

theorem sqrt_jacobiMu_pos (m : Fin 3 → ℝ)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) : 0 < Real.sqrt (jacobiMu m) :=
  Real.sqrt_pos.2 (jacobiMu_pos m hm0 hm1)

theorem sqrt_jacobiNu_pos (m : Fin 3 → ℝ)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    0 < Real.sqrt (jacobiNu m) :=
  Real.sqrt_pos.2 (jacobiNu_pos m hm0 hm1 hm2)

/-- Center of mass of the first pair. -/
def jacobiPairCenter (m : Fin 3 → ℝ) (q : Fin 3 → Point) : Point :=
  (jacobiPairMass m)⁻¹ • (m 0 • q 0 + m 1 • q 1)

/-- First mass-normalized Jacobi vector. -/
def jacobiX (m : Fin 3 → ℝ) (q : Fin 3 → Point) : Point :=
  Real.sqrt (jacobiMu m) • (q 1 - q 0)

/-- Second mass-normalized Jacobi vector. -/
def jacobiY (m : Fin 3 → ℝ) (q : Fin 3 → Point) : Point :=
  Real.sqrt (jacobiNu m) • (q 2 - jacobiPairCenter m q)

/-- The two Jacobi vectors as columns of a planar matrix. -/
def jacobiMatrix (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun r c => if c = 0 then jacobiX m q r else jacobiY m q r

/-- Jacobi moment, the squared Frobenius norm of the two coordinate columns. -/
def jacobiMoment (m : Fin 3 → ℝ) (q : Fin 3 → Point) : ℝ :=
  ‖jacobiX m q‖ ^ 2 + ‖jacobiY m q‖ ^ 2

@[simp] theorem jacobiMatrix_col_zero (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (r : Fin 2) : jacobiMatrix m q r 0 = jacobiX m q r := by
  simp [jacobiMatrix]

@[simp] theorem jacobiMatrix_col_one (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (r : Fin 2) : jacobiMatrix m q r 1 = jacobiY m q r := by
  simp [jacobiMatrix]

theorem jacobiMatrix_det_eq_cross (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix.det (jacobiMatrix m q) = cross (jacobiX m q) (jacobiY m q) := by
  rw [Matrix.det_fin_two]
  simp [jacobiMatrix, cross]
  ring

/-- The pair center is an affine combination of the two positions; hence the
    oriented area using `q₂-p` equals the original signed area. -/
theorem jacobi_pairCross_eq_signedDoubleArea
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    cross (q 1 - q 0) (q 2 - jacobiPairCenter m q) = signedDoubleArea q := by
  have hS : jacobiPairMass m ≠ 0 := ne_of_gt (jacobiPairMass_pos m hm0 hm1)
  simp [jacobiPairCenter, jacobiPairMass, signedDoubleArea, cross]
  field_simp [hS]
  ring

/-- Determinant of the two mass-normalized Jacobi columns. -/
theorem jacobiMatrix_det_eq_sqrtMass_mul_area
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    Matrix.det (jacobiMatrix m q) =
      Real.sqrt (jacobiMu m) * Real.sqrt (jacobiNu m) * signedDoubleArea q := by
  rw [jacobiMatrix_det_eq_cross]
  have hcross : cross (jacobiX m q) (jacobiY m q) =
      Real.sqrt (jacobiMu m) * Real.sqrt (jacobiNu m) *
        cross (q 1 - q 0) (q 2 - jacobiPairCenter m q) := by
    simp [jacobiX, jacobiY, cross]
    ring
  rw [hcross, jacobi_pairCross_eq_signedDoubleArea m q hm0 hm1]

theorem jacobiPairCenter_eq_q0_add_fraction
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    jacobiPairCenter m q =
      q 0 + (m 1 / jacobiPairMass m) • (q 1 - q 0) := by
  have hS : jacobiPairMass m ≠ 0 := ne_of_gt (jacobiPairMass_pos m hm0 hm1)
  ext k
  simp [jacobiPairCenter, jacobiPairMass]
  field_simp [hS]
  ring

theorem jacobiPairCenter_eq_q1_sub_fraction
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    jacobiPairCenter m q =
      q 1 - (m 0 / jacobiPairMass m) • (q 1 - q 0) := by
  have hS : jacobiPairMass m ≠ 0 := ne_of_gt (jacobiPairMass_pos m hm0 hm1)
  ext k
  simp [jacobiPairCenter, jacobiPairMass]
  field_simp [hS]
  ring

/-- Inverting the mass normalization recovers the first relative position. -/
theorem jacobiX_unscale
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    (Real.sqrt (jacobiMu m))⁻¹ • jacobiX m q = q 1 - q 0 := by
  have hs := sqrt_jacobiMu_pos m hm0 hm1
  have hinv : (Real.sqrt (jacobiMu m))⁻¹ * Real.sqrt (jacobiMu m) = 1 :=
    inv_mul_cancel₀ hs.ne'
  simp [jacobiX, smul_smul, hinv]

/-- Inverting the second mass normalization recovers the pair-relative
    position of body two. -/
theorem jacobiY_unscale
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    (Real.sqrt (jacobiNu m))⁻¹ • jacobiY m q =
      q 2 - jacobiPairCenter m q := by
  have hs := sqrt_jacobiNu_pos m hm0 hm1 hm2
  have hinv : (Real.sqrt (jacobiNu m))⁻¹ * Real.sqrt (jacobiNu m) = 1 :=
    inv_mul_cancel₀ hs.ne'
  simp [jacobiY, smul_smul, hinv]

theorem jacobi_q0_reconstruction_from_pairCenter
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    q 0 = jacobiPairCenter m q -
      (m 1 / jacobiPairMass m) •
        ((Real.sqrt (jacobiMu m))⁻¹ • jacobiX m q) := by
  rw [jacobiX_unscale m q hm0 hm1]
  rw [jacobiPairCenter_eq_q0_add_fraction m q hm0 hm1]
  ext k
  simp

theorem jacobi_q1_reconstruction_from_pairCenter
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    q 1 = jacobiPairCenter m q +
      (m 0 / jacobiPairMass m) •
        ((Real.sqrt (jacobiMu m))⁻¹ • jacobiX m q) := by
  rw [jacobiX_unscale m q hm0 hm1]
  rw [jacobiPairCenter_eq_q1_sub_fraction m q hm0 hm1]
  ext k
  simp

theorem jacobi_q2_reconstruction_from_pairCenter
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    q 2 = jacobiPairCenter m q +
      (Real.sqrt (jacobiNu m))⁻¹ • jacobiY m q := by
  rw [jacobiY_unscale m q hm0 hm1 hm2]
  abel

/-- If the full configuration is centered, its first-pair center is the
    negative mass fraction of the second Jacobi displacement. -/
theorem jacobiPairCenter_eq_neg_fraction_of_centered
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hcenter : weightedPosition m q = 0) :
    jacobiPairCenter m q =
      -(m 2 / totalMass m) • (q 2 - jacobiPairCenter m q) := by
  have hS := jacobiPairMass_pos m hm0 hm1
  have hM := totalMass_pos_of_positive m hm0 hm1 hm2
  ext k
  have hc := congrArg (fun p : Point => p k) hcenter
  simp [weightedPosition, totalMass, Fin.sum_univ_succ, jacobiPairCenter,
    jacobiPairMass] at hc ⊢
  field_simp [ne_of_gt hS, ne_of_gt hM]
  nlinarith

private theorem norm_sq_add_smul_eq
    (u v : Point) (a : ℝ) :
    ‖u + a • v‖ ^ 2 = ‖u‖ ^ 2 + 2 * a * dot2 u v + a ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_eq_dot2 (u + a • v), norm_sq_eq_dot2 u, norm_sq_eq_dot2 v]
  simp [dot2, smul_eq_mul]
  ring

theorem jacobi_pairDistance02_decomposition
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    q 2 - q 0 = q 2 - jacobiPairCenter m q +
      (m 1 / jacobiPairMass m) • (q 1 - q 0) := by
  rw [jacobiPairCenter_eq_q0_add_fraction m q hm0 hm1]
  abel

theorem jacobi_pairDistance12_decomposition
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    q 2 - q 1 = q 2 - jacobiPairCenter m q -
      (m 0 / jacobiPairMass m) • (q 1 - q 0) := by
  rw [jacobiPairCenter_eq_q1_sub_fraction m q hm0 hm1]
  abel

/-- Pair moment in the unscaled relative Jacobi displacements.
    Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Mass-normalized Jacobi coordinates and their inverse", `eq:massmetric`.
    The scalar pair-moment identity is project-derived from the three
    pairwise-distance decompositions and polarization; it is not a verbatim
    formalization of the displayed matrix identity. -/
theorem pairMoment_eq_totalMass_mul_reducedPairMoments
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    pairMoment m q = totalMass m *
      (jacobiMu m * ‖q 1 - q 0‖ ^ 2 +
        jacobiNu m * ‖q 2 - jacobiPairCenter m q‖ ^ 2) := by
  let r := q 1 - q 0
  let s := q 2 - jacobiPairCenter m q
  let α := m 1 / jacobiPairMass m
  let β := m 0 / jacobiPairMass m
  have hS : jacobiPairMass m ≠ 0 := ne_of_gt (jacobiPairMass_pos m hm0 hm1)
  have hM : totalMass m ≠ 0 :=
    ne_of_gt (totalMass_pos_of_positive m hm0 hm1 hm2)
  have h01 : dist (q 0) (q 1) = ‖r‖ := by
    simp [r, dist_eq_norm, norm_sub_rev]
  have h02 : dist (q 0) (q 2) = ‖s + α • r‖ := by
    rw [dist_eq_norm]
    rw [← jacobi_pairDistance02_decomposition m q hm0 hm1]
    simp [norm_sub_rev]
  have h12 : dist (q 1) (q 2) = ‖s - β • r‖ := by
    rw [dist_eq_norm]
    rw [← jacobi_pairDistance12_decomposition m q hm0 hm1]
    simp [norm_sub_rev]
  rw [pairMoment, h01, h12, h02]
  have hminus : s - β • r = s + (-β) • r := by
    calc
      s - β • r = s + -(β • r) := by abel
      _ = s + (-β) • r := by rw [← neg_smul]
  rw [hminus]
  rw [norm_sq_add_smul_eq s r (-β), norm_sq_add_smul_eq s r α]
  simp [r, s, α, β, jacobiMu, jacobiNu, jacobiPairMass, totalMass,
    Fin.sum_univ_succ]
  field_simp [hS, hM]
  ring_nf

private theorem norm_sq_smul_eq (a : ℝ) (u : Point) :
    ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
  calc
    ‖a • u‖ ^ 2 = (|a| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
    _ = |a| ^ 2 * ‖u‖ ^ 2 := by rw [mul_pow]
    _ = a ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]

theorem jacobiMoment_eq_reducedPairMoments
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiMoment m q =
      jacobiMu m * ‖q 1 - q 0‖ ^ 2 +
        jacobiNu m * ‖q 2 - jacobiPairCenter m q‖ ^ 2 := by
  have hμ := jacobiMu_pos m hm0 hm1
  have hν := jacobiNu_pos m hm0 hm1 hm2
  rw [jacobiMoment, jacobiX, jacobiY,
    norm_sq_smul_eq (Real.sqrt (jacobiMu m)) (q 1 - q 0),
    norm_sq_smul_eq (Real.sqrt (jacobiNu m))
      (q 2 - jacobiPairCenter m q),
    Real.sq_sqrt (le_of_lt hμ), Real.sq_sqrt (le_of_lt hν)]

theorem pairMoment_eq_totalMass_mul_jacobiMoment
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    pairMoment m q = totalMass m * jacobiMoment m q := by
  rw [pairMoment_eq_totalMass_mul_reducedPairMoments m q hm0 hm1 hm2,
    jacobiMoment_eq_reducedPairMoments m q hm0 hm1 hm2]

theorem massMoment_eq_jacobiMoment_of_centered
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hcenter : weightedPosition m q = 0) :
    massMoment m q = jacobiMoment m q := by
  have hpair := pairMoment_eq_totalMass_mul_jacobiMoment m q hm0 hm1 hm2
  have hcenterPair := pairMoment_eq_totalMass_mul_massMoment_of_centered
    m q hcenter
  have hM : totalMass m ≠ 0 :=
    ne_of_gt (totalMass_pos_of_positive m hm0 hm1 hm2)
  exact mul_left_cancel₀ hM (hcenterPair.symm.trans hpair)

theorem jacobiMatrix_trace_mul_transpose_eq_jacobiMoment
    (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix.trace (jacobiMatrix m q * Matrix.transpose (jacobiMatrix m q)) =
      jacobiMoment m q := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
    jacobiMoment, jacobiMatrix, jacobiX, jacobiY,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  ring

/-- Jacobi-coordinate coefficient of the oriented pair difference `q₁-q₀`.
    The two entries multiply the columns `jacobiX` and `jacobiY`. -/
def jacobiPairCoeff01 (m : Fin 3 → ℝ) : Fin 2 → ℝ :=
  fun k => if k = 0 then (Real.sqrt (jacobiMu m))⁻¹ else 0

/-- Jacobi-coordinate coefficient of `q₂-q₀`, using the pair-center
    decomposition. -/
def jacobiPairCoeff02 (m : Fin 3 → ℝ) : Fin 2 → ℝ :=
  fun k => if k = 0 then
    (m 1 / jacobiPairMass m) * (Real.sqrt (jacobiMu m))⁻¹
    else (Real.sqrt (jacobiNu m))⁻¹

/-- Jacobi-coordinate coefficient of `q₂-q₁`. -/
def jacobiPairCoeff12 (m : Fin 3 → ℝ) : Fin 2 → ℝ :=
  fun k => jacobiPairCoeff02 m k - jacobiPairCoeff01 m k

/-- Scalar product of two two-coordinate coefficient vectors. -/
def jacobiCoeffDot (c w : Fin 2 → ℝ) : ℝ :=
  c 0 * w 0 + c 1 * w 1

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Mass-normalized Jacobi coordinates and their inverse", `eq:di`.
    Zero-based transcription of the first component; the coefficient is
    independently verified by the following position-recovery theorem. -/
def jacobiBodyCoeffX (m : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  match i with
  | 0 => -(m 1 / jacobiPairMass m) * (Real.sqrt (jacobiMu m))⁻¹
  | 1 => (m 0 / jacobiPairMass m) * (Real.sqrt (jacobiMu m))⁻¹
  | _ => 0

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Mass-normalized Jacobi coordinates and their inverse", `eq:di`.
    Zero-based transcription of the second component, checked by the
    position-recovery theorem below. -/
def jacobiBodyCoeffY (m : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  match i with
  | 0 => -(m 2 / totalMass m) * (Real.sqrt (jacobiNu m))⁻¹
  | 1 => -(m 2 / totalMass m) * (Real.sqrt (jacobiNu m))⁻¹
  | _ => (jacobiPairMass m / totalMass m) *
      (Real.sqrt (jacobiNu m))⁻¹

/-- Constant two-coordinate coefficient of a body position in the inverse
    mass-normalized Jacobi map. -/
def jacobiBodyCoeff (m : Fin 3 → ℝ) (i : Fin 3) : Fin 2 → ℝ :=
  fun k => if k = 0 then jacobiBodyCoeffX m i else jacobiBodyCoeffY m i

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:Kpositive` and the pair
    vectors following it. Project-derived zero-based coefficient identity. -/
theorem jacobiPairCoeff01_eq_bodyDifference
    (m : Fin 3 → ℝ) (hm0 : 0 < m 0) (hm1 : 0 < m 1)
    (_hm2 : 0 < m 2) :
    jacobiPairCoeff01 m = fun k => jacobiBodyCoeff m 1 k -
      jacobiBodyCoeff m 0 k := by
  funext k
  fin_cases k
  · simp [jacobiPairCoeff01, jacobiBodyCoeff, jacobiBodyCoeffX]
    have hS : jacobiPairMass m ≠ 0 :=
      ne_of_gt (jacobiPairMass_pos m hm0 hm1)
    field_simp [hS]
    simp [jacobiPairMass]
  · simp [jacobiPairCoeff01, jacobiBodyCoeff, jacobiBodyCoeffY]

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:Kpositive` and the pair
    vectors following it. Project-derived zero-based coefficient identity. -/
theorem jacobiPairCoeff02_eq_bodyDifference
    (m : Fin 3 → ℝ) (hm0 : 0 < m 0) (hm1 : 0 < m 1)
    (hm2 : 0 < m 2) :
    jacobiPairCoeff02 m = fun k => jacobiBodyCoeff m 2 k -
      jacobiBodyCoeff m 0 k := by
  funext k
  fin_cases k
  · simp [jacobiPairCoeff02, jacobiBodyCoeff, jacobiBodyCoeffX]
  · simp [jacobiPairCoeff02, jacobiBodyCoeff, jacobiBodyCoeffY]
    have hM : totalMass m ≠ 0 :=
      ne_of_gt (totalMass_pos_of_positive m hm0 hm1 hm2)
    field_simp [hM]
    simp [totalMass, Fin.sum_univ_succ]
    simp [jacobiPairMass]
    ring

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:Kpositive` and the pair
    vectors following it. This third identity follows algebraically from
    the first two, in the project's zero-based indexing. -/
theorem jacobiPairCoeff12_eq_bodyDifference
    (m : Fin 3 → ℝ) (hm0 : 0 < m 0) (hm1 : 0 < m 1)
    (hm2 : 0 < m 2) :
    jacobiPairCoeff12 m = fun k => jacobiBodyCoeff m 2 k -
      jacobiBodyCoeff m 1 k := by
  funext k
  rw [jacobiPairCoeff12, jacobiPairCoeff02_eq_bodyDifference m hm0 hm1 hm2,
    jacobiPairCoeff01_eq_bodyDifference m hm0 hm1 hm2]
  ring

theorem jacobiX_eq_weightedBodyCoefficientSum
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    jacobiX m q = fun k =>
      ∑ i : Fin 3, m i * q i k * jacobiBodyCoeffX m i := by
  have hS : jacobiPairMass m ≠ 0 :=
    ne_of_gt (jacobiPairMass_pos m hm0 hm1)
  have hμpos := jacobiMu_pos m hm0 hm1
  have hr : Real.sqrt (jacobiMu m) ≠ 0 :=
    (sqrt_jacobiMu_pos m hm0 hm1).ne'
  have hsquare : (Real.sqrt (jacobiMu m)) ^ 2 = jacobiMu m :=
    Real.sq_sqrt (le_of_lt hμpos)
  ext k
  simp [jacobiX, jacobiBodyCoeffX, Fin.sum_univ_succ]
  field_simp [hS, hr]
  rw [hsquare]
  simp [jacobiMu, jacobiPairMass]
  field_simp [hS]
  ring

theorem jacobiY_eq_weightedBodyCoefficientSum
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiY m q = fun k =>
      ∑ i : Fin 3, m i * q i k * jacobiBodyCoeffY m i := by
  have hS : jacobiPairMass m ≠ 0 :=
    ne_of_gt (jacobiPairMass_pos m hm0 hm1)
  have hM : totalMass m ≠ 0 :=
    ne_of_gt (totalMass_pos_of_positive m hm0 hm1 hm2)
  have hνpos := jacobiNu_pos m hm0 hm1 hm2
  have hr : Real.sqrt (jacobiNu m) ≠ 0 :=
    (sqrt_jacobiNu_pos m hm0 hm1 hm2).ne'
  have hsquare : (Real.sqrt (jacobiNu m)) ^ 2 = jacobiNu m :=
    Real.sq_sqrt (le_of_lt hνpos)
  ext k
  simp [jacobiY, jacobiBodyCoeffY, Fin.sum_univ_succ]
  field_simp [hS, hM, hr]
  rw [hsquare]
  simp [jacobiNu, totalMass, jacobiPairMass, jacobiPairCenter,
    Fin.sum_univ_succ]
  field_simp [hS, hM]
  ring

/-- Matrix of the weighted coordinate sum `Σᵢ mᵢ qᵢ dᵢᵀ` in the two
    mass-normalized Jacobi columns. -/
def jacobiBodyRecoveryMatrix (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix (Fin 2) (Fin 2) ℝ := fun r c =>
  ∑ i : Fin 3, m i * q i r *
    (if c = 0 then jacobiBodyCoeffX m i else jacobiBodyCoeffY m i)

/-- The Jacobi matrix is recovered by the weighted sum of positions times
    the constant inverse-coordinate coefficients. Source:
    [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Mass-normalized Jacobi coordinates and their inverse", `eq:Qrecovery`.
    Project-derived componentwise proof from the two weighted column sums. -/
theorem jacobiBodyRecoveryMatrix_eq_jacobiMatrix
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiBodyRecoveryMatrix m q = jacobiMatrix m q := by
  ext r c
  fin_cases c
  · change (∑ i : Fin 3, m i * q i r * jacobiBodyCoeffX m i) =
      jacobiX m q r
    exact (congrFun (jacobiX_eq_weightedBodyCoefficientSum m q hm0 hm1) r).symm
  · change (∑ i : Fin 3, m i * q i r * jacobiBodyCoeffY m i) =
      jacobiY m q r
    exact (congrFun
      (jacobiY_eq_weightedBodyCoefficientSum m q hm0 hm1 hm2) r).symm

theorem jacobiPairCoeff01_dot (m : Fin 3 → ℝ) (w : Fin 2 → ℝ) :
    jacobiCoeffDot (jacobiPairCoeff01 m) w =
      (Real.sqrt (jacobiMu m))⁻¹ * w 0 := by
  simp [jacobiCoeffDot, jacobiPairCoeff01]

theorem jacobiPairCoeff02_dot (m : Fin 3 → ℝ) (w : Fin 2 → ℝ) :
    jacobiCoeffDot (jacobiPairCoeff02 m) w =
      (m 1 / jacobiPairMass m) * (Real.sqrt (jacobiMu m))⁻¹ * w 0 +
        (Real.sqrt (jacobiNu m))⁻¹ * w 1 := by
  simp [jacobiCoeffDot, jacobiPairCoeff02]

/-- The coefficient vector of the first pair reconstructs its physical
    displacement from the mass-normalized Jacobi columns. -/
theorem jacobiPairCoeff01_reconstructs
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) :
    jacobiPairCoeff01 m 0 • jacobiX m q +
        jacobiPairCoeff01 m 1 • jacobiY m q = q 1 - q 0 := by
  have hc0 : jacobiPairCoeff01 m 0 = (Real.sqrt (jacobiMu m))⁻¹ := by
    simp [jacobiPairCoeff01]
  have hc1 : jacobiPairCoeff01 m 1 = 0 := by
    simp [jacobiPairCoeff01]
  rw [hc0, hc1, zero_smul, add_zero]
  exact jacobiX_unscale m q hm0 hm1

/-- The coefficient vector of the second independent pair reconstructs its
    physical displacement from the two Jacobi columns. -/
theorem jacobiPairCoeff02_reconstructs
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiPairCoeff02 m 0 • jacobiX m q +
        jacobiPairCoeff02 m 1 • jacobiY m q = q 2 - q 0 := by
  have hX := jacobiX_unscale m q hm0 hm1
  have hY := jacobiY_unscale m q hm0 hm1 hm2
  have hc0 : jacobiPairCoeff02 m 0 =
      (m 1 / jacobiPairMass m) * (Real.sqrt (jacobiMu m))⁻¹ := by
    simp [jacobiPairCoeff02]
  have hc1 : jacobiPairCoeff02 m 1 = (Real.sqrt (jacobiNu m))⁻¹ := by
    simp [jacobiPairCoeff02]
  have hdecomp := jacobi_pairDistance02_decomposition m q hm0 hm1
  rw [hc0, hc1, ← smul_smul, hX, hY]
  rw [hdecomp]
  abel

theorem jacobiPairCoeff12_reconstructs
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    jacobiPairCoeff12 m 0 • jacobiX m q +
        jacobiPairCoeff12 m 1 • jacobiY m q = q 2 - q 1 := by
  calc
    _ = (jacobiPairCoeff02 m 0 • jacobiX m q +
          jacobiPairCoeff02 m 1 • jacobiY m q) -
        (jacobiPairCoeff01 m 0 • jacobiX m q +
          jacobiPairCoeff01 m 1 • jacobiY m q) := by
        simp [jacobiPairCoeff12]
        module
    _ = (q 2 - q 0) - (q 1 - q 0) := by
        rw [jacobiPairCoeff02_reconstructs m q hm0 hm1 hm2,
          jacobiPairCoeff01_reconstructs m q hm0 hm1]
    _ = q 2 - q 1 := by abel

/-- The pair directions `q₁-q₀` and `q₂-q₀` are linearly independent in
    mass-normalized Jacobi coordinates. -/
theorem jacobiPairCoeff_det_pos
    (m : Fin 3 → ℝ) (hm0 : 0 < m 0) (hm1 : 0 < m 1)
    (hm2 : 0 < m 2) :
    0 < jacobiPairCoeff01 m 0 * jacobiPairCoeff02 m 1 -
      jacobiPairCoeff01 m 1 * jacobiPairCoeff02 m 0 := by
  have hμ := sqrt_jacobiMu_pos m hm0 hm1
  have hν := sqrt_jacobiNu_pos m hm0 hm1 hm2
  simp [jacobiPairCoeff01, jacobiPairCoeff02]
  positivity

/-- The two independent Jacobi pair directions detect every nonzero vector.
    This is the algebraic core of strict positivity of the pair-force
    quadratic form. -/
theorem exists_jacobiPairCoeff_dot_ne_zero
    (m : Fin 3 → ℝ) (hm0 : 0 < m 0) (hm1 : 0 < m 1)
    (hm2 : 0 < m 2) (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    jacobiCoeffDot (jacobiPairCoeff01 m) w ≠ 0 ∨
      jacobiCoeffDot (jacobiPairCoeff02 m) w ≠ 0 := by
  have hμ := sqrt_jacobiMu_pos m hm0 hm1
  have hν := sqrt_jacobiNu_pos m hm0 hm1 hm2
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro hw1
      apply hw
      funext k
      fin_cases k
      · exact hw0
      · exact hw1
    right
    rw [jacobiPairCoeff02_dot, hw0]
    simp only [mul_zero, zero_add]
    exact mul_ne_zero (inv_ne_zero hν.ne') hw1
  · left
    rw [jacobiPairCoeff01_dot]
    exact mul_ne_zero (inv_ne_zero hμ.ne') hw0

/-- The positive quadratic form contributed by the three pair forces in
    Jacobi coordinates. Distances are explicit positive parameters, so the
    lemma is independent of a trajectory. -/
def jacobiPairForceQuadratic (G : ℝ) (m : Fin 3 → ℝ)
    (d01 d02 d12 : ℝ) (w : Fin 2 → ℝ) : ℝ :=
  G * ((m 0 * m 1 / d01 ^ 3) *
      (jacobiCoeffDot (jacobiPairCoeff01 m) w) ^ 2 +
    (m 0 * m 2 / d02 ^ 3) *
      (jacobiCoeffDot (jacobiPairCoeff02 m) w) ^ 2 +
    (m 1 * m 2 / d12 ^ 3) *
      (jacobiCoeffDot (jacobiPairCoeff12 m) w) ^ 2)

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29, Section
    "Newton's equations as a matrix equation", `eq:Kpositive`.
    Project-derived proof of strict positivity after the two independent
    coefficient directions have been checked against `eq:di`. -/
theorem jacobiPairForceQuadratic_pos
    (G : ℝ) (m : Fin 3 → ℝ) (d01 d02 d12 : ℝ)
    (hG : 0 < G) (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hd01 : 0 < d01) (hd02 : 0 < d02) (hd12 : 0 < d12)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    0 < jacobiPairForceQuadratic G m d01 d02 d12 w := by
  have hμ := sqrt_jacobiMu_pos m hm0 hm1
  have hν := sqrt_jacobiNu_pos m hm0 hm1 hm2
  unfold jacobiPairForceQuadratic
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro hw1
      apply hw
      funext k
      fin_cases k
      · exact hw0
      · exact hw1
    have hdot : jacobiCoeffDot (jacobiPairCoeff02 m) w ≠ 0 := by
      rw [jacobiPairCoeff02_dot, hw0]
      simp only [mul_zero, zero_add]
      exact mul_ne_zero (inv_ne_zero hν.ne') hw1
    positivity
  · have hdot : jacobiCoeffDot (jacobiPairCoeff01 m) w ≠ 0 := by
      rw [jacobiPairCoeff01_dot]
      exact mul_ne_zero (inv_ne_zero hμ.ne') hw0
    positivity


end

end DroppingThreeBodies
