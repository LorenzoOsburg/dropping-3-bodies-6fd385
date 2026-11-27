module

public import Dropping3Bodies.Inertia.CentralForceJacobi
public import Dropping3Bodies.Inertia.AbstractJacobiContraction
public import Dropping3Bodies.Inertia.AbstractJacobiArea
public import Mathlib.Analysis.Matrix.Normed
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-! Physical contraction and area theorems for arbitrary symmetric attractive
central pair forces, obtained by instantiating abstract Jacobi dynamics. -/

namespace DroppingThreeBodies.CentralForce

noncomputable section

open Filter
open scoped Matrix.Norms.Elementwise

variable {κ : Coefficients} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
  {a s t : ℝ}

private theorem inertia_curve_eq (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (z : ℝ → Phase) :
    AbstractJacobi.inertia (fun u => jacobiMatrix m (z u).1) =
      centerOfMassMomentCurve m (fun i u => (z u).1 i) := by
  funext u
  exact (jacobiMatrix_trace_mul_transpose_eq_jacobiMoment m (z u).1).trans
    (centerOfMassMoment_eq_jacobiMoment m (z u).1 (hm 0) (hm 1) (hm 2)).symm

private theorem det_ne_zero_iff (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (q : Fin 3 → Point) : (jacobiMatrix m q).det ≠ 0 ↔ signedDoubleArea q ≠ 0 := by
  rw [jacobiMatrix_det_eq_sqrtMass_mul_area m q (hm 0) (hm 1)]
  simp [(sqrt_jacobiMu_pos m (hm 0) (hm 1)).ne',
    (sqrt_jacobiNu_pos m (hm 0) (hm 1) (hm 2)).ne']

theorem centeredSpatialMoment_hasDerivAt (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (ht : t ∈ I) :
    HasDerivAt (fun u => centeredSpatialMoment m (z u).1)
      (AbstractJacobi.spatialRate (fun u => jacobiMatrix m (z u).1)
        (fun u => jacobiMatrix m (z u).2) t) t := by
  have hd := (jacobiSystem hsol hm).spatial_hasDerivAt ht
  have heq : (fun u => centeredSpatialMoment m (z u).1) =
      AbstractJacobi.spatial (fun u => jacobiMatrix m (z u).1) :=
    funext fun u => centeredSpatialMoment_eq_jacobiMatrix_mul_transpose m (z u).1 hm
  rw [heq]
  exact hd

/-- The tensor derivative is strictly negative in every nonzero spatial direction,
strictly after rest and before the first collinearity. -/
theorem centeredSpatialMoment_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    matrixQuadratic (deriv (fun u => centeredSpatialMoment m (z u).1) t) w < 0 := by
  have hd : deriv (fun u => centeredSpatialMoment m (z u).1) t =
      AbstractJacobi.spatialRate (fun u => jacobiMatrix m (z u).1)
        (fun u => jacobiMatrix m (z u).2) t := by
    simpa using! (centeredSpatialMoment_hasDerivAt hsol hm
      (ht.2.1 ⟨hat.le, le_rfl⟩)).deriv
  rw [hd]
  apply (jacobiSystem hsol hm).spatialRate_neg (jacobiSystem_positiveForce hsol hm hκ)
    hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
  · simpa only [initialBranch_eq m hm z I a] using ht
  · exact hat
  · exact hw

theorem centeredSpatialMoment_deriv_symmetric (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (ht : t ∈ I) :
    (deriv (fun u => centeredSpatialMoment m (z u).1) t).transpose =
      deriv (fun u => centeredSpatialMoment m (z u).1) t := by
  have hd : deriv (fun u => centeredSpatialMoment m (z u).1) t =
      AbstractJacobi.spatialRate (fun u => jacobiMatrix m (z u).1)
        (fun u => jacobiMatrix m (z u).2) t := by
    simpa using! (centeredSpatialMoment_hasDerivAt hsol hm ht).deriv
  rw [hd]
  simp [AbstractJacobi.spatialRate, Matrix.transpose_add, Matrix.transpose_mul, add_comm]

theorem centerOfMassMomentCurve_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) t < 0 := by
  have hn := (jacobiSystem hsol hm).inertia_deriv_neg (jacobiSystem_positiveForce hsol hm hκ)
    hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
    (show t ∈ AbstractJacobi.initialBranch (fun u => jacobiMatrix m (z u).1) I a by
      simpa only [initialBranch_eq m hm z I a] using ht) hat
  rwa [inertia_curve_eq m hm z] at hn

theorem centerOfMassMomentCurve_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (centerOfMassMomentCurve m (fun i u => (z u).1 i))
      (BeforeFirstCollinearity z I a) := by
  have hn := (jacobiSystem hsol hm).inertia_strictAntiOn_initialBranch
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
  rwa [inertia_curve_eq m hm z, initialBranch_eq m hm z I a] at hn

/-- The positive conversion factor from signed double area to the Jacobi determinant. -/
def areaScale (m : Fin 3 → ℝ) : ℝ := Real.sqrt (jacobiMu m) * Real.sqrt (jacobiNu m)

theorem areaScale_pos (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i) : 0 < areaScale m :=
  mul_pos (sqrt_jacobiMu_pos m (hm 0) (hm 1))
    (sqrt_jacobiNu_pos m (hm 0) (hm 1) (hm 2))

theorem abs_det_eq_areaScale_mul_absArea (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (q : Fin 3 → Point) :
    |(jacobiMatrix m q).det| = areaScale m * |signedDoubleArea q| := by
  rw [jacobiMatrix_det_eq_sqrtMass_mul_area m q (hm 0) (hm 1)]
  change |areaScale m * signedDoubleArea q| = _
  rw [abs_mul, abs_of_pos (areaScale_pos m hm)]

theorem sqrt_abs_det_eq (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (q : Fin 3 → Point) :
    Real.sqrt |(jacobiMatrix m q).det| =
      Real.sqrt (areaScale m) * Real.sqrt |signedDoubleArea q| := by
  rw [abs_det_eq_areaScale_mul_absArea m hm q, Real.sqrt_mul (areaScale_pos m hm).le]

/-- Explicit strict curvature at any noncollinear time in the connected solution
interval, including the release time. This uses the second-derivative identity,
rather than inferring curvature from strict concavity. -/
theorem sqrtAbsArea_second_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    deriv (deriv (fun u => Real.sqrt |signedDoubleArea (z u).1|)) t < 0 := by
  have hh := (jacobiSystem hsol hm).sqrtAbsDet_second_deriv_neg
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha ht
    (jacobi_velocity_zero_of_rest m z a hrest)
    ((det_ne_zero_iff m hm (z t).1).mpr harea)
  have heq : (fun u => Real.sqrt |(jacobiMatrix m (z u).1).det|) =
      (fun u => Real.sqrt (areaScale m) * Real.sqrt |signedDoubleArea (z u).1|) :=
    funext fun u => sqrt_abs_det_eq m hm (z u).1
  rw [heq, deriv_const_mul_field', deriv_const_mul_field] at hh
  have hk := Real.sqrt_pos.2 (areaScale_pos m hm)
  nlinarith

theorem signedDoubleArea_hasDerivAt (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (ht : t ∈ I) (harea : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (fun u => signedDoubleArea (z u).1)
      (signedDoubleArea (z t).1 * Matrix.trace (jacobiRiccatiMatrixCurve m z t)) t := by
  have hk := (areaScale_pos m hm).ne'
  have hd := ((jacobiSystem hsol hm).det_hasDerivAt ht
    ((det_ne_zero_iff m hm (z t).1).mpr harea)).const_mul (areaScale m)⁻¹
  have heq : (fun u => signedDoubleArea (z u).1) =ᶠ[nhds t]
      (fun u => (areaScale m)⁻¹ * (jacobiMatrix m (z u).1).det) := by
    filter_upwards [] with u
    rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z u).1 (hm 0) (hm 1)]
    change _ = (areaScale m)⁻¹ * (areaScale m * _)
    simp [hk]
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z t).1 (hm 0) (hm 1)]
  change (areaScale m)⁻¹ * (areaScale m * _ * _) = _
  field_simp
  rfl

private theorem orientedDet_eq (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (z : ℝ → Phase) (a t : ℝ) :
    AbstractJacobi.orientedDet (fun u => jacobiMatrix m (z u).1) a t =
      areaScale m * orientedArea z a t := by
  have hs : (jacobiMatrix m (z a).1).det < 0 ↔ signedDoubleArea (z a).1 < 0 := by
    rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z a).1 (hm 0) (hm 1)]
    change areaScale m * signedDoubleArea (z a).1 < 0 ↔ _
    simpa only [mul_zero] using
      (mul_lt_mul_iff_right₀ (b := signedDoubleArea (z a).1) (c := (0 : ℝ))
        (areaScale_pos m hm))
  simp only [AbstractJacobi.orientedDet, hs, orientedArea]
  rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z t).1 (hm 0) (hm 1)]
  split <;> simp [areaScale]

/-- The positively oriented double area has strictly negative time derivative
at every time strictly after release on the initial noncollinear branch. -/
theorem orientedArea_deriv_neg
    (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i)
    (hκ : κ.Positive)
    (hconn : IsPreconnected I)
    (ha : a ∈ I)
    (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a)
    (hat : a < t) :
    deriv (fun u => orientedArea z a u) t < 0 := by
  have hsys := jacobiSystem hsol hm
  have hbranch : t ∈ AbstractJacobi.initialBranch (fun u => jacobiMatrix m (z u).1) I a := by
    rw [initialBranch_eq m hm z I a]
    exact ht
  have htrace := hsys.riccati_trace_neg_of_rest (jacobiSystem_positiveForce hsol hm hκ)
    hconn ha (jacobi_velocity_zero_of_rest m z a hrest) hbranch hat
  have hscaled : 0 < areaScale m * orientedArea z a t := by
    rw [← orientedDet_eq m hm z a t, hsys.orientedDet_eq_abs hbranch]
    exact abs_pos.mpr (hbranch.2.2 t ⟨hat.le, le_rfl⟩)
  have hpos := pos_of_mul_pos_right hscaled (areaScale_pos m hm).le
  have hd := signedDoubleArea_hasDerivAt hsol hm
    (ht.2.1 ⟨hat.le, le_rfl⟩) (ht.2.2 t ⟨hat.le, le_rfl⟩)
  have horiented : HasDerivAt (fun u => orientedArea z a u)
      (orientedArea z a t * Matrix.trace (jacobiRiccatiMatrixCurve m z t)) t := by
    by_cases hsign : signedDoubleArea (z a).1 < 0
    · simpa only [orientedArea, ite_eq_left hsign, neg_mul] using hd.fun_neg
    · simpa only [orientedArea, ite_eq_right hsign] using hd
  rw [horiented.deriv]
  exact mul_neg_of_pos_of_neg hpos htrace

theorem orientedArea_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (orientedArea z a) (BeforeFirstCollinearity z I a) := by
  have hh := (jacobiSystem hsol hm).orientedDet_strictAntiOn_initialBranch
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
  rw [initialBranch_eq m hm z I a] at hh
  intro s hs t ht hst
  have hn := hh hs ht hst
  rw [orientedDet_eq m hm z a t, orientedDet_eq m hm z a s] at hn
  exact (mul_lt_mul_iff_right₀ (areaScale_pos m hm)).mp hn

private theorem strictConcaveOn_of_pos_scale {S : Set ℝ} {f : ℝ → ℝ} {k : ℝ}
    (hk : 0 < k) (hf : StrictConcaveOn ℝ S (fun u => k * f u)) :
    StrictConcaveOn ℝ S f := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hn := hf.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hn ⊢
  have heq : a * (k * f x) + b * (k * f y) = k * (a * f x + b * f y) := by ring
  rw [heq] at hn
  exact (mul_lt_mul_iff_right₀ hk).mp hn

theorem sqrtAbsArea_strictConcaveOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictConcaveOn ℝ (BeforeFirstCollinearity z I a)
      (fun u => Real.sqrt |signedDoubleArea (z u).1|) := by
  have hh := (jacobiSystem hsol hm).sqrtAbsDet_strictConcaveOn_initialBranch
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
  rw [initialBranch_eq m hm z I a] at hh
  have heq : (fun u => Real.sqrt |(jacobiMatrix m (z u).1).det|) =
      (fun u => Real.sqrt (areaScale m) * Real.sqrt |signedDoubleArea (z u).1|) :=
    funext fun u => sqrt_abs_det_eq m hm (z u).1
  rw [heq] at hh
  exact strictConcaveOn_of_pos_scale (Real.sqrt_pos.2 (areaScale_pos m hm)) hh

theorem sqrtAbsArea_tangent_bound (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (hs : s ∈ BeforeFirstCollinearity z I a) (ht : t ∈ BeforeFirstCollinearity z I a)
    (hst : s ≤ t) :
    Real.sqrt |signedDoubleArea (z t).1| ≤ Real.sqrt |signedDoubleArea (z s).1| +
      (t - s) * (Real.sqrt |signedDoubleArea (z s).1| *
        Matrix.trace (jacobiRiccatiMatrixCurve m z s) / 2) := by
  have hh := (jacobiSystem hsol hm).sqrtAbsDet_tangent_bound
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
    hst (fun u hu => ht.2.1 ⟨hs.1.trans hu.1, hu.2⟩)
    (fun u hu => (det_ne_zero_iff m hm (z u).1).mpr (ht.2.2 u ⟨hs.1.trans hu.1, hu.2⟩))
  simp only [sqrt_abs_det_eq m hm] at hh
  apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.2 (areaScale_pos m hm))).mp
  convert! hh using 1
  dsimp only [jacobiRiccatiMatrixCurve, AbstractJacobi.riccati]
  ring

theorem initialBranch_remainingTime_bound (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (hs : s ∈ BeforeFirstCollinearity z I a) (has : a < s)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hst : s ≤ t) :
    t < s + 2 / (-Matrix.trace (jacobiRiccatiMatrixCurve m z s)) := by
  apply (jacobiSystem hsol hm).initialBranch_remainingTime_bound
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
  · simpa only [initialBranch_eq m hm z I a] using hs
  · exact has
  · simpa only [initialBranch_eq m hm z I a] using ht
  · exact hst

theorem initialBranch_bddAbove (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    BddAbove (BeforeFirstCollinearity z I a) := by
  have hh := (jacobiSystem hsol hm).initialBranch_bddAbove
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
  rwa [initialBranch_eq m hm z I a] at hh

/-- The endpoint is regular as a classical solution, but need not be invertible.
No assertion of strict tensor negativity at a collinear endpoint is made. -/
theorem centerOfMassMomentCurve_deriv_neg_at_regular_endpoint (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) {T : ℝ} (haT : a < T)
    (hI : Set.Icc a T ⊆ I)
    (harea : ∀ u ∈ Set.Ico a T, signedDoubleArea (z u).1 ≠ 0) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) T < 0 := by
  have hh := (jacobiSystem hsol hm).inertia_deriv_neg_at_endpoint
    (jacobiSystem_positiveForce hsol hm hκ) hconn ha (jacobi_velocity_zero_of_rest m z a hrest)
    haT hI (fun u hu => (det_ne_zero_iff m hm (z u).1).mpr (harea u hu))
    (jacobiMatrix_ne_zero_of_collisionFree m (z T).1 (hm 0) (hm 1)
      (hsol.2 T (hI ⟨haT.le, le_rfl⟩)).1)
  rwa [inertia_curve_eq m hm z] at hh

end
end DroppingThreeBodies.CentralForce
