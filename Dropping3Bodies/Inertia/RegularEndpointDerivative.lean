module

public import Dropping3Bodies.Inertia.CenterOfMassMoment
public import Dropping3Bodies.Support.IntervalEndpoint

@[expose] public section

/-!
# Moment derivative at a regular first syzygy

The Riccati matrix is used only strictly before the collinear endpoint. The
endpoint estimate will be obtained from continuous moment rates and a fixed
interior Riccati matrix. This follows the orientation, mass-normalized Jacobi
matrix, and trace conventions of `Inertia/JacobiRiccati.lean`.
-/

namespace DroppingThreeBodies

noncomputable section

/-- At an at-rest time, the logarithmic derivative in Jacobi coordinates
vanishes. -/
theorem generalNewton_jacobiRiccatiMatrixCurve_eq_zero_at_rest
    {m : Fin 3 → ℝ} {z : ℝ → Phase} {a : ℝ}
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : signedDoubleArea (z a).1 ≠ 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    jacobiRiccatiMatrixCurve m z a = 0 := by
  have hvel : (fun i => (z a).2 i) = fun _ => (0 : Point) := by
    funext i
    exact hrest i
  have hV0 : jacobiMatrix m (fun i => (z a).2 i) = 0 := by
    rw [hvel]
    ext r c
    simp [jacobiMatrix, jacobiX, jacobiY, jacobiPairCenter]
  have hdet : (jacobiMatrix m (z a).1).det ≠ 0 := by
    rw [jacobiMatrix_det_eq_sqrtMass_mul_area m (z a).1 hm0 hm1]
    exact mul_ne_zero
      (mul_ne_zero (sqrt_jacobiMu_pos m hm0 hm1).ne'
        (sqrt_jacobiNu_pos m hm0 hm1 hm2).ne') harea
  change (jacobiMatrix m (z a).1)⁻¹ * jacobiMatrix m (fun i => (z a).2 i) = 0
  rw [hV0]
  simp

/-- From initial rest, the Riccati quadratic form at any later regular
positive-area time is strictly negative in every nonzero fixed direction. -/
theorem generalNewton_jacobiRiccatiQuadratic_neg_of_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : a < t) (hIcc : Set.Icc a t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1)
    (hrest : ∀ i, (z a).2 i = 0) (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    matrixQuadratic (jacobiRiccatiMatrixCurve m z t) w < 0 := by
  have hanti := generalNewton_jacobiRiccatiQuadratic_strictAntiOn_Icc
    hsol hconn ha hIcc hm0 hm1 hm2 hG harea hrest w hw
  have hzero := generalNewton_jacobiRiccatiMatrixCurve_eq_zero_at_rest
    hm0 hm1 hm2 (ne_of_gt (harea a ⟨le_rfl, le_of_lt ht⟩)) hrest
  have h := hanti ⟨le_rfl, le_of_lt ht⟩ ⟨le_of_lt ht, le_rfl⟩ ht
  simpa [hzero, matrixQuadratic] using h

/-- After an interior time, every fixed Riccati quadratic form is
nonincreasing up to any later pre-syzygy time. The vector may vary between
applications; this pointwise form is useful for the rows of the Jacobi matrix. -/
theorem generalNewton_jacobiRiccatiQuadratic_le_of_preEndpoint
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t₀ t : ℝ} (ha : a ∈ I) (hat₀ : a ≤ t₀) (ht₀t : t₀ ≤ t)
    (hIcc : Set.Icc a t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1)
    (hrest : ∀ i, (z a).2 i = 0) (w : Fin 2 → ℝ) :
    matrixQuadratic (jacobiRiccatiMatrixCurve m z t) w ≤
      matrixQuadratic (jacobiRiccatiMatrixCurve m z t₀) w := by
  by_cases hw : w = 0
  · simp [hw, matrixQuadratic]
  · have hIcc' : Set.Icc t₀ t ⊆ I := by
      intro s hs
      exact hIcc ⟨le_trans hat₀ hs.1, hs.2⟩
    have harea' : ∀ s ∈ Set.Icc t₀ t, 0 < signedDoubleArea (z s).1 := by
      intro s hs
      exact harea s ⟨le_trans hat₀ hs.1, hs.2⟩
    by_cases hEq : t₀ = t
    · simp [hEq]
    · have hlt : t₀ < t := lt_of_le_of_ne ht₀t hEq
      have hanti := generalNewton_jacobiRiccatiQuadratic_strictAntiOn_Icc
        hsol hconn ha hIcc' hm0 hm1 hm2 hG harea' hrest w hw
      exact le_of_lt (hanti ⟨le_rfl, le_of_lt hlt⟩
        ⟨le_of_lt hlt, le_rfl⟩ hlt)

/-- At a collision-free endpoint the Jacobi matrix is nonzero, even if it is
singular because the endpoint is collinear: its first column records the
nonzero displacement of bodies 0 and 1. -/
theorem jacobiMatrix_ne_zero_of_collisionFree
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1)
    (hcf : CollisionFree q) : jacobiMatrix m q ≠ 0 := by
  have hq01 : q 1 - q 0 ≠ 0 := sub_ne_zero.mpr (hcf 1 0 (by decide))
  have hx : jacobiX m q ≠ 0 := by
    simp [jacobiX, (sqrt_jacobiMu_pos m hm0 hm1).ne', hq01]
  intro hQ
  have hx0 : jacobiMatrix m q 0 0 = 0 := by rw [hQ]; simp
  have hx1 : jacobiMatrix m q 1 0 = 0 := by rw [hQ]; simp
  have : jacobiX m q = 0 := by
    ext k
    fin_cases k
    · simpa [jacobiMatrix] using hx0
    · simpa [jacobiMatrix] using hx1
  exact hx this

/-- At a positive-area interior time, the Jacobi moment rate is twice the sum
of the two Riccati quadratic forms evaluated on the rows of the Jacobi
position matrix. -/
theorem generalNewton_jacobiMomentCurve_deriv_eq_rowQuadraticSum
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : a < t) (hIcc : Set.Icc a t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) t =
      2 * ∑ i : Fin 2, matrixQuadratic (jacobiRiccatiMatrixCurve m z t)
        (fun j => jacobiMatrix m (fun i => (z t).1 i) i j) := by
  have hareaT := harea t ⟨le_of_lt ht, le_rfl⟩
  let Q := jacobiMatrix m (fun i => (z t).1 i)
  let V := jacobiMatrix m (fun i => (z t).2 i)
  let C := jacobiRiccatiMatrixCurve m z t
  have hCsym := generalNewton_jacobiRiccatiMatrix_symmetric
    hsol hconn ha (hIcc ⟨le_of_lt ht, le_rfl⟩) hm0 hm1 hm2 hareaT hrest
  have hdetpos := jacobiMatrix_det_pos_of_positive_area m (z t).1
    hm0 hm1 hm2 hareaT
  have hdet : Q.det ≠ 0 := ne_of_gt (by simpa [Q] using hdetpos)
  have hVeq : V = Q * C := by
    dsimp [Q, V, C, jacobiRiccatiMatrixCurve]
    have hright := Matrix.mul_nonsing_inv
      (jacobiMatrix m (fun i => (z t).1 i)) (isUnit_iff_ne_zero.mpr hdet)
    calc
      jacobiMatrix m (fun i => (z t).2 i) =
          (jacobiMatrix m (fun i => (z t).1 i) *
            ((jacobiMatrix m (fun i => (z t).1 i))⁻¹)) *
              jacobiMatrix m (fun i => (z t).2 i) := by rw [hright]; simp
      _ = jacobiMatrix m (fun i => (z t).1 i) *
          (((jacobiMatrix m (fun i => (z t).1 i))⁻¹) *
            jacobiMatrix m (fun i => (z t).2 i)) := by rw [Matrix.mul_assoc]
  have hpair := matrixFrobeniusPairing_eq_rowQuadraticSum Q C V hVeq hCsym
  have hderiv := generalNewton_jacobiMomentCurve_deriv hsol
    (hIcc ⟨le_of_lt ht, le_rfl⟩) hm0 hm1 hm2
  rw [hderiv.deriv, hpair]

/-- The derivative before the endpoint is bounded above by the fixed
interior Riccati form applied to the current Jacobi rows. This is the
pointwise estimate whose right-hand side remains defined at a singular
collinear endpoint. -/
theorem generalNewton_jacobiMomentCurve_deriv_le_fixedRiccatiRows
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t₀ t : ℝ} (ha : a ∈ I) (hat₀ : a ≤ t₀) (ht₀ : t₀ < t)
    (hIcc : Set.Icc a t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) t ≤
      2 * ∑ i : Fin 2, matrixQuadratic (jacobiRiccatiMatrixCurve m z t₀)
        (fun j => jacobiMatrix m (fun i => (z t).1 i) i j) := by
  have hIcc' : Set.Icc a t₀ ⊆ I := by
    intro s hs
    exact hIcc ⟨hs.1, le_trans hs.2 (le_of_lt ht₀)⟩
  have harea' : ∀ s ∈ Set.Icc a t₀, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact harea s ⟨hs.1, le_trans hs.2 (le_of_lt ht₀)⟩
  have hrows : ∀ i : Fin 2,
      matrixQuadratic (jacobiRiccatiMatrixCurve m z t)
        (fun j => jacobiMatrix m (fun k => (z t).1 k) i j) ≤
      matrixQuadratic (jacobiRiccatiMatrixCurve m z t₀)
        (fun j => jacobiMatrix m (fun k => (z t).1 k) i j) := by
    intro i
    exact generalNewton_jacobiRiccatiQuadratic_le_of_preEndpoint
      hsol hconn ha hat₀ (le_of_lt ht₀) hIcc
      hm0 hm1 hm2 hG harea hrest
      (fun j => jacobiMatrix m (fun k => (z t).1 k) i j)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2)))
    (fun i hi => hrows i)
  have hrateT := generalNewton_jacobiMomentCurve_deriv_eq_rowQuadraticSum
    hsol hconn ha (lt_of_le_of_lt hat₀ ht₀) hIcc
    hm0 hm1 hm2 harea hrest
  rw [hrateT]
  nlinarith

/-- If the endpoint Jacobi matrix is nonzero, the fixed negative definite
Riccati form has a strictly negative sum over its two rows. -/
theorem matrixQuadratic_rowSum_lt_zero_of_negDef
    (C : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hneg : ∀ w : Fin 2 → ℝ, w ≠ 0 → matrixQuadratic C w < 0)
    (hQ : Q ≠ 0) :
    ∑ i : Fin 2, matrixQuadratic C (fun j => Q i j) < 0 := by
  have hrow : (fun j => Q 0 j) ≠ 0 ∨ (fun j => Q 1 j) ≠ 0 := by
    by_contra hn
    have hnot0 : ¬ (fun j => Q 0 j) ≠ 0 := (not_or.mp hn).1
    have hnot1 : ¬ (fun j => Q 1 j) ≠ 0 := (not_or.mp hn).2
    have hz0 : (fun j => Q 0 j) = 0 := not_not.mp hnot0
    have hz1 : (fun j => Q 1 j) = 0 := not_not.mp hnot1
    apply hQ
    ext i j
    fin_cases i
    · exact congrFun hz0 j
    · exact congrFun hz1 j
  have hq0 : matrixQuadratic C (fun j => Q 0 j) ≤ 0 := by
    by_cases hz : (fun j => Q 0 j) = 0
    · simp [hz, matrixQuadratic]
    · exact le_of_lt (hneg _ hz)
  have hq1 : matrixQuadratic C (fun j => Q 1 j) ≤ 0 := by
    by_cases hz : (fun j => Q 1 j) = 0
    · simp [hz, matrixQuadratic]
    · exact le_of_lt (hneg _ hz)
  have hs : matrixQuadratic C (fun j => Q 0 j) < 0 ∨
      matrixQuadratic C (fun j => Q 1 j) < 0 := by
    rcases hrow with hrow | hrow
    · exact Or.inl (hneg _ hrow)
    · exact Or.inr (hneg _ hrow)
  simp [Fin.sum_univ_succ]
  rcases hs with hs | hs <;> linarith

/-- At a regular collinear endpoint, the Jacobi moment derivative is strictly
negative. The Riccati matrix is evaluated only at an interior time t₀; its
negative quadratic form bounds the continuous moment rate up to the endpoint.
This is project-derived from the Riccati inequality and the Jacobi trace
identity cited in `Inertia/JacobiRiccati.lean`. -/
theorem generalNewton_jacobiMomentCurve_deriv_neg_at_regular_syzygy
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t₀ T : ℝ} (ha : a ∈ I) (hat₀ : a < t₀) (ht₀T : t₀ < T)
    (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hareaPre : ∀ s ∈ Set.Ico a T, 0 < signedDoubleArea (z s).1)
    (_hareaT : signedDoubleArea (z T).1 = 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 := by
  let Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s => jacobiMatrix m (fun i => (z s).1 i)
  let V : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s => jacobiMatrix m (fun i => (z s).2 i)
  let C₀ : Matrix (Fin 2) (Fin 2) ℝ := jacobiRiccatiMatrixCurve m z t₀
  let rate : ℝ → ℝ := fun s =>
    2 * ∑ i : Fin 2, ∑ j : Fin 2, Q s i j * V s i j
  let bound : ℝ → ℝ := fun s =>
    2 * ∑ i : Fin 2, matrixQuadratic C₀ (fun j => Q s i j)
  let gap : ℝ → ℝ := fun s => rate s - bound s
  have ht₀Ico : t₀ ∈ Set.Ico a T := ⟨le_of_lt hat₀, ht₀T⟩
  have hIcc₀ : Set.Icc a t₀ ⊆ I := by
    intro s hs
    exact hIcc ⟨hs.1, le_trans hs.2 (le_of_lt ht₀T)⟩
  have harea₀ : ∀ s ∈ Set.Icc a t₀, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 ht₀T⟩
  have hC₀neg : ∀ w : Fin 2 → ℝ, w ≠ 0 → matrixQuadratic C₀ w < 0 := by
    intro w hw
    exact generalNewton_jacobiRiccatiQuadratic_neg_of_rest
      hsol hconn ha hat₀ hIcc₀ hm0 hm1 hm2 hG harea₀ hrest w hw
  have hQendpoint : Q T ≠ 0 := by
    apply jacobiMatrix_ne_zero_of_collisionFree m (z T).1 hm0 hm1
    exact (hsol.2 T (hIcc ⟨le_of_lt (lt_trans hat₀ ht₀T), le_rfl⟩)).1
  have hboundT : bound T < 0 := by
    dsimp [bound, C₀, Q]
    have hsum := matrixQuadratic_rowSum_lt_zero_of_negDef
      (jacobiRiccatiMatrixCurve m z t₀)
      (jacobiMatrix m (fun i => (z T).1 i)) hC₀neg hQendpoint
    nlinarith
  have hZcont : ContinuousOn z (Set.Icc t₀ T) := by
    intro s hs
    exact ((hsol.2 s (hIcc ⟨le_trans (le_of_lt hat₀) hs.1, hs.2⟩)).2).continuousAt.continuousWithinAt
  have hCenterField : Continuous (fun p : Phase =>
      jacobiPairCenter m (fun i => p.1 i)) := by
    unfold jacobiPairCenter
    fun_prop [jacobiPairMass]
  have hYField : Continuous (fun p : Phase =>
      jacobiY m (fun i => p.1 i)) := by
    unfold jacobiY
    have hq2 : Continuous (fun p : Phase => p.1 2) := by fun_prop
    have hdisp : Continuous (fun p : Phase =>
        p.1 2 - jacobiPairCenter m (fun i => p.1 i)) := by
      exact hq2.sub hCenterField
    exact (continuous_const_smul (Real.sqrt (jacobiNu m))).comp hdisp
  have hYVField : Continuous (fun p : Phase =>
      jacobiY m (fun i => p.2 i)) := by
    unfold jacobiY
    have hcenter : Continuous (fun p : Phase =>
        jacobiPairCenter m (fun i => p.2 i)) := by
      unfold jacobiPairCenter
      fun_prop [jacobiPairMass]
    have hq2 : Continuous (fun p : Phase => p.2 2) := by fun_prop
    exact (continuous_const_smul (Real.sqrt (jacobiNu m))).comp (hq2.sub hcenter)
  have hQfield : Continuous (fun p : Phase => jacobiMatrix m (fun i => p.1 i)) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro c
    fin_cases c
    · simp [jacobiMatrix]
      fun_prop [jacobiX]
    · simp [jacobiMatrix, jacobiY, jacobiPairCenter, jacobiPairMass]
      fun_prop
  have hVfield : Continuous (fun p : Phase => jacobiMatrix m (fun i => p.2 i)) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro c
    fin_cases c
    · simp [jacobiMatrix]
      fun_prop [jacobiX]
    · simp [jacobiMatrix, jacobiY, jacobiPairCenter, jacobiPairMass]
      fun_prop
  have hQcont : ContinuousOn Q (Set.Icc t₀ T) := by
    dsimp [Q]
    exact hQfield.continuousOn.comp hZcont (by intro s hs; exact Set.mem_univ (z s))
  have hVcont : ContinuousOn V (Set.Icc t₀ T) := by
    dsimp [V]
    exact hVfield.continuousOn.comp hZcont (by intro s hs; exact Set.mem_univ (z s))
  have hRateCont : ContinuousOn rate (Set.Icc t₀ T) := by
    dsimp [rate]
    fun_prop
  have hBoundField : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      2 * ∑ i : Fin 2, matrixQuadratic C₀ (fun j => M i j)) := by
    simp only [matrixQuadratic, Fin.sum_univ_succ]
    fun_prop
  have hBoundCont : ContinuousOn bound (Set.Icc t₀ T) := by
    have hmaps : Set.MapsTo Q (Set.Icc t₀ T) Set.univ := by
      intro s hs
      exact Set.mem_univ (Q s)
    have hcomp := hBoundField.continuousOn.comp hQcont hmaps
    change ContinuousOn (fun s => 2 * ∑ i : Fin 2,
      matrixQuadratic C₀ (fun j => Q s i j)) (Set.Icc t₀ T)
    exact hcomp
  have hGapCont : ContinuousOn gap (Set.Icc t₀ T) := by
    dsimp [gap]
    exact hRateCont.sub hBoundCont
  have hRateDeriv : ∀ s ∈ Set.Icc t₀ T,
      deriv (fun u => jacobiMomentCurve m (fun i τ => (z τ).1 i) u) s = rate s := by
    intro s hs
    have h := generalNewton_jacobiMomentCurve_deriv hsol
      (hIcc ⟨le_trans (le_of_lt hat₀) hs.1, hs.2⟩) hm0 hm1 hm2
    simpa [rate, Q, V] using h.deriv
  have hgapNonpos : ∀ s ∈ Set.Ico t₀ T, gap s ≤ 0 := by
    intro s hs
    by_cases hst : s = t₀
    · subst s
      have hrate := hRateDeriv t₀ ⟨le_rfl, le_of_lt ht₀T⟩
      have hrow := generalNewton_jacobiMomentCurve_deriv_eq_rowQuadraticSum
        hsol hconn ha hat₀ hIcc₀ hm0 hm1 hm2 harea₀ hrest
      have heq : rate t₀ = bound t₀ := by
        calc
          rate t₀ = deriv (fun u => jacobiMomentCurve m
              (fun i τ => (z τ).1 i) u) t₀ := hrate.symm
          _ = 2 * ∑ i : Fin 2, matrixQuadratic C₀
              (fun j => jacobiMatrix m (fun i => (z t₀).1 i) i j) := hrow
          _ = bound t₀ := by simp [bound, C₀, Q]
      dsimp [gap]
      rw [heq]
      simp
    · have ht₀s : t₀ < s := lt_of_le_of_ne hs.1 (Ne.symm hst)
      have hIccs : Set.Icc a s ⊆ I := by
        intro r hr
        exact hIcc ⟨hr.1, le_trans hr.2 (le_of_lt hs.2)⟩
      have hareas : ∀ r ∈ Set.Icc a s, 0 < signedDoubleArea (z r).1 := by
        intro r hr
        exact hareaPre r ⟨hr.1, lt_of_le_of_lt hr.2 hs.2⟩
      have hbound := generalNewton_jacobiMomentCurve_deriv_le_fixedRiccatiRows
        hsol hconn ha (le_of_lt hat₀) ht₀s hIccs hm0 hm1 hm2 hG hareas hrest
      have hrate := hRateDeriv s ⟨le_of_lt ht₀s, le_of_lt hs.2⟩
      dsimp [gap]
      rw [← hrate]
      simpa [bound, Q, C₀] using hbound
  have hgapT : gap T ≤ 0 :=
    continuousOn_nonpos_right_of_nonpos_Ico ht₀T hGapCont hgapNonpos
  have hrateAtT : deriv (fun s => jacobiMomentCurve m
      (fun i τ => (z τ).1 i) s) T = rate T :=
    hRateDeriv T ⟨le_of_lt ht₀T, le_rfl⟩
  have hgap : rate T - bound T ≤ 0 := by simpa [gap] using hgapT
  linarith

/-- Exact negative Jacobi-moment derivative at a regular first syzygy in
either orientation. Negative-area data are reflected; the pair moment's
reflection invariance identifies the Jacobi-moment curves and hence their
derivatives. -/
theorem generalNewton_jacobiMomentCurve_deriv_neg_at_regular_syzygy_eitherOrientation
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t₀ T : ℝ} (ha : a ∈ I) (hat₀ : a < t₀) (ht₀T : t₀ < T)
    (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hareaSign : (∀ s ∈ Set.Ico a T, 0 < signedDoubleArea (z s).1) ∨
      (∀ s ∈ Set.Ico a T, signedDoubleArea (z s).1 < 0))
    (hareaT : signedDoubleArea (z T).1 = 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 := by
  rcases hareaSign with hpos | hneg
  · exact generalNewton_jacobiMomentCurve_deriv_neg_at_regular_syzygy
      hsol hconn ha hat₀ ht₀T hIcc hm0 hm1 hm2 hG hpos hareaT hrest
  · let zR : ℝ → Phase := fun s => reflectGeneralPhase (z s)
    have hsolR : GeneralClassicalNewtonSolution G m zR I := by
      simpa [zR] using generalClassicalNewtonSolution_reflect hsol
    have hrestR : ∀ i, (zR a).2 i = 0 := by
      intro i
      simpa [zR, reflectGeneralPhase, reflectConfiguration] using
        congrArg reflectPoint (hrest i)
    have hareaR : ∀ s ∈ Set.Ico a T,
        0 < signedDoubleArea (zR s).1 := by
      intro s hs
      rw [show (zR s).1 = reflectConfiguration (z s).1 by rfl,
        signedDoubleArea_reflectConfiguration]
      exact neg_pos.mpr (hneg s hs)
    have hderivR := generalNewton_jacobiMomentCurve_deriv_neg_at_regular_syzygy
      hsolR hconn ha hat₀ ht₀T hIcc hm0 hm1 hm2 hG hareaR (by
        rw [show (zR T).1 = reflectConfiguration (z T).1 by rfl,
          signedDoubleArea_reflectConfiguration, hareaT]
        norm_num) hrestR
    have hM : totalMass m ≠ 0 := ne_of_gt (totalMass_pos_of_positive m hm0 hm1 hm2)
    have hcurve : jacobiMomentCurve m (fun i s => (zR s).1 i) =
        jacobiMomentCurve m (fun i s => (z s).1 i) := by
      funext s
      apply mul_left_cancel₀ hM
      have hpair := pairMomentCurve_reflectGeneralPhase m z s
      change pairMoment m (fun i => (zR s).1 i) =
        pairMoment m (fun i => (z s).1 i) at hpair
      change totalMass m * jacobiMoment m (fun i => (zR s).1 i) =
        totalMass m * jacobiMoment m (fun i => (z s).1 i)
      rw [← pairMoment_eq_totalMass_mul_jacobiMoment m
        (fun i => (zR s).1 i) hm0 hm1 hm2,
        ← pairMoment_eq_totalMass_mul_jacobiMoment m
        (fun i => (z s).1 i) hm0 hm1 hm2]
      exact hpair
    have hderivCurve := congrArg (fun f : ℝ → ℝ => deriv f T) hcurve
    calc
      deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) T =
          deriv (fun s => jacobiMomentCurve m (fun i τ => (zR τ).1 i) s) T :=
        hderivCurve.symm
      _ < 0 := hderivR

/-- The physical center-of-mass moment has the same exact negative derivative
at a regular first syzygy, since it equals the Jacobi moment at every time. -/
theorem generalNewton_centerOfMassMomentCurve_deriv_neg_at_regular_syzygy
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t₀ T : ℝ} (ha : a ∈ I) (hat₀ : a < t₀) (ht₀T : t₀ < T)
    (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hareaSign : (∀ s ∈ Set.Ico a T, 0 < signedDoubleArea (z s).1) ∨
      (∀ s ∈ Set.Ico a T, signedDoubleArea (z s).1 < 0))
    (hareaT : signedDoubleArea (z T).1 = 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 := by
  have hcurve : (fun s => centerOfMassMomentCurve m
      (fun i τ => (z τ).1 i) s) =
      (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) := by
    funext s
    exact centerOfMassMomentCurve_eq_jacobiMomentCurve m
      (fun i τ => (z τ).1 i) hm0 hm1 hm2 s
  have hderivEq := congrArg (fun f : ℝ → ℝ => deriv f T) hcurve
  calc
    deriv (fun s => centerOfMassMomentCurve m
        (fun i τ => (z τ).1 i) s) T =
        deriv (fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s) T := hderivEq
    _ < 0 := generalNewton_jacobiMomentCurve_deriv_neg_at_regular_syzygy_eitherOrientation
      hsol hconn ha hat₀ ht₀T hIcc hm0 hm1 hm2 hG hareaSign hareaT hrest

/-- The exact Montgomery pair-moment derivative is also strictly negative at
the regular first syzygy. It is total mass times the Jacobi-moment derivative. -/
theorem generalNewton_pairMomentCurve_deriv_neg_at_regular_syzygy
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t₀ T : ℝ} (ha : a ∈ I) (hat₀ : a < t₀) (ht₀T : t₀ < T)
    (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hareaSign : (∀ s ∈ Set.Ico a T, 0 < signedDoubleArea (z s).1) ∨
      (∀ s ∈ Set.Ico a T, signedDoubleArea (z s).1 < 0))
    (hareaT : signedDoubleArea (z T).1 = 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 := by
  let J : ℝ → ℝ := fun s => jacobiMomentCurve m (fun i τ => (z τ).1 i) s
  let P : ℝ → ℝ := fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s
  have hcurve : P = fun s => totalMass m * J s := by
    funext s
    dsimp [P, J]
    rw [pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
        (fun i τ => (z τ).1 i) hm0 hm1 hm2 s,
      centerOfMassMomentCurve_eq_jacobiMomentCurve m
        (fun i τ => (z τ).1 i) hm0 hm1 hm2 s]
  have hJ := generalNewton_jacobiMomentCurve_deriv_neg_at_regular_syzygy_eitherOrientation
    hsol hconn ha hat₀ ht₀T hIcc hm0 hm1 hm2 hG hareaSign hareaT hrest
  have hJhas := generalNewton_jacobiMomentCurve_deriv hsol
    (hIcc ⟨le_of_lt (lt_trans hat₀ ht₀T), le_rfl⟩) hm0 hm1 hm2
  have hPHas : HasDerivAt P (totalMass m * deriv J T) T := by
    have hscaled := HasDerivAt.const_mul (totalMass m) hJhas
    rw [hJhas.deriv]
    exact hscaled.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hcurve s)
  have hM : 0 < totalMass m := totalMass_pos_of_positive m hm0 hm1 hm2
  have hJ' : deriv J T < 0 := by simpa [J] using hJ
  calc
    deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) T = deriv P T := rfl
    _ = totalMass m * deriv J T := hPHas.deriv
    _ < 0 := mul_neg_of_pos_of_neg hM hJ'

/-- The endpoint theorem needs no explicitly supplied interior time: the
midpoint lies strictly between the initial and endpoint times. -/
theorem generalNewton_pairMomentCurve_deriv_neg_at_regular_syzygy_of_nonempty_interval
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (ha : a ∈ I) (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hareaSign : (∀ s ∈ Set.Ico a T, 0 < signedDoubleArea (z s).1) ∨
      (∀ s ∈ Set.Ico a T, signedDoubleArea (z s).1 < 0))
    (hareaT : signedDoubleArea (z T).1 = 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 := by
  let t₀ := (a + T) / 2
  have hat₀ : a < t₀ := by dsimp [t₀]; linarith
  have ht₀T : t₀ < T := by dsimp [t₀]; linarith
  exact generalNewton_pairMomentCurve_deriv_neg_at_regular_syzygy
    hsol hconn ha hat₀ ht₀T hIcc hm0 hm1 hm2 hG hareaSign hareaT hrest

/-- No-explicit-interior-time version for the physical center-of-mass moment. -/
theorem generalNewton_centerOfMassMomentCurve_deriv_neg_at_regular_syzygy_of_nonempty_interval
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (ha : a ∈ I) (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hareaSign : (∀ s ∈ Set.Ico a T, 0 < signedDoubleArea (z s).1) ∨
      (∀ s ∈ Set.Ico a T, signedDoubleArea (z s).1 < 0))
    (hareaT : signedDoubleArea (z T).1 = 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s) T < 0 := by
  let t₀ := (a + T) / 2
  have hat₀ : a < t₀ := by dsimp [t₀]; linarith
  have ht₀T : t₀ < T := by dsimp [t₀]; linarith
  exact generalNewton_centerOfMassMomentCurve_deriv_neg_at_regular_syzygy
    hsol hconn ha hat₀ ht₀T hIcc hm0 hm1 hm2 hG hareaSign hareaT hrest


end

end DroppingThreeBodies
