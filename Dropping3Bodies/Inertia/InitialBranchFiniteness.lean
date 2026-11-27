module

public import Dropping3Bodies.Inertia.AreaConcavity
public import Dropping3Bodies.Inertia.InitialBranchMonotonicity

@[expose] public section

/-!
# Finiteness of the initial noncollinear branch

No endpoint or finiteness assumption is used. The tangent line to the square
root of area at any later branch time gives an upper bound for every remaining
branch time. Reflection then removes the orientation restriction.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Positive initial area stays positive on the entire initial noncollinear
segment, including its endpoint. -/
theorem generalNewton_area_pos_on_initialBranch
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I)
    {a t : ℝ} (ht : t ∈ BeforeFirstCollinearity z I a)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (harea₀ : 0 < signedDoubleArea (z a).1) :
    ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1 := by
  rcases ht with ⟨hat, hIcc, hnonzero⟩
  intro s hs
  rcases lt_or_gt_of_ne (hnonzero s hs) with hneg | hpos
  · have hcont : ContinuousOn (fun r => signedDoubleArea (z r).1) (Set.Icc a s) := by
      intro r hr
      have hrt : r ∈ Set.Icc a t := ⟨hr.1, hr.2.trans hs.2⟩
      exact (generalNewton_signedDoubleArea_deriv hsol (hIcc hrt) hm0 hm1 hm2
        (hnonzero r hrt)).continuousAt.continuousWithinAt
    obtain ⟨r, hr, hzero⟩ := intermediate_value_Icc' hs.1 hcont
      (show (0 : ℝ) ∈ Set.Icc (signedDoubleArea (z s).1)
        (signedDoubleArea (z a).1) from ⟨hneg.le, harea₀.le⟩)
    exact False.elim (hnonzero r ⟨hr.1, hr.2.trans hs.2⟩ hzero)
  · exact hpos

/-- Negative definiteness of `C` from rest implies its trace is negative. -/
theorem generalNewton_jacobiRiccati_trace_neg_of_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a t : ℝ} (ha : a ∈ I) (ht : a < t) (hIcc : Set.Icc a t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    Matrix.trace (jacobiRiccatiMatrixCurve m z t) < 0 := by
  have hneg := generalNewton_jacobiRiccatiQuadratic_neg_of_rest
    hsol hconn ha ht hIcc hm0 hm1 hm2 hG harea hrest
  have h0 := hneg ![1, 0] (by intro h; have := congrFun h 0; norm_num at this)
  have h1 := hneg ![0, 1] (by intro h; have := congrFun h 1; norm_num at this)
  simp [matrixQuadratic, Fin.sum_univ_succ] at h0 h1
  simpa [Matrix.trace, Fin.sum_univ_succ] using add_neg h0 h1

/-- The tangent-line estimate for the square root of positive area. -/
theorem generalNewton_sqrtArea_tangent_bound
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a s t : ℝ} (ha : a ∈ I) (hst : s ≤ t) (hIcc : Set.Icc s t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea : ∀ x ∈ Set.Icc s t, 0 < signedDoubleArea (z x).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    Real.sqrt (signedDoubleArea (z t).1) ≤
      Real.sqrt (signedDoubleArea (z s).1) + (t - s) *
        (Real.sqrt (signedDoubleArea (z s).1) *
          Matrix.trace (jacobiRiccatiMatrixCurve m z s) / 2) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hconc := (generalNewton_sqrtArea_strictConcaveOn_Icc hsol hconn ha hIcc
    hm0 hm1 hm2 hG harea hrest).concaveOn
  have hs : s ∈ Set.Icc s t := ⟨le_rfl, hst.le⟩
  have ht : t ∈ Set.Icc s t := ⟨hst.le, le_rfl⟩
  have h := hconc.slope_le_of_hasDerivAt hs ht hst
    (generalNewton_sqrtArea_deriv hsol (hIcc hs) hm0 hm1 hm2 (harea s hs))
  rw [slope_def_field] at h
  have := (div_le_iff₀ (sub_pos.mpr hst)).mp h
  nlinarith

/-- Equation (3.7), expressed using `B'/B = tr C`: from any branch time
`s > a`, every later branch time is strictly below `s + 2 / (-tr C(s))`. -/
theorem generalNewton_initialBranch_remainingTime_bound
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a s t : ℝ} (hs : s ∈ BeforeFirstCollinearity z I a) (has : a < s)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hst : s ≤ t)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea₀ : 0 < signedDoubleArea (z a).1) (hrest : ∀ i, (z a).2 i = 0) :
    t < s + 2 / (-Matrix.trace (jacobiRiccatiMatrixCurve m z s)) := by
  have hareaS := generalNewton_area_pos_on_initialBranch hsol hs hm0 hm1 hm2 harea₀
  have hareaT := generalNewton_area_pos_on_initialBranch hsol ht hm0 hm1 hm2 harea₀
  have ha : a ∈ I := hs.2.1 ⟨le_rfl, has.le⟩
  have htr := generalNewton_jacobiRiccati_trace_neg_of_rest hsol hconn ha has
    hs.2.1 hm0 hm1 hm2 hG hareaS hrest
  have hIcc : Set.Icc s t ⊆ I := fun x hx => ht.2.1 ⟨has.le.trans hx.1, hx.2⟩
  have harea : ∀ x ∈ Set.Icc s t, 0 < signedDoubleArea (z x).1 :=
    fun x hx => hareaT x ⟨has.le.trans hx.1, hx.2⟩
  have htan := generalNewton_sqrtArea_tangent_bound hsol hconn ha hst hIcc
    hm0 hm1 hm2 hG harea hrest
  have hρs := Real.sqrt_pos.2 (hareaS s ⟨has.le, le_rfl⟩)
  have hρt := Real.sqrt_pos.2 (hareaT t ⟨ht.1, le_rfl⟩)
  have hremaining : 0 < Real.sqrt (signedDoubleArea (z s).1) *
      (2 - (t - s) * (-Matrix.trace (jacobiRiccatiMatrixCurve m z s))) := by
    nlinarith only [htan, hρt]
  have hprod : (t - s) * (-Matrix.trace (jacobiRiccatiMatrixCurve m z s)) < 2 := by
    have := (mul_pos_iff_of_pos_left hρs).mp hremaining
    linarith
  have := (lt_div_iff₀ (neg_pos.mpr htr)).mpr hprod
  linarith

/-- The positive-area initial noncollinear branch is bounded above, even
when no regular endpoint or first collinearity is assumed to exist. -/
theorem generalNewton_initialBranch_bddAbove_of_positive_area
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea₀ : 0 < signedDoubleArea (z a).1) (hrest : ∀ i, (z a).2 i = 0) :
    BddAbove (BeforeFirstCollinearity z I a) := by
  by_cases hex : ∃ s ∈ BeforeFirstCollinearity z I a, a < s
  · obtain ⟨s, hs, has⟩ := hex
    let T := s + 2 / (-Matrix.trace (jacobiRiccatiMatrixCurve m z s))
    have htr := generalNewton_jacobiRiccati_trace_neg_of_rest hsol hconn ha has
      hs.2.1 hm0 hm1 hm2 hG
      (generalNewton_area_pos_on_initialBranch hsol hs hm0 hm1 hm2 harea₀) hrest
    have hsT : s < T := lt_add_of_pos_right s (div_pos (by norm_num) (neg_pos.mpr htr))
    refine ⟨T, fun t ht => ?_⟩
    by_cases hst : s ≤ t
    · exact (generalNewton_initialBranch_remainingTime_bound hsol hconn hs has ht hst
        hm0 hm1 hm2 hG harea₀ hrest).le
    · exact (lt_trans (lt_of_not_ge hst) hsT).le
  · refine ⟨a, fun t ht => ?_⟩
    by_contra h
    exact hex ⟨t, ht, lt_of_not_ge h⟩

/-- Reflection preserves the set of initial noncollinear times. -/
theorem beforeFirstCollinearity_reflect (z : ℝ → Phase) (I : Set ℝ) (a : ℝ) :
    BeforeFirstCollinearity (fun t => reflectGeneralPhase (z t)) I a =
      BeforeFirstCollinearity z I a := by
  ext t
  simp [BeforeFirstCollinearity, reflectGeneralPhase, signedDoubleArea_reflectConfiguration]

/-- For arbitrary positive masses, positive gravity, initial rest, and
noncollinear starting positions, the initial noncollinear branch is bounded
above. Both orientations are allowed, with no assumption of finite lifetime. -/
theorem generalNewton_initialBranch_bddAbove
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea₀ : signedDoubleArea (z a).1 ≠ 0) (hrest : ∀ i, (z a).2 i = 0) :
    BddAbove (BeforeFirstCollinearity z I a) := by
  rcases lt_or_gt_of_ne harea₀ with hneg | hpos
  · have hsolR := generalClassicalNewtonSolution_reflect hsol
    have hposR : 0 < signedDoubleArea (reflectGeneralPhase (z a)).1 := by
      simpa [reflectGeneralPhase, signedDoubleArea_reflectConfiguration] using neg_pos.mpr hneg
    have hrestR : ∀ i, (reflectGeneralPhase (z a)).2 i = 0 := by
      intro i
      simp [reflectGeneralPhase, reflectConfiguration, hrest i, reflectPoint_zero]
    have h := generalNewton_initialBranch_bddAbove_of_positive_area hsolR hconn ha
      hm0 hm1 hm2 hG hposR hrestR
    rwa [beforeFirstCollinearity_reflect] at h
  · exact generalNewton_initialBranch_bddAbove_of_positive_area hsol hconn ha
      hm0 hm1 hm2 hG hpos hrest

end

end DroppingThreeBodies
