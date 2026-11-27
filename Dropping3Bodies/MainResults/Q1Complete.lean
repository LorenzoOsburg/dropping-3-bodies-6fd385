module

public import Dropping3Bodies.MainResults.Q1
public import Dropping3Bodies.Inertia.Virial
public import Dropping3Bodies.Inertia.RegularEndpointDerivative
public import Dropping3Bodies.Dynamics.GeneralReflectionSymmetry

@[expose] public section

/-! # Full classical-branch Q1 contract

This public adapter states the Q1 monotonicity and derivative signs on the
entire regular initial branch without assuming how that branch ends. It also
records both zero derivatives at the initial rest instant.
-/

namespace DroppingThreeBodies

noncomputable section

private theorem q1_pairAndCenter_deriv_neg_of_positiveArea
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I)
    (hconn : IsPreconnected I) {a t : ℝ}
    (ha : a ∈ I) (hat : a < t) (hIcc : Set.Icc a t ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) t < 0 ∧
    deriv (fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s) t < 0 := by
  let Q := jacobiMatrix m (fun i => (z t).1 i)
  let C := jacobiRiccatiMatrixCurve m z t
  have hCneg : ∀ w : Fin 2 → ℝ, w ≠ 0 → matrixQuadratic C w < 0 := by
    intro w hw
    exact generalNewton_jacobiRiccatiQuadratic_neg_of_rest hsol hconn
      ha hat hIcc hm0 hm1 hm2 hG harea hrest w hw
  have hdet : 0 < Q.det := by
    dsimp [Q]
    exact jacobiMatrix_det_pos_of_positive_area m (z t).1 hm0 hm1
      hm2 (harea t ⟨le_of_lt hat, le_rfl⟩)
  have hQne : Q ≠ 0 := by
    intro hzero
    have hdetzero : Q.det = 0 := by
      rw [hzero]
      exact Matrix.det_zero
    linarith
  have hrows := matrixQuadratic_rowSum_lt_zero_of_negDef C Q hCneg hQne
  have hrate := generalNewton_jacobiMomentCurve_deriv_eq_rowQuadraticSum
    hsol hconn ha hat hIcc hm0 hm1 hm2 harea hrest
  have hJneg : deriv (fun s => jacobiMomentCurve m
      (fun i τ => (z τ).1 i) s) t < 0 := by
    rw [hrate]
    dsimp [Q, C] at hrows
    nlinarith
  let J : ℝ → ℝ := fun s => jacobiMomentCurve m
    (fun i τ => (z τ).1 i) s
  let P : ℝ → ℝ := fun s => pairMomentCurve m
    (fun i τ => (z τ).1 i) s
  let M := totalMass m
  have hJhas := generalNewton_jacobiMomentCurve_deriv hsol
    (hIcc ⟨le_of_lt hat, le_rfl⟩) hm0 hm1 hm2
  have hPcurve : P = fun s => M * J s := by
    funext s
    dsimp [P, J, M]
    rw [pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
      (fun i τ => (z τ).1 i) hm0 hm1 hm2 s,
      centerOfMassMomentCurve_eq_jacobiMomentCurve m
        (fun i τ => (z τ).1 i) hm0 hm1 hm2 s]
  have hPhas : HasDerivAt P (M * deriv J t) t := by
    have hscaled := HasDerivAt.const_mul M hJhas
    rw [hJhas.deriv]
    exact hscaled.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hPcurve s)
  have hM : 0 < M := totalMass_pos_of_positive m hm0 hm1 hm2
  have hpair : deriv (fun s => pairMomentCurve m
      (fun i τ => (z τ).1 i) s) t < 0 := by
    change deriv P t < 0
    rw [hPhas.deriv]
    have hJ' : deriv J t < 0 := by simpa [J] using hJneg
    exact mul_neg_of_pos_of_neg hM hJ'
  have hcenterCurve : (fun s => centerOfMassMomentCurve m
      (fun i τ => (z τ).1 i) s) = J := by
    funext s
    exact centerOfMassMomentCurve_eq_jacobiMomentCurve m
      (fun i τ => (z τ).1 i) hm0 hm1 hm2 s
  have hderivEq := congrArg (fun f : ℝ → ℝ => deriv f t) hcenterCurve
  exact ⟨hpair, by rw [hderivEq]; exact hJneg⟩

private theorem q1_area_constantSign_on_Icc
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I)
    {a t : ℝ} (hat : a < t) (hIcc : Set.Icc a t ⊆ I)
    (hnonzero : ∀ s ∈ Set.Icc a t, signedDoubleArea (z s).1 ≠ 0) :
    (∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1) ∨
    (∀ s ∈ Set.Icc a t, signedDoubleArea (z s).1 < 0) := by
  have hpre := generalNewton_signedArea_hasConstantSign_before_endpoint
    hsol hat hIcc (fun s hs => hnonzero s ⟨hs.1, le_of_lt hs.2⟩)
  have hzcont : ContinuousOn z (Set.Icc a t) := by
    intro s hs
    exact ((hsol.2 s (hIcc hs)).2).continuousAt.continuousWithinAt
  have hareaCont : ContinuousOn
      (fun s => signedDoubleArea (z s).1) (Set.Icc a t) := by
    have hfield : Continuous (fun q : Fin 3 → Point => signedDoubleArea q) := by
      unfold signedDoubleArea cross
      fun_prop
    exact hfield.continuousOn.comp hzcont.fst (by intro s hs; exact Set.mem_univ _)
  rcases hpre with hpos | hneg
  · have htpos : 0 < signedDoubleArea (z t).1 := by
      rcases lt_or_gt_of_ne (hnonzero t ⟨le_of_lt hat, le_rfl⟩) with htn | htp
      · have hzero : 0 ∈ Set.Icc (signedDoubleArea (z t).1)
          (signedDoubleArea (z a).1) := ⟨le_of_lt htn, le_of_lt (hpos a ⟨le_rfl, hat⟩)⟩
        obtain ⟨s, hs, hszero⟩ :=
          (intermediate_value_Icc' (le_of_lt hat) hareaCont) hzero
        exact False.elim ((hnonzero s hs) hszero)
      · exact htp
    left
    intro s hs
    by_cases hst : s = t
    · simpa [hst] using htpos
    · have hst' : s < t := lt_of_le_of_ne hs.2 hst
      exact hpos s ⟨hs.1, hst'⟩
  · have htneg : signedDoubleArea (z t).1 < 0 := by
      rcases lt_or_gt_of_ne (hnonzero t ⟨le_of_lt hat, le_rfl⟩) with htn | htp
      · exact htn
      · have hzero : 0 ∈ Set.Icc (signedDoubleArea (z a).1)
          (signedDoubleArea (z t).1) := ⟨le_of_lt (hneg a ⟨le_rfl, hat⟩), le_of_lt htp⟩
        obtain ⟨s, hs, hszero⟩ :=
          (intermediate_value_Icc (le_of_lt hat) hareaCont) hzero
        exact False.elim ((hnonzero s hs) hszero)
    right
    intro s hs
    by_cases hst : s = t
    · simpa [hst] using htneg
    · have hst' : s < t := lt_of_le_of_ne hs.2 hst
      exact hneg s ⟨hs.1, hst'⟩

/-- Along any general-mass classical Newton solution issued from rest, both
Montgomery's pair moment and the physical center-of-mass moment are strictly
antitone on the complete initial noncollinear branch. Their derivatives at
the initial rest time are zero. No future syzygy or regular endpoint is
assumed. -/
theorem q1_for_every_classical_initialBranch
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I)
    (hconn : IsPreconnected I)
    {a : ℝ} (ha : a ∈ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (pairMomentCurve m (fun i s => (z s).1 i))
        (BeforeFirstCollinearity z I a) ∧
      StrictAntiOn (centerOfMassMomentCurve m (fun i s => (z s).1 i))
        (BeforeFirstCollinearity z I a) ∧
      deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) a = 0 ∧
      deriv (fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s) a = 0 ∧
      (∀ t ∈ BeforeFirstCollinearity z I a, a < t →
        deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) t < 0 ∧
        deriv (fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s) t < 0) := by
  have hpair := generalNewton_pairMomentCurve_strictAntiOn_initialBranch
    hsol hconn hm0 hm1 hm2 hG hrest
  have hcenter := generalNewton_centerOfMassMomentCurve_strictAntiOn_initialBranch
    hsol hconn hm0 hm1 hm2 hG hrest
  have hcenter0 := generalNewton_centerOfMassMomentCurve_deriv_eq_zero_at_rest
    hsol hconn ha hm0 hm1 hm2 hrest
  have hpair0 : deriv (fun s => pairMomentCurve m
      (fun i τ => (z τ).1 i) s) a = 0 := by
    have hcurve : (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) =
        fun s => totalMass m * centerOfMassMomentCurve m
          (fun i τ => (z τ).1 i) s := by
      funext s
      exact pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
        (fun i τ => (z τ).1 i) hm0 hm1 hm2 s
    rw [hcurve]
    simp [hcenter0]
  have hderivs : ∀ t ∈ BeforeFirstCollinearity z I a, a < t →
      deriv (fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s) t < 0 ∧
      deriv (fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s) t < 0 := by
    intro t ht hat
    rcases ht with ⟨hatle, hIcc, hnonzero⟩
    have hareaSign := q1_area_constantSign_on_Icc hsol hat hIcc hnonzero
    rcases hareaSign with hpos | hneg
    · exact q1_pairAndCenter_deriv_neg_of_positiveArea hsol hconn ha hat hIcc
        hm0 hm1 hm2 hG hpos hrest
    · let zR : ℝ → Phase := fun s => reflectGeneralPhase (z s)
      have hsolR : GeneralClassicalNewtonSolution G m zR I := by
        simpa [zR] using generalClassicalNewtonSolution_reflect hsol
      have hrestR : ∀ i, (zR a).2 i = 0 := by
        intro i
        simpa [zR, reflectGeneralPhase, reflectConfiguration] using
          congrArg reflectPoint (hrest i)
      have hareaR : ∀ s ∈ Set.Icc a t,
          0 < signedDoubleArea (zR s).1 := by
        intro s hs
        rw [show (zR s).1 = reflectConfiguration (z s).1 by rfl,
          signedDoubleArea_reflectConfiguration]
        exact neg_pos.mpr (hneg s hs)
      have hpositive := q1_pairAndCenter_deriv_neg_of_positiveArea hsolR hconn
        ha hat hIcc hm0 hm1 hm2 hG hareaR hrestR
      have hpairCurve : (fun s => pairMomentCurve m
          (fun i τ => (zR τ).1 i) s) =
          fun s => pairMomentCurve m (fun i τ => (z τ).1 i) s := by
        funext s
        exact pairMomentCurve_reflectGeneralPhase m z s
      have hM : totalMass m ≠ 0 :=
        ne_of_gt (totalMass_pos_of_positive m hm0 hm1 hm2)
      have hcenterCurve : (fun s => centerOfMassMomentCurve m
          (fun i τ => (zR τ).1 i) s) =
          fun s => centerOfMassMomentCurve m (fun i τ => (z τ).1 i) s := by
        funext s
        apply mul_left_cancel₀ hM
        calc
          totalMass m * centerOfMassMomentCurve m
              (fun i τ => (zR τ).1 i) s =
              pairMomentCurve m (fun i τ => (zR τ).1 i) s := by
                symm
                exact pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
                  (fun i τ => (zR τ).1 i) hm0 hm1 hm2 s
          _ = pairMomentCurve m (fun i τ => (z τ).1 i) s := congrFun hpairCurve s
          _ = totalMass m * centerOfMassMomentCurve m
              (fun i τ => (z τ).1 i) s := pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
                (fun i τ => (z τ).1 i) hm0 hm1 hm2 s
      have hpairDeriv := congrArg (fun f : ℝ → ℝ => deriv f t) hpairCurve
      have hcenterDeriv := congrArg (fun f : ℝ → ℝ => deriv f t) hcenterCurve
      exact ⟨by rw [← hpairDeriv]; exact hpositive.1,
        by rw [← hcenterDeriv]; exact hpositive.2⟩
  exact ⟨hpair, hcenter, hpair0, hcenter0, hderivs⟩

end

end DroppingThreeBodies
