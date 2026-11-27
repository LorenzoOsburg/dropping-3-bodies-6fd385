module

public import Dropping3Bodies.Dynamics.SyzygyAngle
public import Dropping3Bodies.Dynamics.GeneralNewton
public import Dropping3Bodies.Inertia.JacobiRiccati

@[expose] public section

namespace DroppingThreeBodies

/-- A unit-mass classical solution is the specialization of the general Newton
    equation at `G=1` and `mᵢ=1`. -/
theorem classicalNewton_generalSolution_one
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I) :
    GeneralClassicalNewtonSolution 1 (fun _ : Fin 3 => (1 : ℝ)) z I := by
  refine ⟨hsol.1, ?_⟩
  intro t ht
  obtain ⟨hcf, hderiv⟩ := hsol.2 t ht
  refine ⟨hcf, ?_⟩
  rw [generalNewtonField_one_eq_unit]
  exact hderiv

/-- Every squared pair distance is bounded by the unit-mass pair moment. -/
theorem unit_pairDistance_sq_le_pairMoment
    (q : Fin 3 → Point) (j k : Fin 3) (hjk : j ≠ k) :
    dist (q j) (q k) ^ 2 ≤ pairMoment (fun _ : Fin 3 => (1 : ℝ)) q := by
  fin_cases j <;> fin_cases k <;>
    simp_all [pairMoment, dist_comm] <;>
    nlinarith [sq_nonneg (dist (q 0) (q 1)), sq_nonneg (dist (q 1) (q 2)),
      sq_nonneg (dist (q 0) (q 2)),
      congrArg (fun x : ℝ => x ^ 2) (dist_comm (q 0) (q 1)),
      congrArg (fun x : ℝ => x ^ 2) (dist_comm (q 1) (q 2)),
      congrArg (fun x : ℝ => x ^ 2) (dist_comm (q 0) (q 2))]

/-- Strict Jacobi-moment decrease from L-G bounds every pair distance using
    the static identity `pairMoment = 3 * jacobiMoment`. -/
theorem classicalNewton_pairDistance_sq_le_three_jacobiMoment_initial
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I)
    (hconn : IsPreconnected I) {a T : ℝ}
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ i, (z a).2 i = 0)
    (harea : ∀ s ∈ Set.Icc a T, 0 < signedDoubleArea (z s).1)
    {t : ℝ} (ht : t ∈ Set.Icc a T) (j k : Fin 3) (hjk : j ≠ k) :
    dist ((z t).1 j) ((z t).1 k) ^ 2 ≤
      3 * jacobiMoment (fun _ : Fin 3 => (1 : ℝ)) ((z a).1) := by
  let m : Fin 3 → ℝ := fun _ => 1
  have hgen := classicalNewton_generalSolution_one hsol
  have haI : a ∈ I := hsegment ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hmono := generalNewton_negJacobiMoment_monotoneOn_Icc
    (G := 1) (m := m) (z := z) (I := I) hgen hconn haI hsegment
    (by norm_num [m]) (by norm_num [m]) (by norm_num [m]) (by norm_num)
    harea hrest
  have hJ : jacobiMomentCurve m (fun i s => (z s).1 i) t ≤
      jacobiMomentCurve m (fun i s => (z s).1 i) a := by
    have h := hmono ⟨le_rfl, le_trans ht.1 ht.2⟩ ht ht.1
    have h' : -jacobiMomentCurve m (fun i s => (z s).1 i) a ≤
        -jacobiMomentCurve m (fun i s => (z s).1 i) t := by simpa using h
    linarith
  have hpair := unit_pairDistance_sq_le_pairMoment ((z t).1) j k hjk
  have hpairId := pairMoment_eq_totalMass_mul_jacobiMoment
    (fun _ : Fin 3 => (1 : ℝ)) ((z t).1) (by norm_num) (by norm_num) (by norm_num)
  rw [hpairId] at hpair
  have hmass : totalMass (fun _ : Fin 3 => (1 : ℝ)) = 3 := by
    norm_num [totalMass]
  rw [hmass] at hpair
  have hJ' : jacobiMoment m ((z t).1) ≤ jacobiMoment m ((z a).1) := by
    simpa [jacobiMomentCurve, m] using hJ
  simpa [m] using le_trans hpair (mul_le_mul_of_nonneg_left hJ' (by norm_num))

/-- Quotient comparison for a nonnegative numerator bounded below and a
    positive denominator bounded above. -/
theorem div_lower_bound_of_num_lower_den_upper
    {x₀ x d M : ℝ} (hx₀ : 0 ≤ x₀) (hx : x₀ ≤ x)
    (hd : 0 < d) (hM : 0 < M) (hdM : d ≤ M) :
    x₀ / M ≤ x / d := by
  have hcross : x₀ * d ≤ x * M := by
    calc
      x₀ * d ≤ x₀ * M := mul_le_mul_of_nonneg_left hdM hx₀
      _ ≤ x * M := mul_le_mul_of_nonneg_right hx (le_of_lt hM)
  exact (div_le_div_iff₀ hM hd).2 hcross

/-- A fixed positive lower bound for the angle rate after a fixed time `t₀`.
    The numerator lower bounds are the two oriented pair rotations at `t₀`;
    the denominator upper bounds follow from the strictly decreasing Jacobi
    moment. Source of the Riccati input: [DroppingMontgomery2026], frozen
    2026-10-29, `eq:endpointbound`; the uniform angle estimate is derived here
    from the project's pair-rotation formulas. -/
theorem classicalNewton_triangleAngleRate_uniform_lower_bound_of_initial_opposite_side_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t₀ T t : ℝ} (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ s ∈ Set.Icc a T, 0 < signedDoubleArea (z s).1)
    (ht₀ : t₀ ∈ Set.Icc a T) (hat₀ : a < t₀)
    (ht : t ∈ Set.Icc a T) (ht₀t : t₀ ≤ t) :
    let c := (sidePairRotationCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) (cyclicNext i) t₀ -
      sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
        (cyclicPrev i) t₀) /
      (3 * (jacobiMoment (fun _ : Fin 3 => (1 : ℝ)) ((z a).1) + 1))
    0 < c ∧ c ≤ triangleAngleRate z i t := by
  let m : Fin 3 → ℝ := fun _ => 1
  let M : ℝ := 3 * (jacobiMoment m ((z a).1) + 1)
  let Lplus := sidePairRotationCurve (solutionPositionCurve z)
    (solutionVelocityCurve z) (cyclicNext i)
  let Lminus := sidePairRotationCurve (solutionPositionCurve z)
    (solutionVelocityCurve z) (cyclicPrev i)
  have hgapNext : sideGap (z a).1 (cyclicNext i) < 0 := by
    rw [sideGap_eq_next_sub_prev_sideSq, cyclicNext_cyclicNext,
      cyclicPrev_cyclicNext]
    exact sub_neg.mpr hlongPrev
  have hgapPrev : 0 < sideGap (z a).1 (cyclicPrev i) := by
    rw [sideGap_eq_next_sub_prev_sideSq, cyclicNext_cyclicPrev,
      cyclicPrev_cyclicPrev]
    exact sub_pos.mpr hlongNext
  have hsegmentT0 : Set.Icc a t₀ ⊆ I := by
    intro s hs
    exact hsegment ⟨hs.1, le_trans hs.2 ht₀.2⟩
  have hareaT0 : ∀ s ∈ Set.Icc a t₀, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact harea s ⟨hs.1, le_trans hs.2 ht₀.2⟩
  have hnextRot := classicalNewton_orientedRotation_pos_of_nonzero_sideGap
    (cyclicNext i) hsol hconn hat₀ hsegmentT0 hrest hcenter
    (ne_of_lt hgapNext) hareaT0
  have hprevRot := classicalNewton_orientedRotation_pos_of_nonzero_sideGap
    (cyclicPrev i) hsol hconn hat₀ hsegmentT0 hrest hcenter
    (ne_of_gt hgapPrev) hareaT0
  have hLplus₀ : 0 < Lplus t₀ := by
    rw [if_neg (not_lt_of_ge (le_of_lt hgapNext))] at hnextRot
    simpa [Lplus, sideGapRotationSignCurve] using hnextRot
  have hLminus₀ : Lminus t₀ < 0 := by
    rw [if_pos hgapPrev] at hprevRot
    simpa [Lminus, sideGapRotationSignCurve] using hprevRot
  have haT : a < T := lt_of_lt_of_le hat₀ ht₀.2
  have hnextMono := classicalNewton_orientedRotation_nondecreasing_on_Icc
    (cyclicNext i) hsol hconn haT hsegment hrest hcenter
    (ne_of_lt hgapNext) harea ht₀ ht ht₀t
  have hprevMono := classicalNewton_orientedRotation_nondecreasing_on_Icc
    (cyclicPrev i) hsol hconn haT hsegment hrest hcenter
    (ne_of_gt hgapPrev) harea ht₀ ht ht₀t
  have hLplus : Lplus t₀ ≤ Lplus t := by
    simpa [Lplus, sideGapRotationSignCurve,
      not_lt_of_ge (le_of_lt hgapNext)] using hnextMono
  have hLminus : -Lminus t₀ ≤ -Lminus t := by
    simpa [Lminus, sideGapRotationSignCurve, hgapPrev] using hprevMono
  have hrateNextDen := classicalNewton_pairDistance_sq_le_three_jacobiMoment_initial
    hsol hconn hsegment hrest harea ht (cyclicPrev i) i (cyclicPrev_ne_self i)
  have hratePrevDen := classicalNewton_pairDistance_sq_le_three_jacobiMoment_initial
    hsol hconn hsegment hrest harea ht (cyclicNext i) i (cyclicNext_ne_self i)
  have hJnonneg : 0 ≤ jacobiMoment m ((z a).1) := by
    unfold jacobiMoment
    positivity
  have hdenBoundNext :
      dist ((z t).1 (cyclicPrev i)) ((z t).1 i) ^ 2 ≤ M := by
    dsimp [M, m]
    nlinarith [hrateNextDen]
  have hdenBoundPrev :
      dist ((z t).1 (cyclicNext i)) ((z t).1 i) ^ 2 ≤ M := by
    dsimp [M, m]
    nlinarith [hratePrevDen]
  have hM : 0 < M := by positivity
  have hnextDist : 0 < dist ((z t).1 (cyclicPrev i)) ((z t).1 i) :=
    (collisionFree_iff_dist_pos (z t).1).1 (hsol.2 t (hsegment ht)).1
      (cyclicPrev i) i (cyclicPrev_ne_self i)
  have hprevDist : 0 < dist ((z t).1 (cyclicNext i)) ((z t).1 i) :=
    (collisionFree_iff_dist_pos (z t).1).1 (hsol.2 t (hsegment ht)).1
      (cyclicNext i) i (cyclicNext_ne_self i)
  have hnextFraction : Lplus t₀ / M ≤
      Lplus t / (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 := by
    exact div_lower_bound_of_num_lower_den_upper (le_of_lt hLplus₀) hLplus
      (sq_pos_of_pos hnextDist) hM hdenBoundNext
  have hprevFraction : (-Lminus t₀) / M ≤
      (-Lminus t) / (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) ^ 2 := by
    exact div_lower_bound_of_num_lower_den_upper (le_of_lt (neg_pos.mpr hLminus₀))
      (by linarith) (sq_pos_of_pos hprevDist) hM hdenBoundPrev
  have hc : 0 < (Lplus t₀ - Lminus t₀) / M := by
    have : 0 < Lplus t₀ - Lminus t₀ := by linarith
    exact div_pos this hM
  have hrateId := classicalNewton_triangleAngleRate_eq_sidePairRotationRatios
    (i := i) hsol (hsegment ht)
  change 0 < (Lplus t₀ - Lminus t₀) / M ∧
    (Lplus t₀ - Lminus t₀) / M ≤ triangleAngleRate z i t
  constructor
  · exact hc
  ·
    rw [hrateId]
    calc
      (Lplus t₀ - Lminus t₀) / M =
          Lplus t₀ / M + (-Lminus t₀) / M := by ring
      _ ≤ Lplus t / (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 +
          (-Lminus t) / (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) ^ 2 :=
            add_le_add hnextFraction hprevFraction
      _ = Lplus t / (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 -
          Lminus t / (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) ^ 2 := by ring

/-- Source: [DroppingMontgomery2026], frozen 2026-10-29,
    `sec:firstsyzygy`, `eq:anglegrowth`--`eq:finitetime`. The mean-value
    argument combines the uniform rate theorem with the branch-free bound
    `0 < α < π`; the resulting finite-time bound is project-formalized. -/
theorem classicalNewton_triangleAngleCurve_time_bound_of_initial_opposite_side_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t₀ T t : ℝ} (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ s ∈ Set.Icc a T, 0 < signedDoubleArea (z s).1)
    (ht₀ : t₀ ∈ Set.Icc a T) (hat₀ : a < t₀)
    (ht : t ∈ Set.Icc a T) (ht₀t : t₀ ≤ t) :
    let c := (sidePairRotationCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) (cyclicNext i) t₀ -
      sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
        (cyclicPrev i) t₀) /
      (3 * (jacobiMoment (fun _ : Fin 3 => (1 : ℝ)) ((z a).1) + 1))
    t ≤ t₀ + (Real.pi - triangleAngleCurve z i t₀) / c := by
  let c := (sidePairRotationCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) (cyclicNext i) t₀ -
    sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
      (cyclicPrev i) t₀) /
    (3 * (jacobiMoment (fun _ : Fin 3 => (1 : ℝ)) ((z a).1) + 1))
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  have hrateLower : ∀ s ∈ Set.Icc t₀ T,
      c ≤ triangleAngleRate z i s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc a T :=
      ⟨le_trans ht₀.1 hs.1, hs.2⟩
    have h := classicalNewton_triangleAngleRate_uniform_lower_bound_of_initial_opposite_side_strictLongest
      i hsol hconn hsegment hrest hcenter hlongPrev hlongNext harea
      ht₀ hat₀ hsIcc hs.1
    simpa [c] using h.2
  have hc : 0 < c := by
    have h := classicalNewton_triangleAngleRate_uniform_lower_bound_of_initial_opposite_side_strictLongest
      i hsol hconn hsegment hrest hcenter hlongPrev hlongNext harea
      ht₀ hat₀ ht₀ le_rfl
    simpa [c] using h.1
  let F : ℝ → ℝ := fun s => triangleAngleCurve z i s - c * s
  have hderivF : ∀ s ∈ Set.Icc t₀ T,
      HasDerivAt F (triangleAngleRate z i s - c) s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc a T := ⟨le_trans ht₀.1 hs.1, hs.2⟩
    have hangle := classicalNewton_triangleAngleCurve_hasDerivAt (i := i) hsol
      (hsegment hsIcc) (harea s hsIcc)
    have hlinear := (hasDerivAt_id s).mul_const c
    have hFfun : F = fun x => triangleAngleCurve z i x - x * c := by
      funext x
      simp [F]
      ring
    rw [hFfun]
    have hlinear' : HasDerivAt (fun x : ℝ => x * c) c s := by
      simpa using hlinear
    exact hangle.sub hlinear'
  have hmono := monotoneOn_of_hasDerivAt_nonneg (convex_Icc t₀ T)
    hderivF (by
      intro s hs
      exact sub_nonneg.mpr (hrateLower s hs))
  have htIoc : t ∈ Set.Icc t₀ T := ⟨ht₀t, ht.2⟩
  have hF := hmono ⟨le_rfl, ht₀.2⟩ htIoc ht₀t
  have hgrowth : triangleAngleCurve z i t₀ + c * (t - t₀) ≤
      triangleAngleCurve z i t := by
    change triangleAngleCurve z i t₀ - c * t₀ ≤
      triangleAngleCurve z i t - c * t at hF
    linarith
  have hupper : triangleAngleCurve z i t ≤ Real.pi :=
    le_of_lt (triangleAngleCurve_mem_Ioo z i t).2
  have hmul : (t - t₀) * c ≤ Real.pi - triangleAngleCurve z i t₀ := by
    nlinarith
  have hdiv : t - t₀ ≤ (Real.pi - triangleAngleCurve z i t₀) / c :=
    (le_div_iff₀ hc).2 hmul
  change t ≤ t₀ + (Real.pi - triangleAngleCurve z i t₀) / c
  linarith

/-- A rightward solution domain on which the oriented area stays positive is
    bounded above when the initial opposite side is strictly longest. The
    fixed rate constant is chosen once at `t₀`; the compact angle time bound
    is then applied separately to every later time.

    Source: [DroppingMontgomery2026], frozen 2026-10-29,
    `sec:firstsyzygy`, `eq:anglegrowth` and `eq:finitetime`. The passage from
    compact time bounds to boundedness of the whole positive-area domain is
    the project formalization. -/
theorem classicalNewton_positiveArea_branch_boundedAbove_of_initial_opposite_side_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t₀ : ℝ} (hat₀ : a < t₀)
    (hsegment₀ : Set.Icc a t₀ ⊆ I)
    (hsegment : ∀ {t}, t ∈ I → a ≤ t → Set.Icc a t ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ I, a ≤ t → 0 < signedDoubleArea (z t).1) :
    ∃ B : ℝ, ∀ t ∈ I, a ≤ t → t ≤ B := by
  let m : Fin 3 → ℝ := fun _ => 1
  let c := (sidePairRotationCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) (cyclicNext i) t₀ -
    sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
      (cyclicPrev i) t₀) /
    (3 * (jacobiMoment m ((z a).1) + 1))
  let B := t₀ + (Real.pi - triangleAngleCurve z i t₀) / c
  have ht₀I : t₀ ∈ I := hsegment₀ ⟨le_of_lt hat₀, le_rfl⟩
  have harea₀ : ∀ s ∈ Set.Icc a t₀, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact harea s (hsegment₀ hs) hs.1
  have hrate₀ := classicalNewton_triangleAngleRate_uniform_lower_bound_of_initial_opposite_side_strictLongest
    i hsol hconn hsegment₀ hrest hcenter hlongPrev hlongNext harea₀
    ⟨le_of_lt hat₀, le_rfl⟩ hat₀ ⟨le_of_lt hat₀, le_rfl⟩ le_rfl
  have hc : 0 < c := by
    simpa [c, m] using hrate₀.1
  have hangle₀ := triangleAngleCurve_mem_Ioo z i t₀
  have ht₀B : t₀ ≤ B := by
    dsimp [B]
    have hnum : 0 ≤ Real.pi - triangleAngleCurve z i t₀ := by linarith [hangle₀.2]
    exact le_add_of_nonneg_right (div_nonneg hnum hc.le)
  refine ⟨B, ?_⟩
  intro t ht hat
  by_cases ht₀t : t ≤ t₀
  · exact le_trans ht₀t ht₀B
  · have ht₀lt : t₀ ≤ t := le_of_not_ge ht₀t
    have hsegT := hsegment ht hat
    have hareaT : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1 := by
      intro s hs
      exact harea s (hsegT hs) hs.1
    have htime := classicalNewton_triangleAngleCurve_time_bound_of_initial_opposite_side_strictLongest
      i hsol hconn hsegT hrest hcenter hlongPrev hlongNext hareaT
      ⟨le_of_lt hat₀, ht₀lt⟩ hat₀ ⟨hat, le_rfl⟩ ht₀lt
    simpa [B, c, m] using htime

end DroppingThreeBodies
