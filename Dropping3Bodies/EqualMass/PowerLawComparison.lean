module

public import Dropping3Bodies.EqualMass.PowerLawModel
public import Dropping3Bodies.Dynamics.GeneralPairRotation
public import Dropping3Bodies.Support.CooperativePair
public import Dropping3Bodies.Support.IntervalEndpoint

@[expose] public section

namespace DroppingThreeBodies.CentralForce

noncomputable section

/-- Pair angular momentum without its constant reduced-mass factor. -/
def powerPairRotation (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  framePairRotation (sideVector (z t).1 i) (sideVector (z t).2 i)

theorem power_pair_torque (α g m : ℝ) (q : Fin 3 → Point) (i : Fin 3) :
    cross (sideVector q i)
      (sideVector (acceleration (powerCoefficients α (commonCouplings g)) (fun _ => m) q) i) =
      α * g / m * signedDoubleArea q *
        (Real.rpow (dist (q (cyclicPrev i)) (q i)) (-α - 2) -
         Real.rpow (dist (q (cyclicNext i)) (q i)) (-α - 2)) := by
  fin_cases i <;>
    simp [sideVector, acceleration, powerCoefficients, commonCouplings, weight,
      cyclicPrev, cyclicNext, signedDoubleArea, cross, Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

variable {α g m : ℝ} {z : ℝ → Phase} {I : Set ℝ} {a t T : ℝ}

private theorem position_coords (hs : EqualPowerSolution α g m z I) (ht : t ∈ I) :
    HasBodyCoordDerivAt (solutionPositionCurve z) (z t).2 t := by
  intro b k
  simpa [solutionPositionCurve, EuclideanSpace.coe_proj] using
    (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
      (body_derivatives hs ht b).1

theorem power_pair_rotation_deriv (hs : EqualPowerSolution α g m z I) (ht : t ∈ I)
    (i : Fin 3) :
    HasDerivAt (powerPairRotation z i)
      (α * g / m * signedDoubleArea (z t).1 *
        (Real.rpow (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) (-α - 2) -
         Real.rpow (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) (-α - 2))) t := by
  have hv : HasBodyCoordDerivAt (solutionVelocityCurve z)
      (acceleration (powerCoefficients α (commonCouplings g)) (fun _ => m) (z t).1) t := by
    intro b k
    simpa [solutionVelocityCurve, EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (body_derivatives hs ht b).2
  have h := hasDerivAt_frameAreaCurve (hasCoordDerivAt_sideVectorCurve (position_coords hs ht) i)
    (hasCoordDerivAt_sideVectorCurve hv i)
  apply h.congr_deriv
  change cross (sideVector (z t).2 i) (sideVector (z t).2 i) + _ = _
  rw [show cross (sideVector (z t).2 i) (sideVector (z t).2 i) = 0 by unfold cross; ring, zero_add]
  exact power_pair_torque α g m (z t).1 i

private theorem power_frame_momentum_zero (hs : EqualPowerSolution α g m z I)
    (hconn : IsPreconnected I) (ha : a ∈ I) (ht : t ∈ I)
    (hrest : ∀ j, (z a).2 j = 0) (i : Fin 3) :
    frameAngularMomentum (sideVector (z t).1 i) (sideOffset (z t).1 i)
      (sideVector (z t).2 i) (sideOffset (z t).2 i) = 0 := by
  let S := fun u => powerPairRotation z 0 u + powerPairRotation z 1 u + powerPairRotation z 2 u
  have d (u : ℝ) (hu : u ∈ I) : HasDerivAt S 0 u := by
    apply (((power_pair_rotation_deriv hs hu 0).add (power_pair_rotation_deriv hs hu 1)).add
      (power_pair_rotation_deriv hs hu 2)).congr_deriv
    simp only [cyclicPrev, cyclicNext]
    simp [dist_comm]; ring
  have heq : S t = S a := hs.1.is_const_of_deriv_eq_zero hconn
    (fun u hu => (d u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (d u hu).deriv) ht ha
  have h0 : S a = 0 := by
    simp [S, powerPairRotation, framePairRotation, sideVector, hrest, cross]
  rw [frameAngularMomentum_eq_sum_sidePairRotations_div_three]
  have hsum := heq.trans h0
  simpa [S, powerPairRotation, Fin.sum_univ_succ, add_assoc] using
    congrArg (fun x : ℝ => x / 3) hsum

private theorem power_area_curve (z : ℝ → Phase) (i : Fin 3) :
    frameAreaCurve (sideVectorCurve (solutionPositionCurve z) i)
      (sideOffsetCurve (solutionPositionCurve z) i) = fun t => signedDoubleArea (z t).1 := by
  funext t
  exact signedDoubleArea_eq_cross_sideFrame _ _

private theorem power_gap_curve (z : ℝ → Phase) (i : Fin 3) :
    frameGapCurve (sideVectorCurve (solutionPositionCurve z) i)
      (sideOffsetCurve (solutionPositionCurve z) i) = fun t => sideGap (z t).1 i := by
  funext t
  exact (sideGap_eq_neg_two_dot_sideFrame _ _).symm

/-- The undivided side-gap identity, including at collinear solution times. -/
theorem power_gap_identity (hs : EqualPowerSolution α g m z I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ j, (z a).2 j = 0) (i : Fin 3) :
    signedDoubleArea (z t).1 * deriv (fun s => sideGap (z s).1 i) t -
      sideGap (z t).1 i * deriv (fun s => signedDoubleArea (z s).1) t =
      -3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) *
        powerPairRotation z i t := by
  have h := bodyCurve_gap_derivative_identity i (position_coords hs ht)
    (power_frame_momentum_zero hs hconn ha ht hrest i)
  simpa only [power_area_curve, power_gap_curve, solutionPositionCurve, powerPairRotation] using h

private theorem gap_distances (q : Fin 3 → Point) (i : Fin 3) :
    sideGap q i = dist (q (cyclicPrev i)) (q i) ^ 2 - dist (q (cyclicNext i)) (q i) ^ 2 := by
  fin_cases i <;> simp [sideGap, cyclicPrev, cyclicNext, dist_eq_norm, norm_sub_rev]
  exact norm_sub_rev _ _

/-- The positive multiplier of a squared-side difference in the power-law torque.
The diagonal value is the negative derivative with respect to squared distance. -/
def powerGapFactor (α x y : ℝ) : ℝ :=
  if x = y then (α+2)/2 * Real.rpow x (-α-4)
  else (Real.rpow y (-α-2) - Real.rpow x (-α-2)) / (x^2-y^2)

theorem power_gap_factorization (α x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.rpow x (-α-2) - Real.rpow y (-α-2) = -powerGapFactor α x y * (x^2-y^2) := by
  by_cases h : x = y
  · subst y
    simp
  · have hsq : x^2-y^2 ≠ 0 := by
      rcases lt_or_gt_of_ne h with h' | h'
      · exact (sub_neg.mpr ((sq_lt_sq₀ hx.le hy.le).2 h')).ne
      · exact (sub_pos.mpr ((sq_lt_sq₀ hy.le hx.le).2 h')).ne'
    simp only [powerGapFactor, if_neg h]
    field_simp
    ring

theorem powerGapFactor_pos (hα : 0 < α) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < powerGapFactor α x y := by
  unfold powerGapFactor
  split_ifs with h
  · exact mul_pos (by linarith) (Real.rpow_pos_of_pos hx _)
  · have hp : -α - 2 < 0 := by linarith
    rcases lt_or_gt_of_ne h with h' | h'
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (Real.rpow_lt_rpow_of_neg hx h' hp))
        (sub_neg.mpr ((sq_lt_sq₀ hx.le hy.le).2 h'))
    · exact div_pos (sub_pos.mpr (Real.rpow_lt_rpow_of_neg hy h' hp))
        (sub_pos.mpr ((sq_lt_sq₀ hy.le hx.le).2 h'))

private def moment (z : ℝ → Phase) (i : Fin 3) (t : ℝ) :=
  frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i)

private def gapMultiplier (α g m : ℝ) (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  α*g/m * powerGapFactor α
    (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
    (dist ((z t).1 (cyclicNext i)) ((z t).1 i))

private theorem adjacent_pos (hs : EqualPowerSolution α g m z I) (ht : t ∈ I)
    (i : Fin 3) :
    0 < dist ((z t).1 (cyclicPrev i)) ((z t).1 i) ∧
    0 < dist ((z t).1 (cyclicNext i)) ((z t).1 i) :=
  ⟨dist_pos.mpr ((hs.2 t ht).1 _ _ (cyclicPrev_ne_self i)),
    dist_pos.mpr ((hs.2 t ht).1 _ _ (cyclicNext_ne_self i))⟩

private theorem power_cooperative (hs : EqualPowerSolution α g m z I)
    (hconn : IsPreconnected I) (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ j, (z a).2 j = 0)
    (i : Fin 3) (hB : signedDoubleArea (z t).1 ≠ 0) :
    HasDerivAt (fun s => sideGap (z s).1 i / signedDoubleArea (z s).1)
        ((3 * moment z i t / signedDoubleArea (z t).1 ^ 2) * (-powerPairRotation z i t)) t ∧
    HasDerivAt (fun s => -powerPairRotation z i s)
        ((signedDoubleArea (z t).1 ^ 2 * gapMultiplier α g m z i t) *
         (sideGap (z t).1 i / signedDoubleArea (z t).1)) t := by
  have hr := hasCoordDerivAt_sideVectorCurve (position_coords hs ht) i
  have ho := hasCoordDerivAt_sideOffsetCurve (position_coords hs ht) i
  have heq : frameArea (sideVector (z t).1 i) (sideOffset (z t).1 i) = signedDoubleArea (z t).1 :=
    signedDoubleArea_eq_cross_sideFrame _ _
  have h := hasDerivAt_frameGapRatioCurve hr ho (power_frame_momentum_zero hs hconn ha ht hrest i)
    (heq.trans_ne hB)
  simp only [power_area_curve, power_gap_curve] at h
  constructor
  · apply h.congr_deriv
    simp only [sideVectorCurve, sideOffsetCurve, solutionPositionCurve, heq]
    unfold moment powerPairRotation
    ring
  · apply (power_pair_rotation_deriv hs ht i).neg.congr_deriv
    have hd := adjacent_pos hs ht i
    rw [power_gap_factorization _ _ _ hd.1 hd.2, gap_distances]
    unfold gapMultiplier
    field_simp [hB]

/-- On every noncollinear initial segment an initially strict side gap keeps
its sign, and the magnitude of the corresponding pair rotation grows strictly.
The area-product hypothesis admits either orientation. -/
theorem power_gap_comparison (hs : EqualPowerSolution α g m z I)
    (hα : 0 < α) (hg : 0 < g) (hm : 0 < m) (hconn : IsPreconnected I)
    (haT : a ≤ T) (hseg : Set.Icc a T ⊆ I) (hrest : ∀ j, (z a).2 j = 0)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z a).1 * signedDoubleArea (z t).1)
    (i : Fin 3) (hgap : sideGap (z a).1 i ≠ 0) :
    (∀ t ∈ Set.Icc a T, 0 < sideGap (z a).1 i * sideGap (z t).1 i) ∧
    StrictMonoOn (fun t => |powerPairRotation z i t|) (Set.Icc a T) ∧
    (∀ t ∈ Set.Ioc a T, 0 < -(sideGap (z a).1 i / signedDoubleArea (z a).1) *
      powerPairRotation z i t) := by
  let B := fun s => signedDoubleArea (z s).1
  let f := fun s => sideGap (z s).1 i
  let ρ := f a / B a
  let X := fun s => ρ * (f s / B s)
  let Y := fun s => ρ * (-powerPairRotation z i s)
  let c := fun s => 3 * moment z i s / B s ^ 2
  let b := fun s => B s ^ 2 * gapMultiplier α g m z i s
  have ha' : a ∈ Set.Icc a T := ⟨le_rfl,haT⟩
  have hB (s) (hs' : s ∈ Set.Icc a T) : B s ≠ 0 :=
    right_ne_zero_of_mul (harea s hs').ne'
  have hρ : ρ ≠ 0 := div_ne_zero hgap (hB a ha')
  have hx0 : 0 < X a := mul_self_pos.mpr hρ
  have hy0 : Y a = 0 := by
    fin_cases i <;> simp [Y, powerPairRotation, framePairRotation, sideVector, hrest, cross]
  have dc (s) (h : s ∈ Set.Icc a T) :=
    power_cooperative hs hconn (hseg ha') (hseg h) hrest i (hB s h)
  have dx (s) (h : s ∈ Set.Icc a T) : HasDerivAt X (c s * Y s) s := by
    apply ((dc s h).1.const_mul ρ).congr_deriv
    dsimp [c,Y,B]
    ring
  have dy (s) (h : s ∈ Set.Icc a T) : HasDerivAt Y (b s * X s) s := by
    apply ((dc s h).2.const_mul ρ).congr_deriv
    dsimp [b,X,f,B]
    ring
  have hc (s) (_h : s ∈ Set.Icc a T) : 0 ≤ c s := by
    dsimp [c, moment, frameMoment]
    positivity
  have hb (s) (h : s ∈ Set.Icc a T) : 0 < b s := by
    have hd := adjacent_pos hs (hseg h) i
    exact mul_pos (sq_pos_of_ne_zero (hB s h)) (mul_pos (div_pos (mul_pos hα hg) hm)
      (powerGapFactor_pos hα hd.1 hd.2))
  have hsign := cooperative_pair_signs haT
    (fun s h => (dx s h).continuousAt.continuousWithinAt)
    (fun s h => (dy s h).continuousAt.continuousWithinAt) hx0 hy0 dx dy hc hb
  have hinc := cooperative_second_strictMono dy hsign.1 hb
  have ynonneg (s) (h : s ∈ Set.Icc a T) : 0 ≤ Y s := by
    rw [←hy0]
    exact hinc.monotoneOn ha' h h.1
  refine ⟨?_, ?_, ?_⟩
  · intro s h
    have hx := hsign.1 s h
    change 0 < (f a / B a) * (f s / B s) at hx
    rw [div_mul_div_comm] at hx
    exact (div_pos_iff_of_pos_right (harea s h)).1 hx
  · intro s hs' u hu hsu
    have habs (v) (hv : v ∈ Set.Icc a T) : Y v = |ρ| * |powerPairRotation z i v| := by
      rw [← abs_of_nonneg (ynonneg v hv)]
      simp [Y, abs_mul]
    have h := hinc hs' hu hsu
    rw [habs s hs', habs u hu] at h
    exact (mul_lt_mul_iff_right₀ (abs_pos.mpr hρ)).mp h
  · intro s h
    simpa [Y, ρ, f, B] using hsign.2 s ⟨h.1.le,h.2⟩ h.1


/-- Strict comparison at a regular collinear endpoint of an initial branch.
The undivided identity controls the endpoint where the normalized gap is undefined. -/
theorem power_gap_at_regular_endpoint (hs : EqualPowerSolution α g m z I)
    (hα : 0 < α) (hg : 0 < g) (hm : 0 < m) (hconn : IsPreconnected I)
    (haT : a < T) (hseg : Set.Icc a T ⊆ I) (hrest : ∀ j, (z a).2 j = 0)
    (harea : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z a).1 * signedDoubleArea (z t).1)
    (hzero : signedDoubleArea (z T).1 = 0) (i : Fin 3) (hgap : sideGap (z a).1 i ≠ 0) :
    0 < sideGap (z a).1 i * sideGap (z T).1 i := by
  have pre (u) (hu : u ∈ Set.Ico a T) := power_gap_comparison hs hα hg hm hconn hu.1
    (fun _ hx => hseg ⟨hx.1, hx.2.trans hu.2.le⟩) hrest
    (fun s h => harea s ⟨h.1, h.2.trans_lt hu.2⟩) i hgap
  have gapcont : ContinuousOn (fun t => sideGap (z t).1 i) (Set.Icc a T) := by
    intro u hu
    have h := hasDerivAt_frameGapCurve
      (hasCoordDerivAt_sideVectorCurve (position_coords hs (hseg hu)) i)
      (hasCoordDerivAt_sideOffsetCurve (position_coords hs (hseg hu)) i)
    rw [power_gap_curve] at h
    exact h.continuousAt.continuousWithinAt
  have hweak := continuousOn_nonneg_right_of_nonneg_Ico haT
    (continuousOn_const.mul gapcont)
    (fun u hu => ((pre u hu).1 u ⟨hu.1, le_rfl⟩).le)
  obtain ⟨s, has, hst⟩ := exists_between haT
  have hKs : powerPairRotation z i s ≠ 0 :=
    right_ne_zero_of_mul ((pre s ⟨has.le, hst⟩).2.2 s ⟨has,le_rfl⟩).ne'
  have hKTbound : 0 ≤ |powerPairRotation z i T| - |powerPairRotation z i s| := by
    apply continuousOn_nonneg_right_of_nonneg_Ico hst
    · apply ContinuousOn.sub _ continuousOn_const
      intro u hu
      exact (power_pair_rotation_deriv hs (hseg ⟨has.le.trans hu.1,hu.2⟩) i).continuousAt.abs.continuousWithinAt
    · intro u hu
      exact sub_nonneg.mpr ((pre u ⟨has.le.trans hu.1,hu.2⟩).2.1.monotoneOn
        ⟨has.le,hu.1⟩ ⟨has.le.trans hu.1, le_rfl⟩ hu.1)
  have hKT : powerPairRotation z i T ≠ 0 :=
    abs_pos.mp (lt_of_lt_of_le (abs_pos.mpr hKs) (sub_nonneg.mp hKTbound))
  have ht := hseg ⟨haT.le, le_rfl⟩
  have hcf : CollisionFree (z T).1 := (hs.2 T ht).1
  have hr : sideVector (z T).1 i ≠ 0 := by
    fin_cases i
    · exact sub_ne_zero.mpr (hcf 2 1 (by decide))
    · exact sub_ne_zero.mpr (hcf 0 2 (by decide))
    · exact sub_ne_zero.mpr (hcf 1 0 (by decide))
  have hi : 0 < frameMoment (sideVector (z T).1 i) (sideOffset (z T).1 i) := by
    have h := norm_pos_iff.mpr hr
    unfold frameMoment
    positivity
  apply lt_of_le_of_ne hweak
  intro h
  have hf : sideGap (z T).1 i = 0 := (mul_eq_zero.mp h.symm).resolve_left hgap
  have hid := power_gap_identity hs hconn (hseg ⟨le_rfl,haT.le⟩) ht hrest i
  rw [hzero, hf] at hid
  have hn : -3 * frameMoment (sideVector (z T).1 i) (sideOffset (z T).1 i) *
      powerPairRotation z i T ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hi.ne') hKT
  exact hn (by linarith only [hid])

end
end DroppingThreeBodies.CentralForce
