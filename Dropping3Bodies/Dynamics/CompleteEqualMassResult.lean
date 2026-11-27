module

public import Dropping3Bodies.Dynamics.FirstSyzygyCertificate
public import Dropping3Bodies.EqualMass.SolutionSideOrdering
public import Mathlib.Tactic

@[expose] public section


/-! # Complete equal-mass strict-longest-side result

This module strengthens the first-event certificate with preservation of both
strict side comparisons through the regular collinear endpoint.
-/

namespace DroppingThreeBodies

noncomputable section

set_option maxHeartbeats 1000000

/-- A strict longest side at rest remains strictly longest throughout the
closed interval ending at a positive-area first regular syzygy. -/
theorem classicalNewton_strictLongestSide_on_Icc_of_firstSyzygy
    (i : Fin 3) {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {T : ℝ} (hTpos : 0 < T) (hsegment : Set.Icc 0 T ⊆ I)
    (hrest : ∀ b, (z 0).2 b = 0)
    (hcenter : (z 0).1 0 + (z 0).1 1 + (z 0).1 2 = 0)
    (hgapPrev : 0 < sideGap (z 0).1 (cyclicPrev i))
    (hgapNext : sideGap (z 0).1 (cyclicNext i) < 0)
    (hgapMiddle : sideGap (z 0).1 i ≠ 0)
    (hareaPre : ∀ t ∈ Set.Ico 0 T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    ∀ t ∈ Set.Icc 0 T,
      sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
      sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
      ((0 < sideGap (z 0).1 i ∧ 0 < sideGap (z t).1 i) ∨
        (sideGap (z 0).1 i < 0 ∧ sideGap (z t).1 i < 0)) := by
  intro t ht
  have hgapP : 0 < sideGap (z t).1 (cyclicPrev i) := by
    by_cases hteq : t = T
    · subst t
      exact classicalNewton_sideGap_pos_at_regular_syzygy_of_pos
        (cyclicPrev i) hsol hconn hTpos hsegment hrest hcenter
        hgapPrev hareaPre hsyzygy
    · have htt : t < T := lt_of_le_of_ne ht.2 hteq
      by_cases htzero : t = 0
      · simpa [htzero] using hgapPrev
      · have h0t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
        have hsub : Set.Icc 0 t ⊆ I := by
          intro s hs
          exact hsegment ⟨hs.1, le_trans hs.2 htt.le⟩
        have harea : ∀ s ∈ Set.Icc 0 t, 0 < signedDoubleArea (z s).1 := by
          intro s hs
          exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 htt⟩
        exact (classicalNewton_sideGap_positive_on_Icc (cyclicPrev i)
          hsol hconn h0t hsub hrest hcenter hgapPrev harea) t ⟨le_of_lt h0t, le_rfl⟩
  have hgapN : sideGap (z t).1 (cyclicNext i) < 0 := by
    by_cases hteq : t = T
    · subst t
      exact classicalNewton_sideGap_neg_at_regular_syzygy_of_neg
        (cyclicNext i) hsol hconn hTpos hsegment hrest hcenter
        hgapNext hareaPre hsyzygy
    · have htt : t < T := lt_of_le_of_ne ht.2 hteq
      by_cases htzero : t = 0
      · simpa [htzero] using hgapNext
      · have h0t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
        have hsub : Set.Icc 0 t ⊆ I := by
          intro s hs
          exact hsegment ⟨hs.1, le_trans hs.2 htt.le⟩
        have harea : ∀ s ∈ Set.Icc 0 t, 0 < signedDoubleArea (z s).1 := by
          intro s hs
          exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 htt⟩
        exact (classicalNewton_sideGap_negative_on_Icc (cyclicNext i)
          hsol hconn h0t hsub hrest hcenter hgapNext harea) t ⟨le_of_lt h0t, le_rfl⟩
  have hgapM : (0 < sideGap (z 0).1 i ∧ 0 < sideGap (z t).1 i) ∨
      (sideGap (z 0).1 i < 0 ∧ sideGap (z t).1 i < 0) := by
    by_cases hpos : 0 < sideGap (z 0).1 i
    · have hstrict : 0 < sideGap (z t).1 i := by
        by_cases hteq : t = T
        · subst t
          exact classicalNewton_sideGap_pos_at_regular_syzygy_of_pos
            i hsol hconn hTpos hsegment hrest hcenter hpos hareaPre hsyzygy
        · have htt : t < T := lt_of_le_of_ne ht.2 hteq
          by_cases htzero : t = 0
          · simpa [htzero] using hpos
          · have h0t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
            have hsub : Set.Icc 0 t ⊆ I := by
              intro s hs
              exact hsegment ⟨hs.1, le_trans hs.2 htt.le⟩
            have harea : ∀ s ∈ Set.Icc 0 t, 0 < signedDoubleArea (z s).1 := by
              intro s hs
              exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 htt⟩
            exact (classicalNewton_sideGap_positive_on_Icc i hsol hconn h0t
              hsub hrest hcenter hpos harea) t ⟨le_of_lt h0t, le_rfl⟩
      exact Or.inl ⟨hpos, hstrict⟩
    · have hneg : sideGap (z 0).1 i < 0 := by
        have hle : sideGap (z 0).1 i ≤ 0 := le_of_not_gt hpos
        exact lt_of_le_of_ne hle hgapMiddle
      have hstrict : sideGap (z t).1 i < 0 := by
        by_cases hteq : t = T
        · subst t
          exact classicalNewton_sideGap_neg_at_regular_syzygy_of_neg
            i hsol hconn hTpos hsegment hrest hcenter hneg hareaPre hsyzygy
        · have htt : t < T := lt_of_le_of_ne ht.2 hteq
          by_cases htzero : t = 0
          · simpa [htzero] using hneg
          · have h0t : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
            have hsub : Set.Icc 0 t ⊆ I := by
              intro s hs
              exact hsegment ⟨hs.1, le_trans hs.2 htt.le⟩
            have harea : ∀ s ∈ Set.Icc 0 t, 0 < signedDoubleArea (z s).1 := by
              intro s hs
              exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 htt⟩
            exact (classicalNewton_sideGap_negative_on_Icc i hsol hconn h0t
              hsub hrest hcenter hneg harea) t ⟨le_of_lt h0t, le_rfl⟩
      exact Or.inr ⟨hneg, hstrict⟩
  constructor
  · rw [sideGap_eq_next_sub_prev_sideSq] at hgapN
    have hgapN' : sideSq (z t).1 (cyclicPrev i) - sideSq (z t).1 i < 0 := by
      simpa [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] using hgapN
    linarith
  · constructor
    · rw [sideGap_eq_next_sub_prev_sideSq] at hgapP
      have hgapP' : 0 < sideSq (z t).1 i - sideSq (z t).1 (cyclicNext i) := by
        simpa [cyclicNext_cyclicPrev, cyclicPrev_cyclicPrev] using hgapP
      linarith
    · exact hgapM

/-- Centered positive-orientation Paper Q2 certificate, including the strict
side ordering at every time in the closed interval through the same first
regular syzygy. -/
theorem exists_completePaperQ2_centered_positive
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : 0 < signedDoubleArea z₀.1)
    (i : Fin 3)
    (hscalene : sideSq z₀.1 (cyclicPrev i) ≠ sideSq z₀.1 (cyclicNext i))
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ (z : ℝ → Phase) (I : Set ℝ) (T : ℝ),
      ClassicalNewtonSolution z I ∧ z 0 = z₀ ∧ 0 ∈ I ∧ T ∈ I ∧
      FirstRegularSyzygy z I 0 T ∧
      Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i) ((z T).1 (cyclicNext i)) ∧
      (∀ t ∈ Set.Icc 0 T,
        sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
        sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
        ((0 < sideGap z₀.1 i ∧ 0 < sideGap (z t).1 i) ∨
          (sideGap z₀.1 i < 0 ∧ sideGap (z t).1 i < 0))) ∧
      (∀ j k, sideSq z₀.1 j < sideSq z₀.1 k →
        ∀ t ∈ Set.Icc 0 T, sideSq (z t).1 j < sideSq (z t).1 k) := by
  obtain ⟨T, hTD, hTpos, hsyzygy, hareaPre⟩ :=
    maximalNewtonUnion_exists_first_syzygy_of_strictLongest
      z₀ hcf hrest hcenter harea₀ i hlongPrev hlongNext
  let z := maximalNewtonUnionTrajectory z₀
  let D := maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := maximalNewtonUnionTrajectory_solution z₀
  have hconn : IsPreconnected D := isPreconnected_maximalNewtonUnionDomain z₀
  have hinit : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  have hzero : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hsegment : Set.Icc 0 T ⊆ D := hconn.Icc_subset hzero hTD
  have hlongPrevDist :
      dist (z₀.1 (cyclicPrev i)) (z₀.1 (cyclicNext i)) ^ 2 ≥
        dist (z₀.1 i) (z₀.1 (cyclicPrev i)) ^ 2 := by
    have hfirst := sideSq_eq_cyclicNeighborDistance z₀.1 i
    have hsecond : sideSq z₀.1 (cyclicNext i) =
        dist (z₀.1 i) (z₀.1 (cyclicPrev i)) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      simp [cyclicPrev_cyclicNext, cyclicNext_cyclicNext]
    rw [← hfirst, ← hsecond]
    exact le_of_lt hlongNext
  have hlongNextDist :
      dist (z₀.1 (cyclicPrev i)) (z₀.1 (cyclicNext i)) ^ 2 ≥
        dist (z₀.1 (cyclicNext i)) (z₀.1 i) ^ 2 := by
    have hfirst := sideSq_eq_cyclicNeighborDistance z₀.1 i
    have hsecond : sideSq z₀.1 (cyclicPrev i) =
        dist (z₀.1 (cyclicNext i)) (z₀.1 i) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      simp [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev]
    rw [← hfirst, ← hsecond]
    exact le_of_lt hlongPrev
  have hrest0 : ∀ b, (z 0).2 b = 0 := by simpa [z, hinit] using hrest
  have hcenter0 : (z 0).1 0 + (z 0).1 1 + (z 0).1 2 = 0 := by
    simpa [z, hinit] using hcenter
  have hlongPrevDist0 :
      dist ((z 0).1 (cyclicPrev i)) ((z 0).1 (cyclicNext i)) ^ 2 ≥
        dist ((z 0).1 i) ((z 0).1 (cyclicPrev i)) ^ 2 := by
    simpa [z, hinit] using hlongPrevDist
  have hlongNextDist0 :
      dist ((z 0).1 (cyclicPrev i)) ((z 0).1 (cyclicNext i)) ^ 2 ≥
        dist ((z 0).1 (cyclicNext i)) ((z 0).1 i) ^ 2 := by
    simpa [z, hinit] using hlongNextDist
  have hbetween := classicalNewton_body_between_sbtw_at_regular_syzygy_of_initial_longest
    i hsol hconn hTpos hsegment hrest0 hcenter0 hlongPrevDist0 hlongNextDist0
      hareaPre hsyzygy
  have hcfT : CollisionFree (z T).1 :=
    (hsol.2 T (hsegment ⟨le_of_lt hTpos, le_rfl⟩)).1
  have hfirst : FirstRegularSyzygy z D 0 T := by
    refine ⟨hTpos, hsegment, hsyzygy, ?_, hcfT⟩
    intro t ht
    exact ne_of_gt (hareaPre t ht)
  have hgapPrev : 0 < sideGap z₀.1 (cyclicPrev i) := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    simpa [cyclicNext_cyclicPrev, cyclicPrev_cyclicPrev] using
      (sub_pos.mpr hlongNext)
  have hgapNext : sideGap z₀.1 (cyclicNext i) < 0 := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    simpa [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] using
      (sub_neg.mpr hlongPrev)
  have hgapMiddle0 : sideGap z₀.1 i ≠ 0 := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    exact sub_ne_zero.mpr (Ne.symm hscalene)
  have hgapMiddleAt0 : sideGap (z 0).1 i ≠ 0 := by
    simpa [hinit] using hgapMiddle0
  have hordersFull := classicalNewton_strictLongestSide_on_Icc_of_firstSyzygy
    i hsol hconn hTpos hsegment hrest0 hcenter0
    (by simpa [hinit] using hgapPrev) (by simpa [hinit] using hgapNext)
    hgapMiddleAt0 hareaPre hsyzygy
  have horders : ∀ t ∈ Set.Icc 0 T,
      sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
      sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
      ((0 < sideGap z₀.1 i ∧ 0 < sideGap (z t).1 i) ∨
        (sideGap z₀.1 i < 0 ∧ sideGap (z t).1 i < 0)) := by
    intro t ht
    simpa [hinit] using hordersFull t ht
  have hshort : ∀ t ∈ Set.Icc 0 T,
      ((0 < sideGap z₀.1 i ∧ 0 < sideGap (z t).1 i) ∨
        (sideGap z₀.1 i < 0 ∧ sideGap (z t).1 i < 0)) := by
    intro t ht
    simpa [hinit] using (hordersFull t ht).2.2
  have hpairwise : ∀ j k, sideSq z₀.1 j < sideSq z₀.1 k →
      ∀ t ∈ Set.Icc 0 T, sideSq (z t).1 j < sideSq (z t).1 k := by
    intro j k hjk t ht
    have hlong := (horders t ht).1
    have hshort' := hshort t ht
    rcases hshort' with hshort' | hshort'
    · rcases hshort' with ⟨hgap0, hgapT⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp_all [cyclicPrev, cyclicNext, sideGap_eq_next_sub_prev_sideSq] <;> linarith
    · rcases hshort' with ⟨hgap0, hgapT⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp_all [cyclicPrev, cyclicNext, sideGap_eq_next_sub_prev_sideSq] <;> linarith
  exact ⟨z, D, T, hsol, hinit, hzero, hTD, hfirst, hbetween, horders, hpairwise⟩

/-- A common positive mass rescales the gravitational constant by that mass. -/
theorem generalAcceleration_commonMass_eq_effectiveGravity
    (G μ : ℝ) (q : Fin 3 → Point) (i : Fin 3) :
    generalAcceleration G (fun _ : Fin 3 => μ) q i =
      generalAcceleration (G * μ) (fun _ : Fin 3 => (1 : ℝ)) q i := by
  rw [generalAcceleration_equalMass_eq_scalar_unit]
  fin_cases i <;>
    simp [generalAcceleration, unitAcceleration, inverseCubeDistance,
      Fin.sum_univ_succ] <;> module

theorem generalNewtonField_commonMass_eq_effectiveGravity
    (G μ : ℝ) (z : Phase) :
    generalNewtonField G (fun _ : Fin 3 => μ) z =
      generalNewtonField (G * μ) (fun _ : Fin 3 => (1 : ℝ)) z := by
  apply Prod.ext
  · rfl
  · funext i
    exact generalAcceleration_commonMass_eq_effectiveGravity G μ z.1 i

/-- Complete centered-positive Paper Q2 result for any positive common mass
and gravitational constant. Time is rescaled by `sqrt (G*μ)`; the first-event
certificate and both strict side comparisons are preserved on the same event
interval. -/
theorem exists_completePaperQ2_commonMass_centered_positive
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ)
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : 0 < signedDoubleArea z₀.1)
    (i : Fin 3)
    (hscalene : sideSq z₀.1 (cyclicPrev i) ≠ sideSq z₀.1 (cyclicNext i))
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ (z : ℝ → Phase) (I : Set ℝ) (T : ℝ),
      GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ) z I ∧
      z 0 = z₀ ∧ 0 ∈ I ∧ T ∈ I ∧ FirstRegularSyzygy z I 0 T ∧
      Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i) ((z T).1 (cyclicNext i)) ∧
      (∀ t ∈ Set.Icc 0 T,
        sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
        sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
        ((0 < sideGap z₀.1 i ∧ 0 < sideGap (z t).1 i) ∨
          (sideGap z₀.1 i < 0 ∧ sideGap (z t).1 i < 0))) ∧
      (∀ j k, sideSq z₀.1 j < sideSq z₀.1 k →
        ∀ t ∈ Set.Icc 0 T, sideSq (z t).1 j < sideSq (z t).1 k) := by
  obtain ⟨zU, IU, TU, hsolU, hinitU, hzeroU, hTdomainU, hfirstU,
    hbetweenU, hordersU, hpairwiseU⟩ :=
    exists_completePaperQ2_centered_positive z₀ hcf hrest hcenter harea₀ i
      hscalene hlongPrev hlongNext
  let κ := Real.sqrt (G * μ)
  have hκpos : 0 < κ := Real.sqrt_pos.2 (mul_pos hG hμ)
  have hκsq : κ ^ 2 = G * μ := Real.sq_sqrt (le_of_lt (mul_pos hG hμ))
  let z := gravityRescaledTrajectory κ zU
  let I := gravityRescaledDomain κ IU
  let T := TU / κ
  have htime : κ * T = TU := by
    dsimp [T]
    field_simp [ne_of_gt hκpos]
  have hsolEff := classicalNewtonSolution_timeRescale κ hsolU
  have hsolEff' : GeneralClassicalNewtonSolution (G * μ)
      (fun _ : Fin 3 => (1 : ℝ))
      (gravityRescaledTrajectory κ zU) (gravityRescaledDomain κ IU) := by
    simpa [hκsq] using hsolEff
  have hsolMass : GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ) z I := by
    change GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ)
      (gravityRescaledTrajectory κ zU) (gravityRescaledDomain κ IU)
    refine ⟨hsolEff'.1, ?_⟩
    intro t ht
    obtain ⟨hcfT, hderiv⟩ := hsolEff'.2 t ht
    refine ⟨hcfT, ?_⟩
    rw [generalNewtonField_commonMass_eq_effectiveGravity]
    exact hderiv
  have hzeroTime : κ * 0 = 0 := by ring
  have hzeroI : (0 : ℝ) ∈ I := by
    change κ * 0 ∈ IU
    rw [hzeroTime]
    exact hzeroU
  have hTmem : T ∈ I := by
    change κ * T ∈ IU
    rw [htime]
    exact hTdomainU
  have hTpos : 0 < T := div_pos (by
    rcases hfirstU with ⟨hTUpos, _, _, _, _⟩
    exact hTUpos) hκpos
  have hinit : z 0 = z₀ := by
    change timeScalePhase κ (zU (κ * 0)) = z₀
    rw [mul_zero, hinitU]
    apply Prod.ext
    · rfl
    · funext j
      simp [timeScalePhase, hrest j]
  have hfirst : FirstRegularSyzygy z I 0 T := by
    rcases hfirstU with ⟨hTUpos, hsegmentU, hzeroAreaU, hpreU, hcfU⟩
    have hsegment : Set.Icc 0 T ⊆ I := by
      intro t ht
      change κ * t ∈ IU
      have hscaled : κ * t ∈ Set.Icc 0 TU := by
        constructor
        · exact mul_nonneg (le_of_lt hκpos) ht.1
        · calc
            κ * t ≤ κ * T := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hκpos)
            _ = TU := htime
      exact hsegmentU hscaled
    have hareaZero : signedDoubleArea (z T).1 = 0 := by
      simpa [z, gravityRescaledTrajectory, timeScalePhase, htime] using hzeroAreaU
    have hareaPre : ∀ t ∈ Set.Ico 0 T, signedDoubleArea (z t).1 ≠ 0 := by
      intro t ht hzero
      have hscaled : κ * t ∈ Set.Ico 0 TU := by
        constructor
        · exact mul_nonneg (le_of_lt hκpos) ht.1
        · calc
            κ * t < κ * T := mul_lt_mul_of_pos_left ht.2 hκpos
            _ = TU := htime
      apply hpreU (κ * t) hscaled
      simpa [z, gravityRescaledTrajectory, timeScalePhase] using hzero
    have hcfEnd : CollisionFree (z T).1 := by
      simpa [z, gravityRescaledTrajectory, timeScalePhase, htime] using hcfU
    exact ⟨hTpos, hsegment, hareaZero, hareaPre, hcfEnd⟩
  have hbetween : Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i)
      ((z T).1 (cyclicNext i)) := by
    simpa [z, gravityRescaledTrajectory, timeScalePhase, htime] using hbetweenU
  have horders : ∀ t ∈ Set.Icc 0 T,
      sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
      sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
      ((0 < sideGap z₀.1 i ∧ 0 < sideGap (z t).1 i) ∨
        (sideGap z₀.1 i < 0 ∧ sideGap (z t).1 i < 0)) := by
    intro t ht
    have hscaled : κ * t ∈ Set.Icc 0 TU := by
      constructor
      · exact mul_nonneg (le_of_lt hκpos) ht.1
      · calc
          κ * t ≤ κ * T := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hκpos)
          _ = TU := htime
    simpa [z, gravityRescaledTrajectory, timeScalePhase] using hordersU (κ * t) hscaled
  have hpairwise : ∀ j k, sideSq z₀.1 j < sideSq z₀.1 k →
      ∀ t ∈ Set.Icc 0 T, sideSq (z t).1 j < sideSq (z t).1 k := by
    intro j k hjk t ht
    have hscaled : κ * t ∈ Set.Icc 0 TU := by
      constructor
      · exact mul_nonneg (le_of_lt hκpos) ht.1
      · calc
          κ * t ≤ κ * T := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hκpos)
          _ = TU := htime
    simpa [z, gravityRescaledTrajectory, timeScalePhase] using hpairwiseU j k hjk (κ * t) hscaled
  exact ⟨z, I, T, hsolMass, hinit, hzeroI, hTmem, hfirst, hbetween,
    horders, hpairwise⟩

end

end DroppingThreeBodies
