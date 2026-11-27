module

public import Mathlib.Tactic
public import Dropping3Bodies.Dynamics.Energy
public import Dropping3Bodies.EqualMass.SolutionSideOrdering

@[expose] public section

/-! Algebraic estimate used in the equal-mass distance barrier. -/

namespace DroppingThreeBodies

/-- On a compact interval where a classical solution remains collision-free,
    each fixed pair distance has a strictly positive minimum. This supplies
    the short initial segment omitted by the later rotation barrier. -/
theorem exists_positive_uniform_pair_distance
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I)
    {a b : ℝ} (hab : a ≤ b) (hsegment : Set.Icc a b ⊆ I)
    (j k : Fin 3) (hjk : j ≠ k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc a b,
      δ ≤ dist ((z t).1 j) ((z t).1 k) := by
  have hphase : ContinuousOn z (Set.Icc a b) :=
    classicalNewton_continuousOn_phase hsol hsegment
  have hdistFun : Continuous fun p : Phase => dist (p.1 j) (p.1 k) := by
    fun_prop
  have hdist : ContinuousOn (fun t => dist ((z t).1 j) ((z t).1 k))
      (Set.Icc a b) := by
    exact hdistFun.continuousOn.comp hphase (by intro t ht; exact Set.mem_univ _)
  obtain ⟨tmin, htmin, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hab) hdist
  have hminPos : 0 < dist ((z tmin).1 j) ((z tmin).1 k) :=
    dist_pos.mpr ((hsol.2 tmin (hsegment htmin)).1 j k hjk)
  refine ⟨dist ((z tmin).1 j) ((z tmin).1 k), hminPos, ?_⟩
  intro t ht
  exact hmin ht

/-- Squared-side comparisons for a shortest side imply the corresponding
    distance comparison against every unordered pair of distinct bodies. -/
theorem shortest_sideSq_le_all_pair_distances
    (q : Fin 3 → Point) (i : Fin 3)
    (hshortest : sideSq q i ≤ sideSq q (cyclicPrev i) ∧
      sideSq q i ≤ sideSq q (cyclicNext i)) :
    ∀ j k : Fin 3, j ≠ k →
      dist (q (cyclicPrev i)) (q (cyclicNext i)) ≤ dist (q j) (q k) := by
  intro j k hjk
  have hsq :
      dist (q (cyclicPrev i)) (q (cyclicNext i)) ^ 2 ≤ dist (q j) (q k) ^ 2 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [sideSq, sideVector, cyclicPrev, cyclicNext, dist_comm,
        dist_eq_norm] <;>
      (have hn01 := congrArg (fun r : ℝ => r ^ 2) (norm_sub_rev (q 0) (q 1))
       have hn02 := congrArg (fun r : ℝ => r ^ 2) (norm_sub_rev (q 0) (q 2))
       have hn12 := congrArg (fun r : ℝ => r ^ 2) (norm_sub_rev (q 1) (q 2))
       nlinarith)
  have hleft : 0 ≤ dist (q (cyclicPrev i)) (q (cyclicNext i)) := dist_nonneg
  have hright : 0 ≤ dist (q j) (q k) := dist_nonneg
  exact (sq_le_sq₀ hleft hright).1 hsq

/-- If a shortest side `a` carries pair rotation of magnitude at least `k`,
    then the energy bound `Tkin ≤ 3/a` forces `a ≥ k²/12`. -/
theorem shortest_side_lower_bound_of_rotation
    {a k Tkin : ℝ}
    (ha : 0 < a)
    (hrotation : k ^ 2 ≤ 4 * a ^ 2 * Tkin)
    (henergy : Tkin ≤ 3 / a) :
    k ^ 2 / 12 ≤ a := by
  have hscale : 0 ≤ 4 * a ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left henergy hscale
  have hcalc : (3 / a) * (4 * a ^ 2) = 12 * a := by
    field_simp [ne_of_gt ha]
    ring
  rw [mul_comm (4 * a ^ 2) (3 / a)] at hmul
  rw [hcalc] at hmul
  nlinarith

/-- A side that is initially weakly shortest remains weakly shortest on a
    compact positive-area segment. Strict adjacent gaps use the cooperative
    sign theorems; a tied adjacent gap uses the already-proved uniqueness
    theorem for the zero solution of that cooperative pair. -/
theorem classicalNewton_initially_shortest_side_remains_shortest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hshortest₀ : sideSq (z a).1 i ≤ sideSq (z a).1 (cyclicPrev i) ∧
      sideSq (z a).1 i ≤ sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∀ t ∈ Set.Icc a T,
      sideSq (z t).1 i ≤ sideSq (z t).1 (cyclicPrev i) ∧
      sideSq (z t).1 i ≤ sideSq (z t).1 (cyclicNext i) := by
  have hgapPrev₀ : sideGap (z a).1 (cyclicPrev i) ≤ 0 := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    simpa [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev] using
      sub_nonpos.mpr hshortest₀.2
  have hgapNext₀ : 0 ≤ sideGap (z a).1 (cyclicNext i) := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    simpa [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] using
      sub_nonneg.mpr hshortest₀.1
  have hgapPrev : ∀ t ∈ Set.Icc a T, sideGap (z t).1 (cyclicPrev i) ≤ 0 := by
    intro t ht
    by_cases heq : sideGap (z a).1 (cyclicPrev i) = 0
    · have hzero := classicalNewton_sideGap_eq_zero_on_Icc_of_tie
        (cyclicPrev i) hsol hconn haT hsegment hrest hcenter heq harea
      rw [hzero t ht]
    · have hnegative : sideGap (z a).1 (cyclicPrev i) < 0 := by
        by_contra hnot
        exact heq (le_antisymm hgapPrev₀ (le_of_not_gt hnot))
      exact le_of_lt ((classicalNewton_sideGap_negative_on_Icc
        (cyclicPrev i) hsol hconn haT hsegment hrest hcenter hnegative harea) t ht)
  have hgapNext : ∀ t ∈ Set.Icc a T, 0 ≤ sideGap (z t).1 (cyclicNext i) := by
    intro t ht
    by_cases heq : sideGap (z a).1 (cyclicNext i) = 0
    · have hzero := classicalNewton_sideGap_eq_zero_on_Icc_of_tie
        (cyclicNext i) hsol hconn haT hsegment hrest hcenter heq harea
      rw [hzero t ht]
    · have hpositive : 0 < sideGap (z a).1 (cyclicNext i) := by
        by_contra hnot
        exact heq (le_antisymm (le_of_not_gt hnot) hgapNext₀)
      exact le_of_lt ((classicalNewton_sideGap_positive_on_Icc
        (cyclicNext i) hsol hconn haT hsegment hrest hcenter hpositive harea) t ht)
  intro t ht
  constructor
  · have hg := hgapNext t ht
    rw [sideGap_eq_next_sub_prev_sideSq] at hg
    simpa [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] using hg
  · have hg := hgapPrev t ht
    rw [sideGap_eq_next_sub_prev_sideSq] at hg
    simpa [cyclicNext_cyclicPrev, cyclicPrev_cyclicPrev] using hg

/-- Along an initial-rest Newton solution, a side whose rotation is already
    nonzero stays bounded away from zero as long as that side remains shortest.
    The statement is conditional on a positive-area interval; it does not
    construct a first syzygy. -/
theorem classicalNewton_shortest_side_distance_barrier
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a₀ T t₀ t : ℝ} (haT : a₀ < T) (ha₀t₀ : a₀ < t₀)
    (hsegment : Set.Icc a₀ T ⊆ I)
    (hrest : ∀ b, (z a₀).2 b = 0)
    (hcenter : (z a₀).1 0 + (z a₀).1 1 + (z a₀).1 2 = 0)
    (hgap : sideGap (z a₀).1 i ≠ 0)
    (harea : ∀ s ∈ Set.Icc a₀ T, 0 < signedDoubleArea (z s).1)
    (ht₀ : t₀ ∈ Set.Icc a₀ T) (ht : t ∈ Set.Icc a₀ T)
    (ht₀t : t₀ ≤ t)
    (hshortest : ∀ j k : Fin 3, j ≠ k →
      dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) ≤
        dist ((z t).1 j) ((z t).1 k)) :
    (let Y := fun s => if 0 < sideGap (z a₀).1 i then
      sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i s else
      -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i s
     Y t₀) ^ 2 / 12 ≤
      dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) := by
  let Y := fun s => if 0 < sideGap (z a₀).1 i then
    sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i s else
    -sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i s
  have hsegment0 : Set.Icc a₀ t₀ ⊆ I := by
    intro s hs
    exact hsegment ⟨hs.1, le_trans hs.2 ht₀.2⟩
  have harea0 : ∀ s ∈ Set.Icc a₀ t₀, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact harea s ⟨hs.1, le_trans hs.2 ht₀.2⟩
  have hY₀ : 0 < Y t₀ := by
    by_cases hpos : 0 < sideGap (z a₀).1 i
    · simpa [Y, hpos] using
        classicalNewton_orientedRotation_pos_of_nonzero_sideGap
          i hsol hconn ha₀t₀ hsegment0 hrest hcenter hgap harea0
    · have hneg := classicalNewton_orientedRotation_pos_of_nonzero_sideGap
        i hsol hconn ha₀t₀ hsegment0 hrest hcenter hgap harea0
      have hcurve : sideGapRotationSignCurve (solutionPositionCurve z)
          (solutionVelocityCurve z) i t₀ < 0 := by
        simpa [hpos] using hneg
      simpa [Y, hpos] using neg_pos.mpr hcurve
  have hYmono := classicalNewton_orientedRotation_nondecreasing_on_Icc
    i hsol hconn haT hsegment hrest hcenter hgap harea ht₀ ht ht₀t
  have hYt : 0 < Y t := lt_of_lt_of_le hY₀ hYmono
  have hYsq : Y t ^ 2 =
      cross (sideVector (z t).1 i) (sideVector (z t).2 i) ^ 2 := by
    by_cases hpos : 0 < sideGap (z a₀).1 i
    · simp [Y, hpos, sideGapRotationSignCurve, sidePairRotationCurve,
        sideVectorCurve, solutionPositionCurve, solutionVelocityCurve]
    · simp [Y, hpos, sideGapRotationSignCurve, sidePairRotationCurve,
        sideVectorCurve, solutionPositionCurve, solutionVelocityCurve]
  have hrotation := sidePairRotation_sq_le_four_sideSq_mul_kinetic
    (z t).1 (z t).2 i
  have hYkin : Y t ^ 2 ≤
      4 * sideSq (z t).1 i * kineticEnergy (z t).2 := by
    rw [hYsq]
    exact hrotation
  have h01 : dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) ≤
      dist ((z t).1 0) ((z t).1 1) := hshortest 0 1 (by decide)
  have h02 : dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) ≤
      dist ((z t).1 0) ((z t).1 2) := hshortest 0 2 (by decide)
  have h12 : dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) ≤
      dist ((z t).1 1) ((z t).1 2) := hshortest 1 2 (by decide)
  have henergy := kineticEnergy_le_three_div_of_initial_rest
    hsol hconn (hsegment ⟨le_rfl, haT.le⟩) (hsegment ht)
    (dist_pos.mpr ((hsol.2 t (hsegment ht)).1
      (cyclicPrev i) (cyclicNext i) (cyclicPrev_ne_cyclicNext i)))
    hrest h01 h02 h12
  have hside : sideSq (z t).1 i =
      dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) ^ 2 :=
    sideSq_eq_cyclicNeighborDistance (z t).1 i
  have hk0 : 0 ≤ Y t₀ := le_of_lt hY₀
  have hk : (Y t₀) ^ 2 ≤ (Y t) ^ 2 :=
    (sq_le_sq₀ hk0 (le_of_lt hYt)).2 hYmono
  have hrotSide : (Y t₀) ^ 2 ≤
      4 * dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) ^ 2 *
        kineticEnergy (z t).2 := by
    rw [hside] at hYkin
    exact le_trans hk hYkin
  simpa only [Y] using shortest_side_lower_bound_of_rotation
    (dist_pos.mpr ((hsol.2 t (hsegment ht)).1
      (cyclicPrev i) (cyclicNext i) (cyclicPrev_ne_cyclicNext i)))
    hrotSide henergy

/-- A fixed side that is initially shortest and has nonzero initial gap has
    a positive uniform lower bound throughout a compact positive-area segment.
    The initial compact part uses ordinary continuity; after `t₀` the rotation
    barrier applies because the side-order theorem keeps this side shortest. -/
theorem classicalNewton_uniform_shortest_side_distance_barrier
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T t₀ : ℝ} (haT : a < T) (hat₀ : a < t₀)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hshortest₀ : sideSq (z a).1 i ≤ sideSq (z a).1 (cyclicPrev i) ∧
      sideSq (z a).1 i ≤ sideSq (z a).1 (cyclicNext i))
    (hgap : sideGap (z a).1 i ≠ 0)
    (harea : ∀ s ∈ Set.Icc a T, 0 < signedDoubleArea (z s).1)
    (ht₀ : t₀ ∈ Set.Icc a T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc a T,
      δ ≤ dist ((z t).1 (cyclicPrev i)) ((z t).1 (cyclicNext i)) := by
  have hshortPersist := classicalNewton_initially_shortest_side_remains_shortest
    i hsol hconn haT hsegment hrest hcenter hshortest₀ harea
  obtain ⟨δ₀, hδ₀, hinitial⟩ := exists_positive_uniform_pair_distance
    hsol (a := a) (b := t₀) (le_of_lt hat₀)
    (fun s hs => hsegment ⟨hs.1, le_trans hs.2 ht₀.2⟩)
    (cyclicPrev i) (cyclicNext i) (cyclicPrev_ne_cyclicNext i)
  let Y := fun s => if 0 < sideGap (z a).1 i then
    sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i s else
    -sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i s
  have hY₀ : 0 < Y t₀ := by
    by_cases hpos : 0 < sideGap (z a).1 i
    · simpa [Y, hpos] using classicalNewton_orientedRotation_pos_of_nonzero_sideGap
        i hsol hconn hat₀
        (fun s hs => hsegment ⟨hs.1, le_trans hs.2 ht₀.2⟩)
        hrest hcenter hgap
        (fun s hs => harea s ⟨hs.1, le_trans hs.2 ht₀.2⟩)
    · have hneg := classicalNewton_orientedRotation_pos_of_nonzero_sideGap
        i hsol hconn hat₀
        (fun s hs => hsegment ⟨hs.1, le_trans hs.2 ht₀.2⟩)
        hrest hcenter hgap
        (fun s hs => harea s ⟨hs.1, le_trans hs.2 ht₀.2⟩)
      have hcurve : sideGapRotationSignCurve (solutionPositionCurve z)
          (solutionVelocityCurve z) i t₀ < 0 := by
        simpa [hpos] using hneg
      simpa [Y, hpos] using neg_pos.mpr hcurve
  let δ₁ : ℝ := Y t₀ ^ 2 / 12
  have hδ₁ : 0 < δ₁ := by positivity
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht
  by_cases hbefore : t ≤ t₀
  · exact le_trans (min_le_left _ _) (hinitial t ⟨ht.1, hbefore⟩)
  · have ht₀t : t₀ ≤ t := le_of_not_ge hbefore
    have ht₀Icc : t₀ ∈ Set.Icc a T := ⟨le_of_lt hat₀, ht₀.2⟩
    have hshortest := shortest_sideSq_le_all_pair_distances
      (z t).1 i (hshortPersist t ht)
    have hbarrier := classicalNewton_shortest_side_distance_barrier i
      hsol hconn haT hat₀ hsegment hrest hcenter hgap harea ht₀Icc ht ht₀t hshortest
    exact le_trans (min_le_right _ _) (by simpa [δ₁, Y] using hbarrier)

/-- On an entire positive-area part of a connected solution interval, an
    initially shortest side with nonzero gap gives one fixed positive lower
    bound for every pair distance. The compact initial segment supplies a
    bound up to a fixed `t₀`; after `t₀`, its oriented pair rotation and energy
    supply a time-independent bound. -/
theorem classicalNewton_global_uniform_pair_distance_barrier_of_shortest_nonzero_gap
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t₀ : ℝ} (hat₀ : a < t₀)
    (hsegment₀ : Set.Icc a t₀ ⊆ I)
    (hsegment : ∀ {t}, t ∈ I → a ≤ t → Set.Icc a t ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hshortest₀ : sideSq (z a).1 i ≤ sideSq (z a).1 (cyclicPrev i) ∧
      sideSq (z a).1 i ≤ sideSq (z a).1 (cyclicNext i))
    (hgap : sideGap (z a).1 i ≠ 0)
    (harea : ∀ t ∈ I, a ≤ t → 0 < signedDoubleArea (z t).1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ I, a ≤ t → ∀ j k : Fin 3, j ≠ k →
      δ ≤ dist ((z t).1 j) ((z t).1 k) := by
  have harea₀ : ∀ s ∈ Set.Icc a t₀, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact harea s (hsegment₀ hs) hs.1
  obtain ⟨δ₀, hδ₀, hinitial⟩ := exists_positive_uniform_pair_distance
    hsol (le_of_lt hat₀) hsegment₀ (cyclicPrev i) (cyclicNext i)
    (cyclicPrev_ne_cyclicNext i)
  let Y := fun s => if 0 < sideGap (z a).1 i then
    sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i s else
    -sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i s
  have hY₀ : 0 < Y t₀ := by
    by_cases hpos : 0 < sideGap (z a).1 i
    · simpa [Y, hpos] using
        classicalNewton_orientedRotation_pos_of_nonzero_sideGap
          i hsol hconn hat₀ hsegment₀ hrest hcenter hgap harea₀
    · have hrot := classicalNewton_orientedRotation_pos_of_nonzero_sideGap
        i hsol hconn hat₀ hsegment₀ hrest hcenter hgap harea₀
      have hnegative : sideGapRotationSignCurve (solutionPositionCurve z)
          (solutionVelocityCurve z) i t₀ < 0 := by
        simpa [hpos] using hrot
      simpa [Y, hpos] using neg_pos.mpr hnegative
  have hshortPersist₀ := classicalNewton_initially_shortest_side_remains_shortest
    i hsol hconn hat₀ hsegment₀ hrest hcenter hshortest₀ harea₀
  let δ₁ : ℝ := Y t₀ ^ 2 / 12
  have hδ₁ : 0 < δ₁ := by positivity
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht hat j k hjk
  have hsegmentT : Set.Icc a t ⊆ I := hsegment ht hat
  have hareaT : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact harea s (hsegmentT hs) hs.1
  by_cases hbefore : t ≤ t₀
  · have hshortest := shortest_sideSq_le_all_pair_distances (z t).1 i
      (hshortPersist₀ t ⟨hat, hbefore⟩)
    exact le_trans (min_le_left _ _)
      (le_trans (hinitial t ⟨hat, hbefore⟩) (hshortest j k hjk))
  · have ht₀t : t₀ ≤ t := le_of_not_ge hbefore
    have ht₀Icc : t₀ ∈ Set.Icc a t := ⟨le_of_lt hat₀, ht₀t⟩
    have hshortPersist := classicalNewton_initially_shortest_side_remains_shortest
      i hsol hconn (lt_of_lt_of_le hat₀ ht₀t) hsegmentT hrest hcenter
      hshortest₀ hareaT
    have hshortest := shortest_sideSq_le_all_pair_distances (z t).1 i
      (hshortPersist t ⟨hat, le_rfl⟩)
    have hbarrier := classicalNewton_shortest_side_distance_barrier i
      hsol hconn (lt_of_lt_of_le hat₀ ht₀t) hat₀ hsegmentT hrest hcenter
      hgap hareaT ht₀Icc ⟨hat, le_rfl⟩ ht₀t hshortest
    exact le_trans (min_le_right _ _) (by simpa [δ₁, Y] using hbarrier.trans (hshortest j k hjk))

/-- The strict-longest-side collision barrier is uniform over the entire
    rightward positive-area part of a connected solution domain. -/
theorem classicalNewton_global_uniform_pair_distance_barrier_of_initial_strictLongest
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
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ I, a ≤ t → ∀ j k : Fin 3, j ≠ k →
      δ ≤ dist ((z t).1 j) ((z t).1 k) := by
  let p := cyclicPrev i
  let n := cyclicNext i
  by_cases hpn : sideSq (z a).1 p ≤ sideSq (z a).1 n
  · have hshortest₀ : sideSq (z a).1 p ≤ sideSq (z a).1 (cyclicPrev p) ∧
        sideSq (z a).1 p ≤ sideSq (z a).1 (cyclicNext p) := by
      constructor
      · simpa [p, cyclicPrev_cyclicPrev] using hpn
      · simpa [p, cyclicNext_cyclicPrev] using hlongPrev.le
    have hgap : sideGap (z a).1 p ≠ 0 := by
      intro heq
      have hformula := sideGap_eq_next_sub_prev_sideSq (z a).1 p
      rw [cyclicNext_cyclicPrev, cyclicPrev_cyclicPrev] at hformula
      rw [hformula] at heq
      linarith [hlongNext]
    exact classicalNewton_global_uniform_pair_distance_barrier_of_shortest_nonzero_gap
      p hsol hconn hat₀ hsegment₀ hsegment hrest hcenter hshortest₀ hgap harea
  · have hnp : sideSq (z a).1 n ≤ sideSq (z a).1 p := le_of_lt (lt_of_not_ge hpn)
    have hshortest₀ : sideSq (z a).1 n ≤ sideSq (z a).1 (cyclicPrev n) ∧
        sideSq (z a).1 n ≤ sideSq (z a).1 (cyclicNext n) := by
      constructor
      · simpa [n, cyclicPrev_cyclicNext] using hlongNext.le
      · simpa [n, cyclicNext_cyclicNext] using hnp
    have hgap : sideGap (z a).1 n ≠ 0 := by
      intro heq
      have hformula := sideGap_eq_next_sub_prev_sideSq (z a).1 n
      rw [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] at hformula
      rw [hformula] at heq
      linarith [hlongPrev]
    exact classicalNewton_global_uniform_pair_distance_barrier_of_shortest_nonzero_gap
      n hsol hconn hat₀ hsegment₀ hsegment hrest hcenter hshortest₀ hgap harea

/-- An initially uniquely longest opposite side leaves a nonzero gap on each
    of its adjacent sides. Choose the shorter adjacent side and apply the
    existing rotation/energy barrier: all three pair distances then have a
    positive uniform lower bound on every compact positive-area segment.

    Source route: [DroppingMontgomery2026], frozen 2026-10-29,
    `sec:firstsyzygy`, `eq:distancebarrier`--`eq:deltabound`. The selection of
    the shortest side and the Lean proof are formalized here from the project's
    equal-mass ordering and energy lemmas. -/
theorem classicalNewton_uniform_pair_distance_barrier_of_initial_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Icc a T, ∀ j k : Fin 3, j ≠ k →
      δ ≤ dist ((z t).1 j) ((z t).1 k) := by
  let p := cyclicPrev i
  let n := cyclicNext i
  let t₀ := (a + T) / 2
  have hat₀ : a < t₀ := by dsimp [t₀]; linarith
  have ht₀T : t₀ < T := by dsimp [t₀]; linarith
  have ht₀ : t₀ ∈ Set.Icc a T := ⟨le_of_lt hat₀, le_of_lt ht₀T⟩
  by_cases hpn : sideSq (z a).1 p ≤ sideSq (z a).1 n
  · have hshortest₀ : sideSq (z a).1 p ≤ sideSq (z a).1 (cyclicPrev p) ∧
        sideSq (z a).1 p ≤ sideSq (z a).1 (cyclicNext p) := by
      constructor
      · simpa [p, cyclicPrev_cyclicPrev] using hpn
      · simpa [p, cyclicNext_cyclicPrev] using hlongPrev.le
    have hgap : sideGap (z a).1 p ≠ 0 := by
      intro heq
      have hformula := sideGap_eq_next_sub_prev_sideSq (z a).1 p
      rw [cyclicNext_cyclicPrev, cyclicPrev_cyclicPrev] at hformula
      rw [hformula] at heq
      linarith [hlongNext]
    have hshortest := classicalNewton_initially_shortest_side_remains_shortest
      p hsol hconn haT hsegment hrest hcenter hshortest₀ harea
    obtain ⟨δ, hδ, hbound⟩ := classicalNewton_uniform_shortest_side_distance_barrier
      p hsol hconn haT hat₀ hsegment hrest hcenter hshortest₀ hgap harea ht₀
    refine ⟨δ, hδ, ?_⟩
    intro t ht j k hjk
    have hmin := shortest_sideSq_le_all_pair_distances (z t).1 p
      (hshortest t ht)
    exact le_trans (hbound t ht) (hmin j k hjk)
  · have hnp : sideSq (z a).1 n ≤ sideSq (z a).1 p :=
      le_of_lt (lt_of_not_ge hpn)
    have hshortest₀ : sideSq (z a).1 n ≤ sideSq (z a).1 (cyclicPrev n) ∧
        sideSq (z a).1 n ≤ sideSq (z a).1 (cyclicNext n) := by
      constructor
      · simpa [n, cyclicPrev_cyclicNext] using hlongNext.le
      · simpa [n, cyclicNext_cyclicNext] using hnp
    have hgap : sideGap (z a).1 n ≠ 0 := by
      intro heq
      have hformula := sideGap_eq_next_sub_prev_sideSq (z a).1 n
      rw [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] at hformula
      rw [hformula] at heq
      linarith [hlongPrev]
    have hshortest := classicalNewton_initially_shortest_side_remains_shortest
      n hsol hconn haT hsegment hrest hcenter hshortest₀ harea
    obtain ⟨δ, hδ, hbound⟩ := classicalNewton_uniform_shortest_side_distance_barrier
      n hsol hconn haT hat₀ hsegment hrest hcenter hshortest₀ hgap harea ht₀
    refine ⟨δ, hδ, ?_⟩
    intro t ht j k hjk
    have hmin := shortest_sideSq_le_all_pair_distances (z t).1 n
      (hshortest t ht)
    exact le_trans (hbound t ht) (hmin j k hjk)

end DroppingThreeBodies
