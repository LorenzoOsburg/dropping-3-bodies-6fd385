module

public import Dropping3Bodies.Dynamics.RegularDomain
public import Dropping3Bodies.Dynamics.PhaseExtension
public import Dropping3Bodies.Dynamics.PhaseLipschitz
public import Dropping3Bodies.Dynamics.SyzygyQuantitative
public import Dropping3Bodies.Support.FirstZero
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Maximal solution from the union of all local intervals

For a fixed collision-free initial phase at time zero, consider all classical
Newton solutions on open intervals `(a,b)` with `a < 0 < b`. Local uniqueness
on preconnected overlaps makes this family compatible. The pointwise union
construction below defines one classical solution on the union of all such
intervals, with no symmetry restriction on either endpoint.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- A local classical solution on an open interval containing the initial
    time zero and taking a fixed value there. -/
structure NewtonInitialIntervalWitness (z₀ : Phase) where
  left : ℝ
  right : ℝ
  trajectory : ℝ → Phase
  left_lt_zero : left < 0
  zero_lt_right : 0 < right
  initial : trajectory 0 = z₀
  solution : ClassicalNewtonSolution trajectory (Set.Ioo left right)

/-- The union of every open interval on which the same initial phase has a
    classical collision-free Newton solution. -/
def maximalNewtonUnionDomain (z₀ : Phase) : Set ℝ :=
  ⋃₀ {s : Set ℝ | ∃ w : NewtonInitialIntervalWitness z₀,
    s = Set.Ioo w.left w.right}

/-- Local Picard existence supplies an interval witness around time zero. -/
theorem exists_newtonInitialIntervalWitness (z₀ : Phase)
    (hcf : CollisionFree z₀.1) : Nonempty (NewtonInitialIntervalWitness z₀) := by
  obtain ⟨ε, hε, z, hz₀, hsol⟩ := exists_local_classicalNewtonSolution z₀ hcf
  exact ⟨⟨-ε, ε, z, neg_neg_of_pos hε, hε, hz₀, hsol⟩⟩

/-- The union of all witness intervals is open. -/
theorem isOpen_maximalNewtonUnionDomain (z₀ : Phase) :
    IsOpen (maximalNewtonUnionDomain z₀) := by
  unfold maximalNewtonUnionDomain
  apply isOpen_sUnion
  rintro s ⟨w, rfl⟩
  exact isOpen_Ioo

/-- All witness intervals contain zero, so their union is preconnected. -/
theorem isPreconnected_maximalNewtonUnionDomain (z₀ : Phase) :
    IsPreconnected (maximalNewtonUnionDomain z₀) := by
  unfold maximalNewtonUnionDomain
  apply isPreconnected_sUnion 0
  · rintro s ⟨w, rfl⟩
    exact ⟨w.left_lt_zero, w.zero_lt_right⟩
  · rintro s ⟨w, rfl⟩
    exact isPreconnected_Ioo

/-- Every point of the union is covered by a witness interval. -/
theorem maximalNewtonUnionDomain_covered (z₀ : Phase) {t : ℝ}
    (ht : t ∈ maximalNewtonUnionDomain z₀) :
    ∃ w : NewtonInitialIntervalWitness z₀,
      t ∈ Set.Ioo w.left w.right := by
  rcases Set.mem_sUnion.mp ht with ⟨s, hs, ht⟩
  rcases hs with ⟨w, rfl⟩
  exact ⟨w, ht⟩

/-- Choose a local witness at each point of the union domain. -/
noncomputable def maximalNewtonChosenWitness (z₀ : Phase) (t : ℝ)
    (ht : t ∈ maximalNewtonUnionDomain z₀) : NewtonInitialIntervalWitness z₀ :=
  Classical.choose (maximalNewtonUnionDomain_covered z₀ ht)

theorem maximalNewtonChosenWitness_spec (z₀ : Phase) (t : ℝ)
    (ht : t ∈ maximalNewtonUnionDomain z₀) :
    t ∈ Set.Ioo (maximalNewtonChosenWitness z₀ t ht).left
        (maximalNewtonChosenWitness z₀ t ht).right :=
  Classical.choose_spec (maximalNewtonUnionDomain_covered z₀ ht)

/-- The pointwise choice of local trajectories on the union domain. -/
noncomputable def maximalNewtonUnionTrajectory (z₀ : Phase) (t : ℝ) : Phase := by
  classical
  exact if ht : t ∈ maximalNewtonUnionDomain z₀ then
    (maximalNewtonChosenWitness z₀ t ht).trajectory t
  else z₀

/-- Intersections of two real open intervals are convex, hence preconnected. -/
theorem isPreconnected_inter_openIntervals (a b c d : ℝ) :
    IsPreconnected (Set.Ioo a b ∩ Set.Ioo c d) := by
  exact (Convex.inter (convex_Ioo a b) (convex_Ioo c d)).isPreconnected

/-- Near any time in the union, its selected trajectory agrees with a fixed
    local solution covering that time. -/
theorem maximalNewtonUnionTrajectory_eventuallyEq_chosen (z₀ : Phase) (t : ℝ)
    (ht : t ∈ maximalNewtonUnionDomain z₀) :
    maximalNewtonUnionTrajectory z₀ =ᶠ[𝓝 t]
      (maximalNewtonChosenWitness z₀ t ht).trajectory := by
  let w := maximalNewtonChosenWitness z₀ t ht
  have htW := maximalNewtonChosenWitness_spec z₀ t ht
  have hDopen := isOpen_maximalNewtonUnionDomain z₀
  have htD : maximalNewtonUnionDomain z₀ ∈ 𝓝 t := hDopen.mem_nhds ht
  have htWnhds : Set.Ioo w.left w.right ∈ 𝓝 t := isOpen_Ioo.mem_nhds htW
  filter_upwards [htD, htWnhds] with s hsD hsW
  let v := maximalNewtonChosenWitness z₀ s hsD
  have hsV := maximalNewtonChosenWitness_spec z₀ s hsD
  have hvSol := v.solution
  have hwSol := w.solution
  have hinit : w.trajectory 0 = v.trajectory 0 := w.initial.trans v.initial.symm
  have hzero : (0 : ℝ) ∈ Set.Ioo w.left w.right ∩ Set.Ioo v.left v.right :=
    ⟨⟨w.left_lt_zero, w.zero_lt_right⟩,
      ⟨v.left_lt_zero, v.zero_lt_right⟩⟩
  have hoverlap := classicalNewton_eq_on_of_preconnected_overlap
    hwSol hvSol (isPreconnected_inter_openIntervals w.left w.right v.left v.right)
    hzero hinit
  have hsOverlap : s ∈ Set.Ioo w.left w.right ∩ Set.Ioo v.left v.right :=
    ⟨hsW, hsV⟩
  have heq := hoverlap s hsOverlap
  have htrajectory : maximalNewtonUnionTrajectory z₀ s = v.trajectory s := by
    unfold maximalNewtonUnionTrajectory
    rw [dif_pos hsD]
  rw [htrajectory, heq]

/-- The union trajectory is a classical collision-free Newton solution on the
    entire union domain. -/
theorem maximalNewtonUnionTrajectory_solution (z₀ : Phase) :
    ClassicalNewtonSolution (maximalNewtonUnionTrajectory z₀)
      (maximalNewtonUnionDomain z₀) := by
  refine ⟨isOpen_maximalNewtonUnionDomain z₀, ?_⟩
  intro t ht
  let w := maximalNewtonChosenWitness z₀ t ht
  have htW := maximalNewtonChosenWitness_spec z₀ t ht
  have hcollision := (w.solution.2 t htW).1
  have hvalue : maximalNewtonUnionTrajectory z₀ t = w.trajectory t := by
    unfold maximalNewtonUnionTrajectory
    rw [dif_pos ht]
  constructor
  · rw [hvalue]
    exact hcollision
  · have hD := (w.solution.2 t htW).2
    have hevent := maximalNewtonUnionTrajectory_eventuallyEq_chosen z₀ t ht
    have hderiv := hD.congr_of_eventuallyEq hevent
    simpa [hvalue] using hderiv

/-- The union trajectory takes its prescribed initial phase at time zero. -/
theorem maximalNewtonUnionTrajectory_initial (z₀ : Phase)
    (hcf : CollisionFree z₀.1) :
    maximalNewtonUnionTrajectory z₀ 0 = z₀ := by
  obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
  have hzero : (0 : ℝ) ∈ Set.Ioo w.left w.right :=
    ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hzeroD : (0 : ℝ) ∈ maximalNewtonUnionDomain z₀ :=
    Set.mem_sUnion.mpr ⟨Set.Ioo w.left w.right, ⟨w, rfl⟩, hzero⟩
  have hchosen := maximalNewtonChosenWitness_spec z₀ 0 hzeroD
  have hval : maximalNewtonUnionTrajectory z₀ 0 =
      (maximalNewtonChosenWitness z₀ 0 hzeroD).trajectory 0 := by
    unfold maximalNewtonUnionTrajectory
    rw [dif_pos hzeroD]
  rw [hval]
  exact (maximalNewtonChosenWitness z₀ 0 hzeroD).initial

/-- Every local solution interval with the prescribed initial value is
    contained in the union domain; this is the domain-maximality property of
    the construction. -/
theorem maximalNewtonWitness_interval_subset (z₀ : Phase)
    (w : NewtonInitialIntervalWitness z₀) :
    Set.Ioo w.left w.right ⊆ maximalNewtonUnionDomain z₀ := by
  intro t ht
  exact Set.mem_sUnion.mpr ⟨Set.Ioo w.left w.right, ⟨w, rfl⟩, ht⟩

/-- The union domain cannot have a finite right endpoint with a
    collision-free phase limit. The endpoint gluing theorem would create a
    larger interval witness with the same initial phase. -/
theorem maximalNewtonUnion_finiteRightEndpoint_not_collisionFree
    (z₀ : Phase) {z : ℝ → Phase} {T a : ℝ} {zT : Phase}
    (hsol : ClassicalNewtonSolution z (maximalNewtonUnionDomain z₀))
    (hinit : z 0 = z₀)
    (ha0 : a < 0) (haT : a < T) (h0T : 0 < T)
    (hright : ∀ t ∈ Set.Ioo a T, t ∈ maximalNewtonUnionDomain z₀)
    (hupper : ∀ t ∈ maximalNewtonUnionDomain z₀, t ≤ T)
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT)) :
    ¬ CollisionFree zT.1 := by
  intro hcf
  obtain ⟨ρ, hρ, w, _, hnew, hagree⟩ :=
    classicalNewton_local_extension_of_phase_left_limit
      haT hsol hright hlim hcf
  have hnewInitial : w 0 = z₀ := by
    have hzero : (0 : ℝ) ∈ Set.Ioo a T := ⟨ha0, h0T⟩
    exact (hagree 0 hzero).trans hinit
  have hnewRight : 0 < T + ρ := by linarith
  let ext : NewtonInitialIntervalWitness z₀ :=
    ⟨a, T + ρ, w, ha0, hnewRight, hnewInitial, hnew⟩
  have hpoint : T + ρ / 2 ∈ Set.Ioo ext.left ext.right := by
    constructor
    · dsimp [ext]
      linarith
    · dsimp [ext]
      linarith
  have hdomain := maximalNewtonWitness_interval_subset z₀ ext hpoint
  have hbound := hupper (T + ρ / 2) hdomain
  linarith

/-- A maximal union trajectory cannot keep positive oriented area at every
    nonnegative time if the initial opposite side is strictly longest. The
    uniform angle-growth bound gives a finite right endpoint, while the global
    pair-distance barrier gives a collision-free endpoint limit; local ODE
    continuation then contradicts maximality of the union domain. -/
theorem maximalNewtonUnion_area_not_positive_forall_forward_of_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ¬ (∀ t ∈ maximalNewtonUnionDomain z₀, 0 ≤ t →
      0 < signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1) := by
  intro hpositive
  let z := maximalNewtonUnionTrajectory z₀
  let D := maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D :=
    maximalNewtonUnionTrajectory_solution z₀
  have hconn : IsPreconnected D := isPreconnected_maximalNewtonUnionDomain z₀
  have hinit : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
  let t₀ := w.right / 2
  let a := w.left / 2
  have ht₀pos : 0 < t₀ := by dsimp [t₀]; linarith [w.zero_lt_right]
  have hapos : a < 0 := by dsimp [a]; linarith [w.left_lt_zero]
  have hzeroD : (0 : ℝ) ∈ D := by
    have hzero : (0 : ℝ) ∈ Set.Ioo w.left w.right :=
      ⟨w.left_lt_zero, w.zero_lt_right⟩
    exact maximalNewtonWitness_interval_subset z₀ w hzero
  have ht₀D : t₀ ∈ D := by
    apply maximalNewtonWitness_interval_subset z₀ w
    constructor
    · dsimp [t₀]
      nlinarith [w.left_lt_zero, w.zero_lt_right]
    · dsimp [t₀]
      linarith [w.zero_lt_right]
  have haD : a ∈ D := by
    apply maximalNewtonWitness_interval_subset z₀ w
    constructor
    · dsimp [a]
      linarith [w.left_lt_zero]
    · dsimp [a]
      linarith [w.left_lt_zero, w.zero_lt_right]
  have hsegment0 : Set.Icc 0 t₀ ⊆ D := hconn.Icc_subset hzeroD ht₀D
  have hsegment : ∀ {t}, t ∈ D → 0 ≤ t → Set.Icc 0 t ⊆ D := by
    intro t ht ht0
    exact hconn.Icc_subset hzeroD ht
  have hrestZ : ∀ b, (z 0).2 b = 0 := by
    intro b
    rw [hinit]
    exact hrest b
  have hcenterZ : (z 0).1 0 + (z 0).1 1 + (z 0).1 2 = 0 := by
    rw [hinit]
    exact hcenter
  have hlongPrevZ : sideSq (z 0).1 i > sideSq (z 0).1 (cyclicPrev i) := by
    rw [hinit]
    exact hlongPrev
  have hlongNextZ : sideSq (z 0).1 i > sideSq (z 0).1 (cyclicNext i) := by
    rw [hinit]
    exact hlongNext
  have harea : ∀ t ∈ D, 0 ≤ t → 0 < signedDoubleArea (z t).1 :=
    fun t ht ht0 => hpositive t ht ht0
  obtain ⟨B, hB⟩ :=
    classicalNewton_positiveArea_branch_boundedAbove_of_initial_opposite_side_strictLongest
      i hsol hconn ht₀pos hsegment0 hsegment hrestZ hcenterZ
      hlongPrevZ hlongNextZ harea
  have hBdd : BddAbove D := by
    refine ⟨max 0 B, ?_⟩
    intro t ht
    by_cases ht0 : 0 ≤ t
    · exact le_trans (hB t ht ht0) (le_max_right 0 B)
    · exact le_trans (le_of_lt (lt_of_not_ge ht0)) (le_max_left 0 B)
  have hDne : D.Nonempty := ⟨0, hzeroD⟩
  let T := sSup D
  have hupper : ∀ t ∈ D, t ≤ T := fun t ht => le_csSup hBdd ht
  have h0T : 0 < T := by
    have ht₀T : t₀ ≤ T := le_csSup hBdd ht₀D
    dsimp [T]
    exact lt_of_lt_of_le ht₀pos ht₀T
  have hright0 : ∀ t ∈ Set.Ico 0 T, t ∈ D := by
    intro t ht
    obtain ⟨u, huD, htu⟩ := (lt_csSup_iff hBdd hDne).mp ht.2
    have hIcc := hconn.Icc_subset hzeroD huD
    exact hIcc ⟨ht.1, le_of_lt htu⟩
  obtain ⟨zT, hlim, hcfT, _⟩ :=
    classicalNewton_phase_left_limit_collisionFree_of_global_positiveArea_strictLongest
      i hsol hconn h0T ht₀pos hsegment0 hsegment hright0
      hrestZ hcenterZ hlongPrevZ hlongNextZ harea
  have hright : ∀ t ∈ Set.Ioo a T, t ∈ D := by
    intro t ht
    by_cases ht0 : 0 ≤ t
    · obtain ⟨u, huD, htu⟩ := (lt_csSup_iff hBdd hDne).mp ht.2
      have hIcc := hconn.Icc_subset hzeroD huD
      exact hIcc ⟨ht0, le_of_lt htu⟩
    · have hIcc := hconn.Icc_subset haD hzeroD
      exact hIcc ⟨le_of_lt ht.1, le_of_lt (lt_of_not_ge ht0)⟩
  have hTmax : ¬ CollisionFree zT.1 :=
    maximalNewtonUnion_finiteRightEndpoint_not_collisionFree z₀ hsol hinit
      hapos (by dsimp [T]; exact lt_trans hapos h0T) h0T hright hupper hlim
  exact hTmax hcfT

/-- Under the same equal-mass strict-longest hypotheses, some nonnegative
    time in the maximal union domain has nonpositive oriented area. -/
theorem maximalNewtonUnion_exists_nonpositiveAreaTime_of_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ t ∈ maximalNewtonUnionDomain z₀, 0 ≤ t ∧
      signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 ≤ 0 := by
  have hnot := maximalNewtonUnion_area_not_positive_forall_forward_of_strictLongest
    z₀ hcf hrest hcenter i hlongPrev hlongNext
  by_contra hex
  apply hnot
  intro t ht ht0
  by_contra hpos
  have harea : signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 ≤ 0 :=
    le_of_not_gt hpos
  exact hex ⟨t, ht, ht0, harea⟩

/-- The nonpositive-area time is strictly after the initial time because the
    initial triangle is nondegenerate and positively oriented. -/
theorem maximalNewtonUnion_exists_positiveTime_area_nonpositive_of_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : 0 < signedDoubleArea z₀.1)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ t ∈ maximalNewtonUnionDomain z₀, 0 < t ∧
      signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 ≤ 0 := by
  obtain ⟨t, ht, ht0, harea⟩ :=
    maximalNewtonUnion_exists_nonpositiveAreaTime_of_strictLongest
      z₀ hcf hrest hcenter i hlongPrev hlongNext
  have hinit := maximalNewtonUnionTrajectory_initial z₀ hcf
  have htne : t ≠ 0 := by
    intro heq
    subst t
    rw [hinit] at harea
    linarith
  exact ⟨t, ht, lt_of_le_of_ne ht0 (Ne.symm htne), harea⟩

/-- A positively oriented nondegenerate initial triangle with a strict
    longest opposite side has a finite positive time of collinearity on the
    maximal regular Newton solution. -/
theorem maximalNewtonUnion_exists_syzygy_of_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : 0 < signedDoubleArea z₀.1)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ t ∈ maximalNewtonUnionDomain z₀, 0 < t ∧
      signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 = 0 := by
  obtain ⟨t, htD, htpos, hareaT⟩ :=
    maximalNewtonUnion_exists_positiveTime_area_nonpositive_of_strictLongest
      z₀ hcf hrest hcenter harea₀ i hlongPrev hlongNext
  let z := maximalNewtonUnionTrajectory z₀
  let D := maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := maximalNewtonUnionTrajectory_solution z₀
  have hconn : IsPreconnected D := isPreconnected_maximalNewtonUnionDomain z₀
  have hinit : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  have hzeroD : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hsegment : Set.Icc 0 t ⊆ D := hconn.Icc_subset hzeroD htD
  let A : ℝ → ℝ := fun s => signedDoubleArea (z s).1
  have hphaseCont : ContinuousOn z (Set.Icc 0 t) := by
    intro s hs
    exact (hsol.2 s (hsegment hs)).2.continuousAt.continuousWithinAt
  have hareaField : Continuous (fun q : Phase => signedDoubleArea q.1) := by
    unfold signedDoubleArea cross
    fun_prop
  have hAcont : ContinuousOn A (Set.Icc 0 t) := by
    dsimp [A]
    exact hareaField.continuousOn.comp hphaseCont (by
      intro s hs
      exact Set.mem_univ (z s))
  have hzeroBetween : (0 : ℝ) ∈ Set.Icc (A t) (A 0) := by
    constructor
    · exact hareaT
    · dsimp [A]
      rw [hinit]
      exact le_of_lt harea₀
  have himage : (0 : ℝ) ∈ A '' Set.Icc 0 t :=
    (intermediate_value_Icc' (le_of_lt htpos) hAcont) hzeroBetween
  rcases himage with ⟨s, hs, hAs⟩
  have hsne : s ≠ 0 := by
    intro heq
    subst s
    dsimp [A] at hAs
    rw [hinit] at hAs
    linarith
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsne)
  refine ⟨s, hsegment hs, hspos, ?_⟩
  exact hAs

/-- Select the first positive syzygy time on the maximal regular solution.
    The area is strictly positive at every earlier time. -/
theorem maximalNewtonUnion_exists_first_syzygy_of_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : 0 < signedDoubleArea z₀.1)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ T ∈ maximalNewtonUnionDomain z₀, 0 < T ∧
      signedDoubleArea (maximalNewtonUnionTrajectory z₀ T).1 = 0 ∧
      ∀ t ∈ Set.Ico 0 T,
        0 < signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 := by
  obtain ⟨s, hsD, hspos, hAs⟩ :=
    maximalNewtonUnion_exists_syzygy_of_strictLongest
      z₀ hcf hrest hcenter harea₀ i hlongPrev hlongNext
  let z := maximalNewtonUnionTrajectory z₀
  let D := maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := maximalNewtonUnionTrajectory_solution z₀
  have hconn : IsPreconnected D := isPreconnected_maximalNewtonUnionDomain z₀
  have hinit : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  have hzeroD : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hsegment : Set.Icc 0 s ⊆ D := hconn.Icc_subset hzeroD hsD
  let A : ℝ → ℝ := fun t => signedDoubleArea (z t).1
  have hAcont : ContinuousOn A (Set.Icc 0 s) := by
    have hphaseCont : ContinuousOn z (Set.Icc 0 s) := by
      intro t ht
      exact (hsol.2 t (hsegment ht)).2.continuousAt.continuousWithinAt
    have hareaField : Continuous (fun q : Phase => signedDoubleArea q.1) := by
      unfold signedDoubleArea cross
      fun_prop
    dsimp [A]
    exact hareaField.continuousOn.comp hphaseCont (by
      intro t ht
      exact Set.mem_univ (z t))
  have hAstart : 0 < A 0 := by
    dsimp [A]
    rw [hinit]
    exact harea₀
  have hAend : A s = 0 := by
    dsimp [A]
    exact hAs
  obtain ⟨T, hTinterval, hTpos, hAT, hbefore⟩ :=
    exists_first_zero_Icc A s hspos hAcont hAstart hAend
  exact ⟨T, hsegment hTinterval, hTpos, hAT, hbefore⟩

/-- The regular first syzygy of a strict-longest-side rest start places the
    body opposite that side strictly between the other two. -/
theorem maximalNewtonUnion_body_between_at_first_syzygy_of_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : 0 < signedDoubleArea z₀.1)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ T ∈ maximalNewtonUnionDomain z₀, 0 < T ∧
      Sbtw ℝ ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i))
        ((maximalNewtonUnionTrajectory z₀ T).1 i)
        ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i)) := by
  obtain ⟨T, hTD, hTpos, hsyzygy, hareaPre⟩ :=
    maximalNewtonUnion_exists_first_syzygy_of_strictLongest
      z₀ hcf hrest hcenter harea₀ i hlongPrev hlongNext
  let z := maximalNewtonUnionTrajectory z₀
  let D := maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := maximalNewtonUnionTrajectory_solution z₀
  have hconn : IsPreconnected D := isPreconnected_maximalNewtonUnionDomain z₀
  have hinit : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  have hsegment : Set.Icc 0 T ⊆ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    have hzero : (0 : ℝ) ∈ D := maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
    exact hconn.Icc_subset hzero hTD
  have hlongPrevDistance :
      dist (z₀.1 (cyclicPrev i)) (z₀.1 (cyclicNext i)) ^ 2 ≥
        dist (z₀.1 i) (z₀.1 (cyclicPrev i)) ^ 2 := by
    have hfirst := sideSq_eq_cyclicNeighborDistance z₀.1 i
    have hsecond : sideSq z₀.1 (cyclicNext i) =
        dist (z₀.1 i) (z₀.1 (cyclicPrev i)) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      simp [cyclicPrev_cyclicNext, cyclicNext_cyclicNext]
    rw [← hfirst, ← hsecond]
    exact le_of_lt hlongNext
  have hlongNextDistance :
      dist (z₀.1 (cyclicPrev i)) (z₀.1 (cyclicNext i)) ^ 2 ≥
        dist (z₀.1 (cyclicNext i)) (z₀.1 i) ^ 2 := by
    have hfirst := sideSq_eq_cyclicNeighborDistance z₀.1 i
    have hsecond : sideSq z₀.1 (cyclicPrev i) =
        dist (z₀.1 (cyclicNext i)) (z₀.1 i) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      simp [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev]
    rw [← hfirst, ← hsecond]
    exact le_of_lt hlongPrev
  have hrest0 : ∀ b, (z 0).2 b = 0 := by
    simpa [z, hinit] using hrest
  have hcenter0 : (z 0).1 0 + (z 0).1 1 + (z 0).1 2 = 0 := by
    simpa [z, hinit] using hcenter
  have hlongPrevDistance0 :
      dist ((z 0).1 (cyclicPrev i)) ((z 0).1 (cyclicNext i)) ^ 2 ≥
        dist ((z 0).1 i) ((z 0).1 (cyclicPrev i)) ^ 2 := by
    simpa [z, hinit] using hlongPrevDistance
  have hlongNextDistance0 :
      dist ((z 0).1 (cyclicPrev i)) ((z 0).1 (cyclicNext i)) ^ 2 ≥
        dist ((z 0).1 (cyclicNext i)) ((z 0).1 i) ^ 2 := by
    simpa [z, hinit] using hlongNextDistance
  have hbetween := classicalNewton_body_between_sbtw_at_regular_syzygy_of_initial_longest
    i hsol hconn hTpos hsegment hrest0 hcenter0 hlongPrevDistance0 hlongNextDistance0
    hareaPre hsyzygy
  exact ⟨T, hTD, hTpos, hbetween⟩

end

end DroppingThreeBodies
