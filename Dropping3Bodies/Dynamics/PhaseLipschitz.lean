module

public import Dropping3Bodies.Dynamics.Newton
public import Dropping3Bodies.Dynamics.Energy
public import Dropping3Bodies.Dynamics.RegularDomain
public import Dropping3Bodies.Support.CollisionBarrier
public import Dropping3Bodies.Support.IntervalEndpoint
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Lipschitz bounds for classical Newton trajectories

This module turns a uniform bound on the Newton phase field into a uniform
Lipschitz bound on a compact time interval. Deriving the field bound from
energy and the collision barrier is a separate estimate.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

/-- A single inverse-cube Newton force term has norm equal to the inverse
    square of the pair distance. -/
theorem inverseCubeForceTerm_norm_eq_inv_dist_sq
    (q : Fin 3 → Point) (i j : Fin 3) (hij : i ≠ j)
    (hcollision : CollisionFree q) :
    ‖inverseCubeDistance q i j • (q j - q i)‖ =
      (dist (q i) (q j) ^ 2)⁻¹ := by
  have hd : 0 < dist (q i) (q j) := by
    exact dist_pos.mpr (hcollision i j hij)
  have hforcepos : 0 < inverseCubeDistance q i j := by
    rw [inverseCubeDistance_eq_inv_distance_cube]
    positivity
  have hnorm : ‖q j - q i‖ = dist (q i) (q j) := by
    rw [dist_eq_norm, norm_sub_rev]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hforcepos,
    inverseCubeDistance_eq_inv_distance_cube, hnorm]
  field_simp [ne_of_gt hd]

/-- If every pair is at least `δ` apart, each body's total acceleration is
    at most the sum of its two inverse-square force bounds. -/
theorem unitAcceleration_norm_le_of_distance_lower_bound
    (q : Fin 3 → Point) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ j k : Fin 3, j ≠ k → δ ≤ dist (q j) (q k))
    (i : Fin 3) : ‖unitAcceleration q i‖ ≤ 2 / δ ^ 2 := by
  have hcf : CollisionFree q := by
    intro j k hjk hEq
    have h := hsep j k hjk
    rw [hEq, dist_self] at h
    linarith
  have hterm (j : Fin 3) (hij : i ≠ j) :
      ‖inverseCubeDistance q i j • (q j - q i)‖ ≤ (δ ^ 2)⁻¹ := by
    rw [inverseCubeForceTerm_norm_eq_inv_dist_sq q i j hij hcf]
    have hdist := hsep i j hij
    have hsquares : δ ^ 2 ≤ dist (q i) (q j) ^ 2 := by
      nlinarith [sq_nonneg (dist (q i) (q j) - δ)]
    have hinv := one_div_le_one_div_of_le (sq_pos_of_pos hδ) hsquares
    simpa [one_div] using hinv
  fin_cases i
  · change ‖inverseCubeDistance q 0 1 • (q 1 - q 0) +
      inverseCubeDistance q 0 2 • (q 2 - q 0)‖ ≤ 2 / δ ^ 2
    calc
      ‖inverseCubeDistance q 0 1 • (q 1 - q 0) +
          inverseCubeDistance q 0 2 • (q 2 - q 0)‖ ≤
        ‖inverseCubeDistance q 0 1 • (q 1 - q 0)‖ +
          ‖inverseCubeDistance q 0 2 • (q 2 - q 0)‖ := norm_add_le _ _
      _ ≤ (δ ^ 2)⁻¹ + (δ ^ 2)⁻¹ :=
        add_le_add (hterm 1 (by decide)) (hterm 2 (by decide))
      _ = 2 / δ ^ 2 := by ring

  · change ‖inverseCubeDistance q 1 0 • (q 0 - q 1) +
      inverseCubeDistance q 1 2 • (q 2 - q 1)‖ ≤ 2 / δ ^ 2
    calc
      ‖inverseCubeDistance q 1 0 • (q 0 - q 1) +
          inverseCubeDistance q 1 2 • (q 2 - q 1)‖ ≤
        ‖inverseCubeDistance q 1 0 • (q 0 - q 1)‖ +
          ‖inverseCubeDistance q 1 2 • (q 2 - q 1)‖ := norm_add_le _ _
      _ ≤ (δ ^ 2)⁻¹ + (δ ^ 2)⁻¹ :=
        add_le_add (hterm 0 (by decide)) (hterm 2 (by decide))
      _ = 2 / δ ^ 2 := by ring
  · change ‖inverseCubeDistance q 2 0 • (q 0 - q 2) +
      inverseCubeDistance q 2 1 • (q 1 - q 2)‖ ≤ 2 / δ ^ 2
    calc
      ‖inverseCubeDistance q 2 0 • (q 0 - q 2) +
          inverseCubeDistance q 2 1 • (q 1 - q 2)‖ ≤
        ‖inverseCubeDistance q 2 0 • (q 0 - q 2)‖ +
          ‖inverseCubeDistance q 2 1 • (q 1 - q 2)‖ := norm_add_le _ _
      _ ≤ (δ ^ 2)⁻¹ + (δ ^ 2)⁻¹ :=
        add_le_add (hterm 0 (by decide)) (hterm 1 (by decide))
      _ = 2 / δ ^ 2 := by ring

/-- The phase-space Newton field is bounded by the larger of a velocity
    bound and the uniform inverse-square acceleration bound. -/
theorem unitNewtonField_norm_le_of_velocity_and_distance_bounds
    (q v : Fin 3 → Point) {δ V : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V)
    (hsep : ∀ j k : Fin 3, j ≠ k → δ ≤ dist (q j) (q k))
    (hvel : ∀ i, ‖v i‖ ≤ V) :
    ‖unitNewtonField (q, v)‖ ≤ max V (2 / δ ^ 2) := by
  have hvconf : ‖v‖ ≤ V :=
    (pi_norm_le_iff_of_nonneg hV).2 hvel
  have hacc : ∀ i, ‖unitAcceleration q i‖ ≤ 2 / δ ^ 2 := by
    intro i
    exact unitAcceleration_norm_le_of_distance_lower_bound q hδ hsep i
  have hacconf : ‖fun i => unitAcceleration q i‖ ≤ 2 / δ ^ 2 :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 hacc
  change max ‖v‖ ‖fun i => unitAcceleration q i‖ ≤ max V (2 / δ ^ 2)
  exact max_le_max hvconf hacconf

/-- A convenient NNReal constant for the energy and force contribution to the
    Newton phase-field norm. -/
noncomputable def newtonPhaseFieldBound (δ : ℝ) : NNReal :=
  ⟨max (Real.sqrt (6 / δ)) (2 / δ ^ 2), by positivity⟩

/-- Energy and a pair-distance lower bound give a uniform Newton phase-field
    bound on a compact interval for a solution starting from rest. -/
theorem classicalNewton_uniform_phaseField_bound_of_distance_lower_bound
    {z : ℝ → Phase} {I : Set ℝ} {a T δ : ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    (hsegment : Set.Icc a T ⊆ I) (haT : a ≤ T)
    (hrest : ∀ i, (z a).2 i = 0) (hδ : 0 < δ)
    (hsep : ∀ t ∈ Set.Icc a T, ∀ j k : Fin 3, j ≠ k →
      δ ≤ dist ((z t).1 j) ((z t).1 k)) :
    ∀ t ∈ Set.Icc a T,
      ‖unitNewtonField (z t)‖₊ ≤ newtonPhaseFieldBound δ := by
  intro t ht
  have hkin := kineticEnergy_le_three_div_of_initial_rest hsol hconn
    (hsegment ⟨le_rfl, haT⟩) (hsegment ht) hδ hrest
    (hsep t ht 0 1 (by decide)) (hsep t ht 0 2 (by decide))
    (hsep t ht 1 2 (by decide))
  have hsum : ∑ i : Fin 3, ‖(z t).2 i‖ ^ 2 ≤ 6 / δ := by
    change (1 / 2 : ℝ) *
      (∑ i : Fin 3, ‖(z t).2 i‖ ^ 2) ≤ 3 / δ at hkin
    calc
      ∑ i : Fin 3, ‖(z t).2 i‖ ^ 2 =
          2 * ((1 / 2 : ℝ) * ∑ i : Fin 3, ‖(z t).2 i‖ ^ 2) := by ring
      _ ≤ 2 * (3 / δ) :=
        mul_le_mul_of_nonneg_left hkin (by norm_num)
      _ = 6 / δ := by ring
  have hvel : ∀ i : Fin 3, ‖(z t).2 i‖ ≤ Real.sqrt (6 / δ) := by
    intro i
    have hsingle : ‖(z t).2 i‖ ^ 2 ≤
        ∑ j : Fin 3, ‖(z t).2 j‖ ^ 2 :=
      Finset.single_le_sum (fun j hj => sq_nonneg (‖(z t).2 j‖))
        (Finset.mem_univ i)
    have hsqrt : 0 ≤ 6 / δ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    nlinarith [Real.sq_sqrt hsqrt]
  have hfield := unitNewtonField_norm_le_of_velocity_and_distance_bounds
    (z t).1 (z t).2 hδ (Real.sqrt_nonneg _)
    (hsep t ht) hvel
  apply NNReal.coe_le_coe.mp
  change ‖unitNewtonField (z t)‖ ≤ max (Real.sqrt (6 / δ)) (2 / δ ^ 2)
  exact hfield

/-- A uniform bound on the Newton phase-field derivative makes a given
    classical trajectory Lipschitz on a compact interval. -/
theorem classicalNewton_phase_lipschitzOnWith_of_field_bound
    {z : ℝ → Phase} {I : Set ℝ} {a T : ℝ} {K : NNReal}
    (hsol : ClassicalNewtonSolution z I)
    (hsegment : Set.Icc a T ⊆ I)
    (hbound : ∀ t ∈ Set.Icc a T, ‖unitNewtonField (z t)‖₊ ≤ K) :
    LipschitzOnWith K z (Set.Icc a T) := by
  exact Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun t ht => (hsol.2 t (hsegment ht)).2.differentiableAt)
    (fun t ht => by
      rw [(hsol.2 t (hsegment ht)).2.deriv]
      exact hbound t ht)
    (convex_Icc a T)

/-- The equal-mass collision barrier and rest-energy estimate provide an
    actual Lipschitz constant for every compact positive-area segment whose
    initial opposite side is uniquely longest. -/
theorem classicalNewton_phase_lipschitzOnWith_of_initial_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∃ K : NNReal, LipschitzOnWith K z (Set.Icc a T) := by
  obtain ⟨δ, hδ, hsep⟩ :=
    classicalNewton_uniform_pair_distance_barrier_of_initial_strictLongest
      i hsol hconn haT hsegment hrest hcenter hlongPrev hlongNext harea
  refine ⟨newtonPhaseFieldBound δ, ?_⟩
  apply classicalNewton_phase_lipschitzOnWith_of_field_bound hsol hsegment
  exact classicalNewton_uniform_phaseField_bound_of_distance_lower_bound
    hsol hconn hsegment (le_of_lt haT) hrest hδ hsep

/-- The global equal-mass collision barrier gives one Lipschitz constant on
    the whole rightward positive-area interval, even when its finite right
    endpoint is not assumed to have positive area. -/
theorem classicalNewton_phase_lipschitzOnWith_of_global_positiveArea_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t₀ T : ℝ} (hat₀ : a < t₀)
    (hsegment₀ : Set.Icc a t₀ ⊆ I)
    (hsegment : ∀ {t}, t ∈ I → a ≤ t → Set.Icc a t ⊆ I)
    (hright : ∀ t ∈ Set.Ico a T, t ∈ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ I, a ≤ t → 0 < signedDoubleArea (z t).1) :
    ∃ K : NNReal, LipschitzOnWith K z (Set.Ico a T) := by
  obtain ⟨δ, hδ, hsep⟩ :=
    classicalNewton_global_uniform_pair_distance_barrier_of_initial_strictLongest
      i hsol hconn hat₀ hsegment₀ hsegment hrest hcenter
      hlongPrev hlongNext harea
  refine ⟨newtonPhaseFieldBound δ, ?_⟩
  intro x hx y hy
  let s := max x y
  have hs : s ∈ Set.Ico a T := by
    constructor
    · exact le_trans hx.1 (le_max_left x y)
    · exact max_lt hx.2 hy.2
  have hIs : s ∈ I := hright s hs
  have hsegS : Set.Icc a s ⊆ I := hsegment hIs hs.1
  have hsepS : ∀ t ∈ Set.Icc a s, ∀ j k : Fin 3, j ≠ k →
      δ ≤ dist ((z t).1 j) ((z t).1 k) := by
    intro t ht j k hjk
    exact hsep t (hsegS ht) ht.1 j k hjk
  have hfield := classicalNewton_uniform_phaseField_bound_of_distance_lower_bound
    hsol hconn hsegS hs.1 hrest hδ hsepS
  have hLip := classicalNewton_phase_lipschitzOnWith_of_field_bound
    hsol hsegS hfield
  have hxS : x ∈ Set.Icc a s :=
    ⟨hx.1, le_max_left x y⟩
  have hyS : y ∈ Set.Icc a s :=
    ⟨hy.1, le_max_right x y⟩
  exact hLip hxS hyS

/-- The pair-distance lower bound on a left interval persists at the limit
    phase. This is the endpoint regularity needed to start a local Newton
    solution there without a binary collision. -/
theorem left_limit_preserves_pairwise_distance_lower_bound
    {z : ℝ → Phase} {zT : Phase} {a T δ : ℝ}
    (haT : a < T)
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT))
    (hsep : ∀ t ∈ Set.Ico a T, ∀ j k : Fin 3, j ≠ k →
      δ ≤ dist ((z t).1 j) ((z t).1 k)) :
    ∀ j k : Fin 3, j ≠ k → δ ≤ dist (zT.1 j) (zT.1 k) := by
  have haEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T), t ∈ Set.Ioi a := by
    exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio T))
      (Ioi_mem_nhds haT)
  intro j k hjk
  have hdist : Continuous fun w : Phase => dist (w.1 j) (w.1 k) := by
    exact continuous_dist.comp₂
      ((continuous_apply j).comp continuous_fst)
      ((continuous_apply k).comp continuous_fst)
  have hdistLim : Tendsto (fun t => dist ((z t).1 j) ((z t).1 k))
      (nhdsWithin T (Set.Iio T)) (𝓝 (dist (zT.1 j) (zT.1 k))) := by
    exact hdist.continuousAt.tendsto.comp hlim
  have hsepEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T),
      dist ((z t).1 j) ((z t).1 k) ∈ Set.Ici δ := by
    filter_upwards [haEvent, self_mem_nhdsWithin] with t hta ht
    exact hsep t ⟨le_of_lt hta, ht⟩ j k hjk
  have hclosed : IsClosed (Set.Ici δ) := isClosed_Ici
  have hmem : dist (zT.1 j) (zT.1 k) ∈ Set.Ici δ :=
    hclosed.mem_of_tendsto hdistLim hsepEvent
  exact hmem

/-- A nonnegative oriented area along a left-hand phase curve remains
    nonnegative at its phase limit. The area is a polynomial in the phase
    coordinates, hence continuous. -/
theorem left_limit_preserves_signedDoubleArea_nonneg
    {z : ℝ → Phase} {zT : Phase} {T a : ℝ} (haT : a < T)
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT))
    (harea : ∀ t ∈ Set.Ico a T, 0 ≤ signedDoubleArea (z t).1) :
    0 ≤ signedDoubleArea zT.1 := by
  have hareaContinuous : Continuous fun w : Phase => signedDoubleArea w.1 := by
    unfold signedDoubleArea cross
    fun_prop
  have hareaLim : Tendsto (fun t => signedDoubleArea (z t).1)
      (nhdsWithin T (Set.Iio T)) (𝓝 (signedDoubleArea zT.1)) :=
    hareaContinuous.continuousAt.tendsto.comp hlim
  have haEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T), t ∈ Set.Ioi a := by
    exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio T))
      (Ioi_mem_nhds haT)
  have hareaEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T),
      signedDoubleArea (z t).1 ∈ Set.Ici 0 := by
    filter_upwards [haEvent, self_mem_nhdsWithin] with t hta ht
    exact harea t ⟨le_of_lt hta, ht⟩
  exact isClosed_Ici.mem_of_tendsto hareaLim hareaEvent

/-- A classical equal-mass Newton solution with initially strict longest
    opposite side has a left phase limit at every finite endpoint of a
    compact positive-area segment. -/
theorem classicalNewton_phase_left_limit_of_initial_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∃ zT : Phase,
      Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT) := by
  obtain ⟨K, hLip⟩ := classicalNewton_phase_lipschitzOnWith_of_initial_strictLongest
    i hsol hconn haT hsegment hrest hcenter hlongPrev hlongNext harea
  apply exists_left_limit_of_lipschitzOnWith_finiteDimensional haT
  exact hLip.mono (by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩)

/-- The phase limit above is collision-free: the equal-mass collision barrier
    supplies a uniform positive lower bound for all pair distances, and
    continuity carries it to the endpoint. -/
theorem classicalNewton_phase_left_limit_collisionFree_of_initial_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∃ zT : Phase,
      Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT) ∧ CollisionFree zT.1 := by
  obtain ⟨δ, hδ, hsep⟩ :=
    classicalNewton_uniform_pair_distance_barrier_of_initial_strictLongest
      i hsol hconn haT hsegment hrest hcenter hlongPrev hlongNext harea
  obtain ⟨zT, hlim⟩ := classicalNewton_phase_left_limit_of_initial_strictLongest
    i hsol hconn haT hsegment hrest hcenter hlongPrev hlongNext harea
  refine ⟨zT, hlim, ?_⟩
  intro j k hjk heq
  have hdist := left_limit_preserves_pairwise_distance_lower_bound haT hlim
    (fun t ht l m hlm => hsep t ⟨ht.1, le_of_lt ht.2⟩ l m hlm) j k hjk
  rw [heq, dist_self] at hdist
  exact (not_le_of_gt hδ) hdist

/-- On the rightward positive-area part of a solution domain, an initially
    strict longest side gives a finite-endpoint phase limit that remains
    collision-free, without assuming positive area at that endpoint. -/
theorem classicalNewton_phase_left_limit_collisionFree_of_global_positiveArea_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t₀ T : ℝ} (haT : a < T) (hat₀ : a < t₀)
    (hsegment₀ : Set.Icc a t₀ ⊆ I)
    (hsegment : ∀ {t}, t ∈ I → a ≤ t → Set.Icc a t ⊆ I)
    (hright : ∀ t ∈ Set.Ico a T, t ∈ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (harea : ∀ t ∈ I, a ≤ t → 0 < signedDoubleArea (z t).1) :
    ∃ zT : Phase,
      Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT) ∧
        CollisionFree zT.1 ∧ 0 ≤ signedDoubleArea zT.1 := by
  obtain ⟨δ, hδ, hsep⟩ :=
    classicalNewton_global_uniform_pair_distance_barrier_of_initial_strictLongest
      i hsol hconn hat₀ hsegment₀ hsegment hrest hcenter
      hlongPrev hlongNext harea
  obtain ⟨K, hLip⟩ :=
    classicalNewton_phase_lipschitzOnWith_of_global_positiveArea_strictLongest
      i hsol hconn hat₀ hsegment₀ hsegment hright hrest hcenter
      hlongPrev hlongNext harea
  obtain ⟨zT, hlim⟩ := exists_left_limit_of_lipschitzOnWith_finiteDimensional
    haT hLip
  refine ⟨zT, hlim, ?_, ?_⟩
  ·
    intro j k hjk heq
    have hdist := left_limit_preserves_pairwise_distance_lower_bound haT hlim
      (fun t ht l m hlm => hsep t (hright t ht) ht.1 l m hlm) j k hjk
    rw [heq, dist_self] at hdist
    exact (not_le_of_gt hδ) hdist
  · apply left_limit_preserves_signedDoubleArea_nonneg haT hlim
    intro t ht
    exact le_of_lt (harea t (hright t ht) ht.1)

/-- Complete the old Newton trajectory by its left phase limit. The field
    values converge by continuity on the collision-free phase domain, so
    Mathlib's one-sided derivative extension theorem supplies the derivative
    at the endpoint. This is the calculus bridge needed for backward ODE
    uniqueness when the endpoint is outside the old solution domain.
    Mathlib source: `Mathlib/Analysis/Calculus/FDeriv/Extend.lean`,
    `hasDerivWithinAt_Iic_of_tendsto_deriv`. -/
theorem classicalNewton_left_extension_hasDerivWithinAt_of_phase_left_limit
    {z : ℝ → Phase} {I : Set ℝ} {zT : Phase} {a T : ℝ}
    (haT : a < T)
    (hsol : ClassicalNewtonSolution z I)
    (hright : ∀ t ∈ Set.Ico a T, t ∈ I)
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT))
    (hcf : CollisionFree zT.1) :
    HasDerivWithinAt (fun t => if t < T then z t else zT)
      (unitNewtonField zT) (Set.Iic T) T := by
  let zExt : ℝ → Phase := fun t => if t < T then z t else zT
  have hEqEvent : zExt =ᶠ[nhdsWithin T (Set.Iio T)] z := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t < T := ht
    simp [zExt, ht']
  have hExtLim : Tendsto zExt (nhdsWithin T (Set.Iio T)) (𝓝 zT) :=
    hlim.congr' hEqEvent.symm
  have hExtCont : ContinuousWithinAt zExt (Set.Ico a T) T := by
    rw [continuousWithinAt_Ico_iff_Iio haT]
    change Tendsto zExt (nhdsWithin T (Set.Iio T)) (𝓝 (zExt T))
    simpa [zExt] using hExtLim
  have hfieldCont : ContinuousAt unitNewtonField zT :=
    (unitNewtonField_contDiffAt zT hcf).continuousAt
  have hfieldLim : Tendsto (fun t => unitNewtonField (z t))
      (nhdsWithin T (Set.Iio T)) (𝓝 (unitNewtonField zT)) :=
    hfieldCont.tendsto.comp hlim
  have hderivEq : ∀ᶠ t in nhdsWithin T (Set.Iio T),
      deriv zExt t = unitNewtonField (z t) := by
    have haEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T), t ∈ Set.Ioi a := by
      exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio T))
        (Ioi_mem_nhds haT)
    filter_upwards [haEvent, self_mem_nhdsWithin] with t hta ht
    have htI : t ∈ I := hright t ⟨le_of_lt hta, ht⟩
    have hD : HasDerivAt z (unitNewtonField (z t)) t := (hsol.2 t htI).2
    have hlocalEq : zExt =ᶠ[𝓝 t] z := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have hs' : s < T := hs
      simp [zExt, hs']
    have hDExt : HasDerivAt zExt (unitNewtonField (z t)) t :=
      hD.congr_of_eventuallyEq hlocalEq
    exact hDExt.deriv
  have hderivFunctionEq : (fun t => deriv zExt t) =ᶠ[nhdsWithin T (Set.Iio T)]
      (fun t => unitNewtonField (z t)) := by
    filter_upwards [hderivEq] with t ht
    exact ht
  have hderivLim : Tendsto (fun t => deriv zExt t)
      (nhdsWithin T (Set.Iio T)) (𝓝 (unitNewtonField zT)) :=
    hfieldLim.congr' hderivFunctionEq.symm
  have hdiff : DifferentiableOn ℝ zExt (Set.Ico a T) := by
    intro t ht
    have htI : t ∈ I := hright t ht
    have hD : HasDerivAt z (unitNewtonField (z t)) t := (hsol.2 t htI).2
    have hlocalEq : zExt =ᶠ[𝓝 t] z := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      have hs' : s < T := hs
      simp [zExt, hs']
    exact (hD.congr_of_eventuallyEq hlocalEq).differentiableAt.differentiableWithinAt
  have hs := Ico_mem_nhdsLT haT
  exact hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hExtCont hs hderivLim

end DroppingThreeBodies
