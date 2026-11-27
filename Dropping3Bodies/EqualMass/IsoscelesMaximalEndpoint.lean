module

public import Dropping3Bodies.EqualMass.IsoscelesComparison
public import Dropping3Bodies.EqualMass.IsoscelesTrajectoryBootstrap
public import Dropping3Bodies.Dynamics.MaximalInterval
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite right endpoint for sufficiently tall isosceles rest data

The scalar comparison gives a uniform finite upper bound on the right extent
of the union of all regular Newton solution intervals. This module does not
yet classify the singular endpoint.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- A sufficiently tall equal-mass isosceles rest start cannot have a regular
    positive-base Newton solution interval reaching the comparison time. -/
theorem maximalNewtonUnionDomain_bddAbove_of_tall_isosceles
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀) (hH : 0 < v₀-u₀)
    (htall : (v₀-u₀)^3 > 96*x₀^3)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ∀ t ∈ maximalNewtonUnionDomain z₀, t < Real.sqrt (8*x₀^3) := by
  let T := Real.sqrt (8*x₀^3)
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hconn : IsPreconnected (maximalNewtonUnionDomain z₀) :=
    isPreconnected_maximalNewtonUnionDomain z₀
  have hzero : (0 : ℝ) ∈ maximalNewtonUnionDomain z₀ := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  intro t ht
  change t < T
  by_contra hnot
  have htT : T ≤ t := le_of_not_gt hnot
  have hsegmentT : Set.Icc 0 T ⊆ maximalNewtonUnionDomain z₀ := by
    have hseg := hconn.Icc_subset hzero ht
    intro s hs
    exact hseg ⟨hs.1, le_trans hs.2 htT⟩
  let z := maximalNewtonUnionTrajectory z₀
  have hsol : ClassicalNewtonSolution z (maximalNewtonUnionDomain z₀) :=
    maximalNewtonUnionTrajectory_solution z₀
  have hconn' : IsPreconnected (maximalNewtonUnionDomain z₀) := hconn
  have hz0 : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  have hstart' : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)) :=
    hz0.trans hstart
  have hfixed : isoscelesSymmetryPhase (z 0) = z 0 := by
    rw [hstart']
    exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
  have hSym : ∀ s ∈ Set.Icc 0 T,
      isoscelesSymmetryPhase (z s) = z s := by
    intro s hs
    exact classicalNewtonSolution_isoscelesSymmetric hsol hconn' hzero
      hfixed s (hsegmentT hs)
  have hx : ∀ s ∈ Set.Icc 0 T, 0 < isoscelesSolutionX z s :=
    classicalNewton_isosceles_base_half_positive_on_segment
      hsol hstart' hsegmentT hSym hx₀
  have himpossible := classicalNewton_isosceles_tall_rest_segment_impossible
    hsol hconn' hzero hstart' hsegmentT hx hx₀ hH htall (by rfl)
  exact himpossible

/-- The maximal regular Newton union for a sufficiently tall isosceles rest
    start has a positive finite right extent, at most the comparison time. -/
theorem maximalNewtonUnionDomain_positive_finite_rightExtent_of_tall_isosceles
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀) (hH : 0 < v₀-u₀)
    (htall : (v₀-u₀)^3 > 96*x₀^3)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    0 < sSup (maximalNewtonUnionDomain z₀) ∧
      sSup (maximalNewtonUnionDomain z₀) ≤ Real.sqrt (8*x₀^3) := by
  have hupper := maximalNewtonUnionDomain_bddAbove_of_tall_isosceles
    x₀ u₀ v₀ hx₀ hH htall z₀ hstart hcf
  have hbounded : BddAbove (maximalNewtonUnionDomain z₀) := by
    refine ⟨Real.sqrt (8*x₀^3), ?_⟩
    intro t ht
    exact le_of_lt (hupper t ht)
  have hnonempty : (maximalNewtonUnionDomain z₀).Nonempty := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact ⟨0, maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩⟩
  have hTpos : 0 < Real.sqrt (8*x₀^3) := by positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    have hrightD : w.right/2 ∈ maximalNewtonUnionDomain z₀ := by
      have : w.right/2 ∈ Set.Ioo w.left w.right := by
        constructor <;> linarith [w.left_lt_zero, w.zero_lt_right]
      exact maximalNewtonWitness_interval_subset z₀ w this
    have hhalf : 0 < w.right/2 := by linarith [w.zero_lt_right]
    have hle : w.right/2 ≤ sSup (maximalNewtonUnionDomain z₀) :=
      le_csSup hbounded hrightD
    exact lt_of_lt_of_le hhalf hle
  · exact csSup_le hnonempty (by
      intro t ht
      exact le_of_lt (hupper t ht))

end


/-- The maximal regular union has finite right extent for every equal-mass
    isosceles rest start with positive base half-length. Unlike the tall-data
    endpoint theorem above, this bound uses only the horizontal equation. -/
theorem maximalNewtonUnionDomain_bddAbove_of_isosceles_rest
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ∀ t ∈ maximalNewtonUnionDomain z₀,
      t < Real.sqrt (8*x₀^3) := by
  let T := Real.sqrt (8*x₀^3)
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hconn : IsPreconnected (maximalNewtonUnionDomain z₀) :=
    isPreconnected_maximalNewtonUnionDomain z₀
  have hzero : (0 : ℝ) ∈ maximalNewtonUnionDomain z₀ := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  intro t ht
  change t < T
  by_contra hnot
  have htT : T ≤ t := le_of_not_gt hnot
  have hsegmentT : Set.Icc 0 T ⊆ maximalNewtonUnionDomain z₀ := by
    have hseg := hconn.Icc_subset hzero ht
    intro s hs
    exact hseg ⟨hs.1, le_trans hs.2 htT⟩
  let z := maximalNewtonUnionTrajectory z₀
  have hsol : ClassicalNewtonSolution z (maximalNewtonUnionDomain z₀) :=
    maximalNewtonUnionTrajectory_solution z₀
  have hz0 : z 0 = z₀ := maximalNewtonUnionTrajectory_initial z₀ hcf
  have hstart' : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)) :=
    hz0.trans hstart
  have hfixed : isoscelesSymmetryPhase (z 0) = z 0 := by
    rw [hstart']
    exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
  have hSym : ∀ s ∈ Set.Icc 0 T,
      isoscelesSymmetryPhase (z s) = z s := by
    intro s hs
    exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
      hfixed s (hsegmentT hs)
  have hx : ∀ s ∈ Set.Icc 0 T, 0 < isoscelesSolutionX z s :=
    classicalNewton_isosceles_base_half_positive_on_segment
      hsol hstart' hsegmentT hSym hx₀
  exact classicalNewton_isosceles_rest_segment_impossible
    hsol hconn hzero hstart' hsegmentT hx hx₀ (by rfl)

/-- The maximal regular union for an arbitrary isosceles rest start has a
    positive finite right endpoint bounded by `sqrt (8*x₀^3)`. -/
theorem maximalNewtonUnionDomain_positive_finite_rightExtent_of_isosceles_rest
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    0 < sSup (maximalNewtonUnionDomain z₀) ∧
      sSup (maximalNewtonUnionDomain z₀) ≤ Real.sqrt (8*x₀^3) := by
  have hupper := maximalNewtonUnionDomain_bddAbove_of_isosceles_rest
    x₀ u₀ v₀ hx₀ z₀ hstart hcf
  have hbounded : BddAbove (maximalNewtonUnionDomain z₀) := by
    refine ⟨Real.sqrt (8*x₀^3), ?_⟩
    intro t ht
    exact le_of_lt (hupper t ht)
  have hnonempty : (maximalNewtonUnionDomain z₀).Nonempty := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact ⟨0, maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    have hrightD : w.right/2 ∈ maximalNewtonUnionDomain z₀ := by
      have hI : w.right/2 ∈ Set.Ioo w.left w.right := by
        constructor <;> linarith [w.left_lt_zero, w.zero_lt_right]
      exact maximalNewtonWitness_interval_subset z₀ w hI
    have hhalf : 0 < w.right/2 := by linarith [w.zero_lt_right]
    have hle : w.right/2 ≤ sSup (maximalNewtonUnionDomain z₀) :=
      le_csSup hbounded hrightD
    exact lt_of_lt_of_le hhalf hle
  · exact csSup_le hnonempty (by
      intro t ht
      exact le_of_lt (hupper t ht))


/-- For every isosceles rest start, the maximal base half-length cannot stay
    uniformly separated from zero on its full forward domain. The leg
    distances are at least the base half-length, so no height barrier is
    needed to obtain a uniform collision barrier under that hypothesis. -/
theorem maximalNewtonUnion_isosceles_base_not_bounded_below
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ maximalNewtonUnionDomain z₀,
      0 ≤ t → δ ≤ isoscelesSolutionX (maximalNewtonUnionTrajectory z₀) t := by
  rintro ⟨δ, hδ, hxlower⟩
  let D := maximalNewtonUnionDomain z₀
  let z := maximalNewtonUnionTrajectory z₀
  let T₀ := Real.sqrt (8*x₀^3)
  let τ := sSup D
  have hupperT : ∀ t ∈ D, t < T₀ := by
    simpa [D, T₀] using
      maximalNewtonUnionDomain_bddAbove_of_isosceles_rest
        x₀ u₀ v₀ hx₀ z₀ hstart hcf
  have hbounded : BddAbove D := ⟨T₀, fun t ht => le_of_lt (hupperT t ht)⟩
  have hzero : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hnonempty : D.Nonempty := ⟨0, hzero⟩
  have hconn : IsPreconnected D := by simpa [D] using
    isPreconnected_maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := by
    simpa [z, D] using maximalNewtonUnionTrajectory_solution z₀
  have hinit : z 0 = z₀ := by simpa [z] using
    maximalNewtonUnionTrajectory_initial z₀ hcf
  have hτpos : 0 < τ := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    have hmem : w.right/2 ∈ D := by
      have hI : w.right/2 ∈ Set.Ioo w.left w.right := by
        constructor <;> linarith [w.left_lt_zero, w.zero_lt_right]
      exact maximalNewtonWitness_interval_subset z₀ w hI
    have hhalf : 0 < w.right/2 := by linarith [w.zero_lt_right]
    have hle : w.right/2 ≤ τ := le_csSup hbounded hmem
    dsimp [τ]
    exact lt_of_lt_of_le hhalf hle
  have hτupper : τ ≤ T₀ := csSup_le hnonempty (fun t ht => le_of_lt (hupperT t ht))
  have hright : ∀ t ∈ Set.Ico 0 τ, t ∈ D := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := (lt_csSup_iff hbounded hnonempty).mp ht.2
    exact hconn.Icc_subset hzero hs ⟨ht.1, le_of_lt hts⟩
  have hstartZ : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)) :=
    hinit.trans hstart
  have hrest : ∀ i : Fin 3, (z 0).2 i = 0 := by
    intro i
    rw [hstartZ]
  have hDelta : 0 < δ := hδ
  let Delta := δ
  have hDelta' : 0 < Delta := by simpa [Delta] using hDelta
  have hsep : ∀ t ∈ Set.Ico 0 τ, ∀ i j : Fin 3, i ≠ j →
      Delta ≤ dist ((z t).1 i) ((z t).1 j) := by
    intro t ht i j hij
    have htD := hright t ht
    have hseg : Set.Icc 0 t ⊆ D := hconn.Icc_subset hzero htD
    have hsym0 : isoscelesSymmetryPhase (z 0) = z 0 := by
      rw [hstartZ]
      exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
    have hSym : ∀ s ∈ Set.Icc 0 t, isoscelesSymmetryPhase (z s) = z s := by
      intro s hs
      exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
        hsym0 s (hseg hs)
    have hxpos : ∀ s ∈ Set.Icc 0 t, 0 < isoscelesSolutionX z s :=
      classicalNewton_isosceles_base_half_positive_on_segment
        hsol hstartZ hseg hSym hx₀
    have hxδ : δ ≤ isoscelesSolutionX z t := hxlower t htD ht.1
    have hxδ' : Delta ≤ isoscelesSolutionX z t := by simpa [Delta] using hxδ
    have hgeom := isoscelesConfiguration_all_distances_ge_base_half
      (isoscelesSolutionX z t) (isoscelesSolutionU z t)
      (isoscelesSolutionV z t) (hxpos t ⟨ht.1, le_rfl⟩) i j hij
    have hconfig : (z t).1 = isoscelesConfiguration
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t) := by
      exact isoscelesConfiguration_eq_of_symmetry_fixed (z t).1
        (congrArg Prod.fst (hSym t ⟨ht.1, le_rfl⟩))
    calc
      Delta ≤ isoscelesSolutionX z t := hxδ'
      _ ≤ dist (isoscelesConfiguration (isoscelesSolutionX z t)
          (isoscelesSolutionU z t) (isoscelesSolutionV z t) i)
          (isoscelesConfiguration (isoscelesSolutionX z t)
          (isoscelesSolutionU z t) (isoscelesSolutionV z t) j) := hgeom
      _ = dist ((z t).1 i) ((z t).1 j) := by rw [hconfig]
  have hLip : LipschitzOnWith (newtonPhaseFieldBound Delta) z (Set.Ico 0 τ) := by
    intro a ha b hb
    let s := max a b
    have hs : s ∈ Set.Ico 0 τ := by
      constructor
      · exact le_trans ha.1 (le_max_left a b)
      · exact max_lt ha.2 hb.2
    have hseg : Set.Icc 0 s ⊆ D := hconn.Icc_subset hzero (hright s hs)
    have hsepSeg : ∀ t ∈ Set.Icc 0 s, ∀ i j : Fin 3, i ≠ j →
        Delta ≤ dist ((z t).1 i) ((z t).1 j) := by
      intro t ht i j hij
      exact hsep t ⟨ht.1, lt_of_le_of_lt ht.2 hs.2⟩ i j hij
    have hfield := classicalNewton_uniform_phaseField_bound_of_distance_lower_bound
      hsol hconn hseg hs.1 hrest hDelta' hsepSeg
    have hLipSeg := classicalNewton_phase_lipschitzOnWith_of_field_bound
      hsol hseg hfield
    exact hLipSeg ⟨ha.1, le_max_left a b⟩ ⟨hb.1, le_max_right a b⟩
  obtain ⟨zτ, hlim⟩ := exists_left_limit_of_lipschitzOnWith_finiteDimensional
    hτpos hLip
  have hsepτ := left_limit_preserves_pairwise_distance_lower_bound
    (a := 0) hτpos hlim hsep
  have hcfτ : CollisionFree zτ.1 := by
    intro i j hij heq
    have hd := hsepτ i j hij
    rw [heq, dist_self] at hd
    exact (not_le_of_gt hDelta') hd
  obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
  let a := w.left/2
  have ha0 : a < 0 := by dsimp [a]; linarith [w.left_lt_zero]
  have haτ : a < τ := lt_trans ha0 hτpos
  have haD : a ∈ D := by
    have hI : a ∈ Set.Ioo w.left w.right := by
      constructor <;> dsimp [a] <;> linarith [w.left_lt_zero, w.zero_lt_right]
    exact maximalNewtonWitness_interval_subset z₀ w hI
  have hrightExt : ∀ t ∈ Set.Ioo a τ, t ∈ D := by
    intro t ht
    by_cases ht0 : 0 ≤ t
    · exact hright t ⟨ht0, ht.2⟩
    · exact hconn.Icc_subset haD hzero ⟨le_of_lt ht.1,
        le_of_lt (lt_of_not_ge ht0)⟩
  have hupperτ : ∀ t ∈ D, t ≤ τ := fun t ht => le_csSup hbounded ht
  have hnotcf := maximalNewtonUnion_finiteRightEndpoint_not_collisionFree
    z₀ hsol hinit ha0 haτ hτpos hrightExt hupperτ hlim
  exact hnotcf hcfτ

/-- Along the maximal isosceles trajectory, the base half-length tends
    to zero at the finite right endpoint. The proof combines the absence of a
    global positive lower bound with antitonicity on every regular segment. -/
theorem maximalNewtonUnion_isosceles_base_tends_zero
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t in nhdsWithin (sSup (maximalNewtonUnionDomain z₀))
        (Set.Iio (sSup (maximalNewtonUnionDomain z₀))),
        |isoscelesSolutionX (maximalNewtonUnionTrajectory z₀) t| < ε := by
  let D := maximalNewtonUnionDomain z₀
  let z := maximalNewtonUnionTrajectory z₀
  let τ := sSup D
  have hupperT : ∀ t ∈ D, t < Real.sqrt (8*x₀^3) := by
    simpa [D] using maximalNewtonUnionDomain_bddAbove_of_isosceles_rest
      x₀ u₀ v₀ hx₀ z₀ hstart hcf
  have hbounded : BddAbove D := ⟨Real.sqrt (8*x₀^3),
    fun t ht => le_of_lt (hupperT t ht)⟩
  have hzero : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hnonempty : D.Nonempty := ⟨0, hzero⟩
  have hconn : IsPreconnected D := by simpa [D] using
    isPreconnected_maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := by
    simpa [z, D] using maximalNewtonUnionTrajectory_solution z₀
  have hinit : z 0 = z₀ := by simpa [z] using
    maximalNewtonUnionTrajectory_initial z₀ hcf
  have hτpos : 0 < τ := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    have hmem : w.right/2 ∈ D := by
      have hI : w.right/2 ∈ Set.Ioo w.left w.right := by
        constructor <;> linarith [w.left_lt_zero, w.zero_lt_right]
      exact maximalNewtonWitness_interval_subset z₀ w hI
    have hhalf : 0 < w.right/2 := by linarith [w.zero_lt_right]
    exact lt_of_lt_of_le hhalf (le_csSup hbounded hmem)
  have hτupper : τ ≤ Real.sqrt (8*x₀^3) :=
    csSup_le hnonempty (fun t ht => le_of_lt (hupperT t ht))
  have hright : ∀ t ∈ Set.Ico 0 τ, t ∈ D := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := (lt_csSup_iff hbounded hnonempty).mp ht.2
    exact hconn.Icc_subset hzero hs ⟨ht.1, le_of_lt hts⟩
  have hstartZ : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)) :=
    hinit.trans hstart
  have hnoLower := maximalNewtonUnion_isosceles_base_not_bounded_below
    x₀ u₀ v₀ hx₀ z₀ hstart hcf
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ t ∈ D, 0 ≤ t ∧ isoscelesSolutionX z t < ε := by
    intro ε hε
    by_contra hnot
    have hlower : ∀ t ∈ D, 0 ≤ t → ε ≤ isoscelesSolutionX z t := by
      intro t ht ht0
      by_contra hlt
      exact hnot ⟨t, ht, ht0, lt_of_not_ge hlt⟩
    exact hnoLower ⟨ε, hε, by simpa [z, D] using hlower⟩
  intro ε hε
  obtain ⟨t₀, ht₀D, ht₀nonneg, hsmall₀⟩ := hsmall ε hε
  obtain ⟨w, ht₀W⟩ := maximalNewtonUnionDomain_covered z₀ ht₀D
  let s₁ := (t₀ + w.right) / 2
  have hs₁W : s₁ ∈ Set.Ioo w.left w.right := by
    constructor <;> dsimp [s₁] <;> rcases ht₀W with ⟨ht₀l, ht₀r⟩ <;> linarith
  have ht₀s₁ : t₀ < s₁ := by
    dsimp [s₁]
    rcases ht₀W with ⟨_, ht₀r⟩
    linarith
  have hs₁D : s₁ ∈ D := maximalNewtonWitness_interval_subset z₀ w hs₁W
  have ht₀τ : t₀ < τ := lt_of_lt_of_le ht₀s₁ (le_csSup hbounded hs₁D)
  have htail : ∀ᶠ t in nhdsWithin τ (Set.Iio τ), t₀ < t := by
    exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio τ))
      (Ioi_mem_nhds ht₀τ)
  filter_upwards [htail, self_mem_nhdsWithin] with t htt htτ
  have ht0 : 0 ≤ t := le_trans ht₀nonneg (le_of_lt htt)
  have htD : t ∈ D := hright t ⟨ht0, htτ⟩
  have hseg : Set.Icc 0 t ⊆ D := hconn.Icc_subset hzero htD
  have hsym0 : isoscelesSymmetryPhase (z 0) = z 0 := by
    rw [hstartZ]
    exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
  have hSym : ∀ s ∈ Set.Icc 0 t, isoscelesSymmetryPhase (z s) = z s := by
    intro s hs
    exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
      hsym0 s (hseg hs)
  have hxpos : ∀ s ∈ Set.Icc 0 t, 0 < isoscelesSolutionX z s :=
    classicalNewton_isosceles_base_half_positive_on_segment
      hsol hstartZ hseg hSym hx₀
  have hanti := classicalNewton_isosceles_base_half_antitone_on_segment
    hsol hstartZ hseg hSym hxpos ht0
  have ht₀seg : t₀ ∈ Set.Icc 0 t := ⟨ht₀nonneg, le_of_lt htt⟩
  have htseg : t ∈ Set.Icc 0 t := ⟨ht0, le_rfl⟩
  have hle := hanti ht₀seg htseg (le_of_lt htt)
  have hpos := hxpos t htseg
  rw [abs_of_pos hpos]
  exact lt_of_le_of_lt hle hsmall₀

/-- The actual base-pair distance on the maximal isosceles orbit tends to zero
    at its finite right endpoint. -/
theorem maximalNewtonUnion_isosceles_base_pair_distance_tends_zero
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    Tendsto
      (fun t => dist ((maximalNewtonUnionTrajectory z₀ t).1 0)
        ((maximalNewtonUnionTrajectory z₀ t).1 1))
      (nhdsWithin (sSup (maximalNewtonUnionDomain z₀))
        (Set.Iio (sSup (maximalNewtonUnionDomain z₀)))) (𝓝 0) := by
  let D := maximalNewtonUnionDomain z₀
  let z := maximalNewtonUnionTrajectory z₀
  let τ := sSup D
  let X := isoscelesSolutionX z
  have hbase := maximalNewtonUnion_isosceles_base_tends_zero
    x₀ u₀ v₀ hx₀ z₀ hstart hcf
  have hXlim : Tendsto X (nhdsWithin τ (Set.Iio τ)) (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    filter_upwards [hbase ε hε] with t ht
    simpa [X, Real.dist_eq] using ht
  have h2Xlim : Tendsto (fun t => 2*X t)
      (nhdsWithin τ (Set.Iio τ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hXlim
  have hupper : ∀ t ∈ D, t < Real.sqrt (8*x₀^3) := by
    simpa [D] using maximalNewtonUnionDomain_bddAbove_of_isosceles_rest
      x₀ u₀ v₀ hx₀ z₀ hstart hcf
  have hbounded : BddAbove D := ⟨Real.sqrt (8*x₀^3),
    fun t ht => le_of_lt (hupper t ht)⟩
  have hnonempty : D.Nonempty := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact ⟨0, maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩⟩
  have hτpos : 0 < τ := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    have hw : w.right/2 ∈ D := by
      apply maximalNewtonWitness_interval_subset z₀ w
      constructor <;> linarith [w.left_lt_zero, w.zero_lt_right]
    exact lt_of_lt_of_le (by linarith [w.zero_lt_right])
      (le_csSup hbounded hw)
  have hzero : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hconn : IsPreconnected D := by
    simpa [D] using isPreconnected_maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := by
    simpa [z, D] using maximalNewtonUnionTrajectory_solution z₀
  have hinit : z 0 = z₀ := by
    simpa [z] using maximalNewtonUnionTrajectory_initial z₀ hcf
  have hstartZ : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)) :=
    hinit.trans hstart
  have hright : ∀ t ∈ Set.Ico 0 τ, t ∈ D := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := (lt_csSup_iff hbounded hnonempty).mp ht.2
    exact hconn.Icc_subset hzero hs ⟨ht.1, le_of_lt hts⟩
  have hdeq : (fun t => dist ((z t).1 0) ((z t).1 1)) =ᶠ[
      nhdsWithin τ (Set.Iio τ)] (fun t => 2*X t) := by
    have hnear : ∀ᶠ t in nhdsWithin τ (Set.Iio τ), 0 < t := by
      exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio τ))
        (Ioi_mem_nhds hτpos)
    filter_upwards [hnear, self_mem_nhdsWithin] with t htt htτ
    have htD : t ∈ D := hright t ⟨le_of_lt htt, htτ⟩
    have hseg : Set.Icc 0 t ⊆ D := hconn.Icc_subset hzero htD
    have hfixed : isoscelesSymmetryPhase (z 0) = z 0 := by
      rw [hstartZ]
      exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀
    have hSym : ∀ s ∈ Set.Icc 0 t, isoscelesSymmetryPhase (z s) = z s := by
      intro s hs
      exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
        hfixed s (hseg hs)
    have hx : 0 < X t :=
      classicalNewton_isosceles_base_half_positive_on_segment hsol hstartZ
        hseg hSym hx₀ t ⟨le_of_lt htt, le_rfl⟩
    have hconfig : (z t).1 = isoscelesConfiguration
        (isoscelesSolutionX z t) (isoscelesSolutionU z t)
        (isoscelesSolutionV z t) :=
      isoscelesConfiguration_eq_of_symmetry_fixed (z t).1
        (congrArg Prod.fst (hSym t ⟨le_of_lt htt, le_rfl⟩))
    have hdist := isoscelesConfiguration_base_dist_eq
      (isoscelesSolutionX z t) (isoscelesSolutionU z t)
      (isoscelesSolutionV z t) (le_of_lt hx)
    simpa [z, X, hconfig] using hdist
  exact h2Xlim.congr' hdeq.symm

/-- Backwards-compatible tall-data specialization of the general
    no-positive-lower-bound result. -/
theorem maximalNewtonUnion_tall_isosceles_base_not_bounded_below
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀) (_hH : 0 < v₀-u₀)
    (_htall : (v₀-u₀)^3 > 96*x₀^3)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ maximalNewtonUnionDomain z₀,
      0 ≤ t → δ ≤ isoscelesSolutionX (maximalNewtonUnionTrajectory z₀) t :=
  maximalNewtonUnion_isosceles_base_not_bounded_below
    x₀ u₀ v₀ hx₀ z₀ hstart hcf

/-- Backwards-compatible tall-data specialization of the general base-limit
    result. -/
theorem maximalNewtonUnion_tall_isosceles_base_tends_zero
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀) (_hH : 0 < v₀-u₀)
    (_htall : (v₀-u₀)^3 > 96*x₀^3)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t in nhdsWithin (sSup (maximalNewtonUnionDomain z₀))
        (Set.Iio (sSup (maximalNewtonUnionDomain z₀))),
        |isoscelesSolutionX (maximalNewtonUnionTrajectory z₀) t| < ε :=
  maximalNewtonUnion_isosceles_base_tends_zero
    x₀ u₀ v₀ hx₀ z₀ hstart hcf

/-- A rest isosceles start whose two legs are strictly longer than its base
    has no syzygy anywhere on the maximal regular forward orbit. The two
    orientation branches are handled by the existing Wronskian ratio
    bootstrap. -/
theorem maximalNewtonUnion_isosceles_no_forward_syzygy_of_longer_legs
    (x₀ u₀ v₀ : ℝ) (hx₀ : 0 < x₀)
    (hratio₀ : Real.sqrt 3 < (v₀-u₀)/x₀ ∨
      (v₀-u₀)/x₀ < -Real.sqrt 3)
    (z₀ : Phase)
    (hstart : z₀ = (isoscelesConfiguration x₀ u₀ v₀,
      fun _ : Fin 3 => (0 : Point)))
    (hcf : CollisionFree z₀.1) :
    ∀ t ∈ maximalNewtonUnionDomain z₀, 0 ≤ t →
      signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 ≠ 0 := by
  let D := maximalNewtonUnionDomain z₀
  let z := maximalNewtonUnionTrajectory z₀
  have hzero : (0 : ℝ) ∈ D := by
    obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
    exact maximalNewtonWitness_interval_subset z₀ w
      ⟨w.left_lt_zero, w.zero_lt_right⟩
  have hconn : IsPreconnected D := by
    simpa [D] using isPreconnected_maximalNewtonUnionDomain z₀
  have hsol : ClassicalNewtonSolution z D := by
    simpa [z, D] using maximalNewtonUnionTrajectory_solution z₀
  have hinit : z 0 = z₀ := by
    simpa [z] using maximalNewtonUnionTrajectory_initial z₀ hcf
  have hstartZ : z 0 =
      (isoscelesConfiguration x₀ u₀ v₀, fun _ : Fin 3 => (0 : Point)) :=
    hinit.trans hstart
  intro t ht ht0
  have hseg : Set.Icc 0 t ⊆ D := hconn.Icc_subset hzero ht
  have hSym : ∀ s ∈ Set.Icc 0 t, isoscelesSymmetryPhase (z s) = z s := by
    intro s hs
    exact classicalNewtonSolution_isoscelesSymmetric hsol hconn hzero
      (by rw [hstartZ]; exact isoscelesRestPhase_fixed_by_symmetry x₀ u₀ v₀)
      s (hseg hs)
  have hx : ∀ s ∈ Set.Icc 0 t, 0 < isoscelesSolutionX z s :=
    classicalNewton_isosceles_base_half_positive_on_segment
      hsol hstartZ hseg hSym hx₀
  have hconfig : (z t).1 = isoscelesConfiguration
      (isoscelesSolutionX z t) (isoscelesSolutionU z t)
      (isoscelesSolutionV z t) :=
    isoscelesConfiguration_eq_of_symmetry_fixed (z t).1
      (congrArg Prod.fst (hSym t ⟨ht0, le_rfl⟩))
  have harea : signedDoubleArea (z t).1 =
      2 * isoscelesSolutionX z t * isoscelesSolutionZ z t := by
    rw [hconfig, isoscelesConfiguration_signedDoubleArea]
    dsimp [isoscelesSolutionZ]
  have hx_t := hx t ⟨ht0, le_rfl⟩
  rcases hratio₀ with hratioPos | hratioNeg
  · have hratio := classicalNewton_isosceles_rest_ratio_stays_above_sqrt_three
      hsol hconn hzero hstartZ hseg hratioPos hx
    have hratio_t : Real.sqrt 3 < isoscelesSolutionZ z t /
        isoscelesSolutionX z t := by
      have h := hratio t ⟨ht0, le_rfl⟩
      simpa [scalarRatioCurve, isoscelesSolutionZ] using h
    have hz : 0 < isoscelesSolutionZ z t := by
      have hmul := (lt_div_iff₀ hx_t).mp hratio_t
      exact lt_trans (by positivity) hmul
    rw [harea]
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) hx_t) hz)
  · have hratio := classicalNewton_isosceles_rest_ratio_stays_below_neg_sqrt_three
      hsol hconn hzero hstartZ hseg hratioNeg hx
    have h := hratio t ⟨ht0, le_rfl⟩
    have hratio_t : isoscelesSolutionZ z t / isoscelesSolutionX z t <
        -Real.sqrt 3 := by simpa [scalarRatioCurve, isoscelesSolutionZ] using h
    have hmul := (div_lt_iff₀ hx_t).mp hratio_t
    have hz : isoscelesSolutionZ z t < 0 := by
      have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      nlinarith [hmul]
    rw [harea]
    exact ne_of_lt (mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) hx_t) hz)
end DroppingThreeBodies
