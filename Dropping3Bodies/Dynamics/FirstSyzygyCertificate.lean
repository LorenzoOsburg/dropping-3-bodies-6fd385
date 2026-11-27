module

public import Dropping3Bodies.Dynamics.MaximalTranslation
public import Dropping3Bodies.Dynamics.GravityRescaling
public import Dropping3Bodies.EqualMass.SolutionSideOrdering
public import Mathlib.Analysis.Convex.Between
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-! # A complete first regular syzygy certificate

The result packages the initial phase, the maximal regular trajectory, its
first collinearity time, and the longest-side ordering at that same time.
-/

namespace DroppingThreeBodies

noncomputable section

set_option maxHeartbeats 5000000

theorem centeredPositive_firstRegularSyzygy_and_middleBody
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : 0 < signedDoubleArea z₀.1)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ T ∈ maximalNewtonUnionDomain z₀,
      0 < T ∧
      FirstRegularSyzygy (maximalNewtonUnionTrajectory z₀)
        (maximalNewtonUnionDomain z₀) 0 T ∧
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
  have hrest0 : ∀ b, (z 0).2 b = 0 := by
    simpa [z, hinit] using hrest
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
  have hcollision : CollisionFree (z T).1 := (hsol.2 T (hsegment ⟨le_of_lt hTpos, le_rfl⟩)).1
  have hfirst : FirstRegularSyzygy z D 0 T := by
    refine ⟨hTpos, hsegment, hsyzygy, ?_, hcollision⟩
    intro t ht
    exact ne_of_gt (hareaPre t ht)
  exact ⟨T, hTD, hTpos, hfirst, hbetween⟩

end

end DroppingThreeBodies
