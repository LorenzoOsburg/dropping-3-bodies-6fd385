module

public import Dropping3Bodies.Dynamics.MaximalInterval
public import Dropping3Bodies.Dynamics.ReflectionSymmetry
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Between

@[expose] public section

/-!
# Reflection of the maximal Newton solution

Reflection preserves every local witness interval. Local uniqueness on
intersections then shows that the pointwise maximal union also commutes with
reflection.
-/

namespace DroppingThreeBodies

noncomputable section

theorem reflectConfiguration_involutive (q : Fin 3 → Point) :
    reflectConfiguration (reflectConfiguration q) = q := by
  funext i
  exact reflectPoint_involutive (q i)

theorem reflectPhase_involutive (z : Phase) : reflectPhase (reflectPhase z) = z := by
  rcases z with ⟨q, v⟩
  apply Prod.ext
  · exact reflectConfiguration_involutive q
  · exact reflectConfiguration_involutive v

/-- Reflect a local initial-value witness without changing its time interval. -/
noncomputable def reflectNewtonInitialIntervalWitness {z₀ : Phase}
    (w : NewtonInitialIntervalWitness z₀) :
    NewtonInitialIntervalWitness (reflectPhase z₀) where
  left := w.left
  right := w.right
  trajectory := fun t => reflectPhase (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by rw [w.initial]
  solution := classicalNewtonSolution_reflect w.solution

/-- Reflecting twice restores the original initial-value witness, up to the
    pointwise involution of its trajectory. -/
noncomputable def unreflectNewtonInitialIntervalWitness {z₀ : Phase}
    (w : NewtonInitialIntervalWitness (reflectPhase z₀)) :
    NewtonInitialIntervalWitness z₀ where
  left := w.left
  right := w.right
  trajectory := fun t => reflectPhase (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by
    rw [w.initial]
    exact reflectPhase_involutive z₀
  solution := classicalNewtonSolution_reflect w.solution

theorem maximalNewtonUnionDomain_reflect (z₀ : Phase) :
    maximalNewtonUnionDomain (reflectPhase z₀) = maximalNewtonUnionDomain z₀ := by
  ext t
  constructor
  · intro ht
    obtain ⟨w, hwt⟩ := maximalNewtonUnionDomain_covered (reflectPhase z₀) ht
    exact maximalNewtonWitness_interval_subset z₀
      (unreflectNewtonInitialIntervalWitness w) hwt
  · intro ht
    obtain ⟨w, hwt⟩ := maximalNewtonUnionDomain_covered z₀ ht
    exact maximalNewtonWitness_interval_subset (reflectPhase z₀)
      (reflectNewtonInitialIntervalWitness w) hwt

theorem maximalNewtonUnionTrajectory_reflect (z₀ : Phase) {t : ℝ}
    (ht : t ∈ maximalNewtonUnionDomain z₀) :
    maximalNewtonUnionTrajectory (reflectPhase z₀) t =
      reflectPhase (maximalNewtonUnionTrajectory z₀ t) := by
  let original := maximalNewtonChosenWitness z₀ t ht
  let reflectedInitial := reflectPhase z₀
  have htR : t ∈ maximalNewtonUnionDomain reflectedInitial := by
    rw [maximalNewtonUnionDomain_reflect z₀]
    exact ht
  let reflected := maximalNewtonChosenWitness reflectedInitial t htR
  let mirror := reflectNewtonInitialIntervalWitness original
  have hmirrorSol : ClassicalNewtonSolution mirror.trajectory
      (Set.Ioo mirror.left mirror.right) := mirror.solution
  have hreflectedSol : ClassicalNewtonSolution reflected.trajectory
      (Set.Ioo reflected.left reflected.right) := reflected.solution
  have hzero : (0 : ℝ) ∈
      Set.Ioo mirror.left mirror.right ∩ Set.Ioo reflected.left reflected.right := by
    constructor
    · exact ⟨mirror.left_lt_zero, mirror.zero_lt_right⟩
    · exact ⟨reflected.left_lt_zero, reflected.zero_lt_right⟩
  have hinit : mirror.trajectory 0 = reflected.trajectory 0 :=
    mirror.initial.trans reflected.initial.symm
  have hoverlap := classicalNewton_eq_on_of_preconnected_overlap
    hmirrorSol hreflectedSol
    (isPreconnected_inter_openIntervals mirror.left mirror.right
      reflected.left reflected.right) hzero hinit
  have htMirror : t ∈ Set.Ioo mirror.left mirror.right := by
    exact maximalNewtonChosenWitness_spec z₀ t ht
  have htReflected : t ∈ Set.Ioo reflected.left reflected.right :=
    maximalNewtonChosenWitness_spec reflectedInitial t htR
  have heq := hoverlap t ⟨htMirror, htReflected⟩
  calc
    maximalNewtonUnionTrajectory reflectedInitial t = reflected.trajectory t := by
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos htR]
    _ = mirror.trajectory t := heq.symm
    _ = reflectPhase (maximalNewtonUnionTrajectory z₀ t) := by
      change reflectPhase (original.trajectory t) = _
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos ht]

/-- The strict-longest-side first-syzygy conclusion also holds for negatively
    oriented equal-mass rest data, by reflecting the complete maximal solution. -/
theorem maximalNewtonUnion_body_between_at_first_syzygy_of_strictLongest_negativeArea
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (hcenter : z₀.1 0 + z₀.1 1 + z₀.1 2 = 0)
    (harea₀ : signedDoubleArea z₀.1 < 0)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ T ∈ maximalNewtonUnionDomain z₀, 0 < T ∧
      Sbtw ℝ ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i))
        ((maximalNewtonUnionTrajectory z₀ T).1 i)
        ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i)) := by
  let zR := reflectPhase z₀
  have hcfR : CollisionFree zR.1 := by
    rw [collisionFree_iff_dist_pos]
    intro a b hab
    change 0 < dist (reflectPoint (z₀.1 a)) (reflectPoint (z₀.1 b))
    rw [reflectPoint_dist]
    exact (collisionFree_iff_dist_pos z₀.1).mp hcf a b hab
  have hrestR : ∀ b, zR.2 b = 0 := by
    intro b
    simp [zR, reflectPhase, reflectConfiguration, hrest b]
  have hcenterR : zR.1 0 + zR.1 1 + zR.1 2 = 0 := by
    have h := congrArg reflectPoint hcenter
    simpa [zR, reflectPhase, reflectConfiguration, reflectPoint_add] using h
  have hareaR : 0 < signedDoubleArea zR.1 := by
    change 0 < signedDoubleArea (reflectConfiguration z₀.1)
    rw [signedDoubleArea_reflectConfiguration]
    linarith
  have hlongPrevR : sideSq zR.1 i > sideSq zR.1 (cyclicPrev i) := by
    change sideSq (reflectConfiguration z₀.1) i >
      sideSq (reflectConfiguration z₀.1) (cyclicPrev i)
    rw [sideSq_reflectConfiguration, sideSq_reflectConfiguration]
    exact hlongPrev
  have hlongNextR : sideSq zR.1 i > sideSq zR.1 (cyclicNext i) := by
    change sideSq (reflectConfiguration z₀.1) i >
      sideSq (reflectConfiguration z₀.1) (cyclicNext i)
    rw [sideSq_reflectConfiguration, sideSq_reflectConfiguration]
    exact hlongNext
  obtain ⟨T, hTR, hTpos, hbetweenR⟩ :=
    maximalNewtonUnion_body_between_at_first_syzygy_of_strictLongest
      zR hcfR hrestR hcenterR hareaR i hlongPrevR hlongNextR
  have hT : T ∈ maximalNewtonUnionDomain z₀ := by
    rw [← maximalNewtonUnionDomain_reflect z₀]
    exact hTR
  have htrajectory := maximalNewtonUnionTrajectory_reflect z₀ hT
  have hbetweenReflect :
      Sbtw ℝ
        (reflectPoint ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i)))
        (reflectPoint ((maximalNewtonUnionTrajectory z₀ T).1 i))
        (reflectPoint ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i))) := by
    rw [htrajectory] at hbetweenR
    simpa [zR, reflectPhase, reflectConfiguration] using hbetweenR
  have hinjective : Function.Injective reflectPointAffine := by
    intro x y hxy
    apply reflectPoint_injective
    simpa using hxy
  refine ⟨T, hT, hTpos, ?_⟩
  exact (Function.Injective.sbtw_map_iff (R := ℝ) hinjective).mp
    (by simpa [reflectPointAffine, reflectPointLinear] using hbetweenReflect)

end

end DroppingThreeBodies
