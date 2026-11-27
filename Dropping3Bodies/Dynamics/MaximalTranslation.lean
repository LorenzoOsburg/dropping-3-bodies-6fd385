module

public import Dropping3Bodies.Dynamics.MaximalInterval
public import Dropping3Bodies.Dynamics.TranslationSymmetry
public import Dropping3Bodies.Dynamics.MaximalReflection
public import Mathlib.Analysis.Convex.Between
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

@[expose] public section

/-! Translation symmetry of maximal Newton trajectories. -/

namespace DroppingThreeBodies

noncomputable section

theorem translatePhase_inverse (c : Point) (z : Phase) :
    translatePhase (-c) (translatePhase c z) = z := by
  apply Prod.ext
  · funext i
    simp [translatePhase, translateConfiguration, translatePoint, add_assoc]
  · rfl

noncomputable def translateNewtonInitialIntervalWitness {z₀ : Phase}
    (c : Point) (w : NewtonInitialIntervalWitness z₀) :
    NewtonInitialIntervalWitness (translatePhase c z₀) where
  left := w.left
  right := w.right
  trajectory := fun t => translatePhase c (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by rw [w.initial]
  solution := classicalNewtonSolution_translate c w.solution

noncomputable def untranslateNewtonInitialIntervalWitness {z₀ : Phase}
    (c : Point) (w : NewtonInitialIntervalWitness (translatePhase c z₀)) :
    NewtonInitialIntervalWitness z₀ where
  left := w.left
  right := w.right
  trajectory := fun t => translatePhase (-c) (w.trajectory t)
  left_lt_zero := w.left_lt_zero
  zero_lt_right := w.zero_lt_right
  initial := by
    rw [w.initial]
    exact translatePhase_inverse c z₀
  solution := classicalNewtonSolution_translate (-c) w.solution

theorem maximalNewtonUnionDomain_translate (z₀ : Phase) (c : Point) :
    maximalNewtonUnionDomain (translatePhase c z₀) = maximalNewtonUnionDomain z₀ := by
  ext t
  constructor
  · intro ht
    obtain ⟨w, hwt⟩ := maximalNewtonUnionDomain_covered (translatePhase c z₀) ht
    exact maximalNewtonWitness_interval_subset z₀
      (untranslateNewtonInitialIntervalWitness c w) hwt
  · intro ht
    obtain ⟨w, hwt⟩ := maximalNewtonUnionDomain_covered z₀ ht
    exact maximalNewtonWitness_interval_subset (translatePhase c z₀)
      (translateNewtonInitialIntervalWitness c w) hwt

theorem maximalNewtonUnionTrajectory_translate (z₀ : Phase) (c : Point)
    {t : ℝ} (ht : t ∈ maximalNewtonUnionDomain z₀) :
    maximalNewtonUnionTrajectory (translatePhase c z₀) t =
      translatePhase c (maximalNewtonUnionTrajectory z₀ t) := by
  let original := maximalNewtonChosenWitness z₀ t ht
  let translatedInitial := translatePhase c z₀
  have htT : t ∈ maximalNewtonUnionDomain translatedInitial := by
    rw [maximalNewtonUnionDomain_translate]
    exact ht
  let translated := maximalNewtonChosenWitness translatedInitial t htT
  let shifted := translateNewtonInitialIntervalWitness c original
  have hshiftedSol : ClassicalNewtonSolution shifted.trajectory
      (Set.Ioo shifted.left shifted.right) := shifted.solution
  have htranslatedSol : ClassicalNewtonSolution translated.trajectory
      (Set.Ioo translated.left translated.right) := translated.solution
  have hzero : (0 : ℝ) ∈
      Set.Ioo shifted.left shifted.right ∩ Set.Ioo translated.left translated.right := by
    constructor
    · exact ⟨shifted.left_lt_zero, shifted.zero_lt_right⟩
    · exact ⟨translated.left_lt_zero, translated.zero_lt_right⟩
  have hinit : shifted.trajectory 0 = translated.trajectory 0 :=
    shifted.initial.trans translated.initial.symm
  have hoverlap := classicalNewton_eq_on_of_preconnected_overlap
    hshiftedSol htranslatedSol
    (isPreconnected_inter_openIntervals shifted.left shifted.right
      translated.left translated.right) hzero hinit
  have htShifted : t ∈ Set.Ioo shifted.left shifted.right :=
    maximalNewtonChosenWitness_spec z₀ t ht
  have htTranslated : t ∈ Set.Ioo translated.left translated.right :=
    maximalNewtonChosenWitness_spec translatedInitial t htT
  have heq := hoverlap t ⟨htShifted, htTranslated⟩
  calc
    maximalNewtonUnionTrajectory translatedInitial t = translated.trajectory t := by
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos htT]
    _ = shifted.trajectory t := heq.symm
    _ = translatePhase c (maximalNewtonUnionTrajectory z₀ t) := by
      change translatePhase c (original.trajectory t) = _
      unfold maximalNewtonUnionTrajectory
      rw [dif_pos ht]

/-- Translation that moves the equal-mass center of three positions to zero. -/
def centerTranslation (q : Fin 3 → Point) : Point :=
  -((1 / 3 : ℝ) • (q 0 + q 1 + q 2))

def translatePointAffine (c : Point) : Point →ᵃ[ℝ] Point := by
  refine AffineMap.mk (fun p : Point => p + c) LinearMap.id ?_
  intro p v
  simp [vadd_eq_add, add_assoc]

@[simp] theorem translatePointAffine_apply (c p : Point) :
    translatePointAffine c p = translatePoint c p := rfl

theorem translatePointAffine_injective (c : Point) :
    Function.Injective (translatePointAffine c) := by
  intro p q hpq
  exact add_right_cancel hpq

theorem translateConfiguration_centered (q : Fin 3 → Point) :
    translateConfiguration (centerTranslation q) q 0 +
      translateConfiguration (centerTranslation q) q 1 +
      translateConfiguration (centerTranslation q) q 2 = 0 := by
  change q 0 + centerTranslation q + (q 1 + centerTranslation q) +
    (q 2 + centerTranslation q) = 0
  have hsum : q 0 + centerTranslation q + (q 1 + centerTranslation q) +
      (q 2 + centerTranslation q) =
      (q 0 + q 1 + q 2) + (3 : ℝ) • centerTranslation q := by
    module
  rw [hsum, centerTranslation]
  module

set_option maxHeartbeats 500000

/-- Removing the centering assumption from the equal-mass, strict-longest
    first-syzygy theorem by translating the whole maximal solution. -/
theorem maximalNewtonUnion_body_between_at_first_syzygy_of_uncentered_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (harea₀ : signedDoubleArea z₀.1 ≠ 0)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ T ∈ maximalNewtonUnionDomain z₀, 0 < T ∧
      Sbtw ℝ ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i))
        ((maximalNewtonUnionTrajectory z₀ T).1 i)
        ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i)) := by
  let c := centerTranslation z₀.1
  let zC := translatePhase c z₀
  have hcfC : CollisionFree zC.1 := by
    change CollisionFree (translateConfiguration c z₀.1)
    rw [collisionFree_iff_dist_pos]
    intro a b hab
    rw [dist_translateConfiguration]
    exact (collisionFree_iff_dist_pos z₀.1).mp hcf a b hab
  have hrestC : ∀ b, zC.2 b = 0 := by
    intro b
    exact hrest b
  have hcenterC : zC.1 0 + zC.1 1 + zC.1 2 = 0 := by
    simpa [zC, translatePhase] using translateConfiguration_centered z₀.1
  have hareaC_eq : signedDoubleArea zC.1 = signedDoubleArea z₀.1 := by
    exact signedDoubleArea_translateConfiguration c z₀.1
  have hlongPrevC : sideSq zC.1 i > sideSq zC.1 (cyclicPrev i) := by
    change sideSq (translateConfiguration c z₀.1) i >
      sideSq (translateConfiguration c z₀.1) (cyclicPrev i)
    rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
    exact hlongPrev
  have hlongNextC : sideSq zC.1 i > sideSq zC.1 (cyclicNext i) := by
    change sideSq (translateConfiguration c z₀.1) i >
      sideSq (translateConfiguration c z₀.1) (cyclicNext i)
    rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
    exact hlongNext
  have hresult : ∃ T ∈ maximalNewtonUnionDomain zC, 0 < T ∧
      Sbtw ℝ ((maximalNewtonUnionTrajectory zC T).1 (cyclicPrev i))
        ((maximalNewtonUnionTrajectory zC T).1 i)
        ((maximalNewtonUnionTrajectory zC T).1 (cyclicNext i)) := by
    by_cases hpos : 0 < signedDoubleArea z₀.1
    · have harea : 0 < signedDoubleArea zC.1 := by rw [hareaC_eq]; exact hpos
      exact maximalNewtonUnion_body_between_at_first_syzygy_of_strictLongest
        zC hcfC hrestC hcenterC harea i hlongPrevC hlongNextC
    · have hneg : signedDoubleArea z₀.1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) harea₀
      have harea : signedDoubleArea zC.1 < 0 := by rw [hareaC_eq]; exact hneg
      exact maximalNewtonUnion_body_between_at_first_syzygy_of_strictLongest_negativeArea
        zC hcfC hrestC hcenterC harea i hlongPrevC hlongNextC
  obtain ⟨T, hTC, hTpos, hbetweenC⟩ := hresult
  have hT : T ∈ maximalNewtonUnionDomain z₀ := by
    rw [← maximalNewtonUnionDomain_translate z₀ c]
    exact hTC
  have htrajectory := maximalNewtonUnionTrajectory_translate z₀ c hT
  have hinj : Function.Injective (translatePointAffine c) :=
    translatePointAffine_injective c
  have htrajectory' :
      maximalNewtonUnionTrajectory zC T =
        translatePhase c (maximalNewtonUnionTrajectory z₀ T) := by
    simpa [zC] using htrajectory
  have hbetweenMap : Sbtw ℝ
      (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i)))
      (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 i))
      (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i))) := by
    have hbetweenC' := hbetweenC
    rw [htrajectory'] at hbetweenC'
    simpa [translatePointAffine, translatePhase, translateConfiguration,
      translatePoint] using hbetweenC'
  have hbetween := (Function.Injective.sbtw_map_iff hinj).mp hbetweenMap
  exact ⟨T, hT, hTpos, hbetween⟩

end

end DroppingThreeBodies
