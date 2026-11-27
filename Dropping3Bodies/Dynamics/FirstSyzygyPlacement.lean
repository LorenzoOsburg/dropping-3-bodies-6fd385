module

public import Dropping3Bodies.Dynamics.FirstSyzygyCertificate
public import Dropping3Bodies.Dynamics.MaximalReflection
public import Dropping3Bodies.Dynamics.MaximalTranslation
public import Dropping3Bodies.Geometry.Reflection
public import Dropping3Bodies.Geometry.Translation
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

@[expose] public section

/-! Placement-free first regular syzygy certificate for a strict-longest
    equal-mass rest start. -/

namespace DroppingThreeBodies

noncomputable section

set_option maxHeartbeats 1000000

/-- From arbitrary position and either orientation, a strict-longest
    equal-mass rest start has a regular first syzygy whose middle body is
    opposite the initially longest side. -/
theorem maximalNewtonUnion_firstRegularSyzygy_middleBody_of_strictLongest
    (z₀ : Phase) (hcf : CollisionFree z₀.1)
    (hrest : ∀ i, z₀.2 i = 0)
    (harea₀ : signedDoubleArea z₀.1 ≠ 0)
    (i : Fin 3)
    (hlongPrev : sideSq z₀.1 i > sideSq z₀.1 (cyclicPrev i))
    (hlongNext : sideSq z₀.1 i > sideSq z₀.1 (cyclicNext i)) :
    ∃ T ∈ maximalNewtonUnionDomain z₀, 0 < T ∧
      FirstRegularSyzygy (maximalNewtonUnionTrajectory z₀)
        (maximalNewtonUnionDomain z₀) 0 T ∧
      Sbtw ℝ ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i))
        ((maximalNewtonUnionTrajectory z₀ T).1 i)
        ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i)) := by
  let c := centerTranslation z₀.1
  let zC := translatePhase c z₀
  have hcfC : CollisionFree zC.1 := by
    rw [collisionFree_iff_dist_pos]
    intro a b hab
    change 0 < dist (translatePoint c (z₀.1 a))
      (translatePoint c (z₀.1 b))
    rw [translatePoint_dist]
    exact (collisionFree_iff_dist_pos z₀.1).mp hcf a b hab
  have hrestC : ∀ b, zC.2 b = 0 := hrest
  have hcenterC : zC.1 0 + zC.1 1 + zC.1 2 = 0 := by
    simpa [zC, translatePhase] using translateConfiguration_centered z₀.1
  have hareaC : signedDoubleArea zC.1 = signedDoubleArea z₀.1 := by
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
  by_cases hpositive : 0 < signedDoubleArea z₀.1
  · have hareaPositive : 0 < signedDoubleArea zC.1 := by
      rw [hareaC]
      exact hpositive
    obtain ⟨T, hTC, hTpos, hfirstC, hbetweenC⟩ :=
      centeredPositive_firstRegularSyzygy_and_middleBody
        zC hcfC hrestC hcenterC hareaPositive i hlongPrevC hlongNextC
    have hT : T ∈ maximalNewtonUnionDomain z₀ := by
      rw [← maximalNewtonUnionDomain_translate z₀ c]
      exact hTC
    have htraj : maximalNewtonUnionTrajectory zC T =
        translatePhase c (maximalNewtonUnionTrajectory z₀ T) := by
      simpa [zC] using maximalNewtonUnionTrajectory_translate z₀ c hT
    have hfirst : FirstRegularSyzygy
        (maximalNewtonUnionTrajectory z₀) (maximalNewtonUnionDomain z₀) 0 T := by
      refine ⟨hfirstC.1, ?_, ?_, ?_, ?_⟩
      · intro t ht
        rw [← maximalNewtonUnionDomain_translate z₀ c]
        exact hfirstC.2.1 ht
      · have hareaEnd : signedDoubleArea (maximalNewtonUnionTrajectory zC T).1 =
            signedDoubleArea (maximalNewtonUnionTrajectory z₀ T).1 := by
          rw [htraj]
          exact signedDoubleArea_translateConfiguration c
            (maximalNewtonUnionTrajectory z₀ T).1
        exact hareaEnd.symm.trans hfirstC.2.2.1
      · intro t ht hzero
        have hdomt : t ∈ maximalNewtonUnionDomain zC :=
          hfirstC.2.1 ⟨ht.1, le_of_lt ht.2⟩
        have hareaEq : signedDoubleArea (maximalNewtonUnionTrajectory zC t).1 =
            signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 := by
          have hdomt₀ : t ∈ maximalNewtonUnionDomain z₀ := by
            rw [← maximalNewtonUnionDomain_translate z₀ c]
            exact hdomt
          have htrajt := maximalNewtonUnionTrajectory_translate z₀ c hdomt₀
          rw [htrajt]
          exact signedDoubleArea_translateConfiguration c
            (maximalNewtonUnionTrajectory z₀ t).1
        apply hfirstC.2.2.2.1 t ht
        exact hareaEq.trans hzero
      · exact (maximalNewtonUnionTrajectory_solution z₀).2 T hT |>.1
    have hbetweenMap : Sbtw ℝ
        (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i)))
        (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 i))
        (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i))) := by
      rw [htraj] at hbetweenC
      simpa [translatePointAffine, translatePhase, translateConfiguration,
        translatePoint] using hbetweenC
    have hinj : Function.Injective (translatePointAffine c) :=
      translatePointAffine_injective c
    refine ⟨T, hT, hTpos, hfirst, ?_⟩
    exact (Function.Injective.sbtw_map_iff hinj).mp hbetweenMap
  · have hnegative : signedDoubleArea z₀.1 < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpositive) harea₀
    let zR := reflectPhase zC
    have hcfR : CollisionFree zR.1 := by
      rw [collisionFree_iff_dist_pos]
      intro a b hab
      change 0 < dist (reflectPoint (zC.1 a)) (reflectPoint (zC.1 b))
      rw [reflectPoint_dist]
      exact (collisionFree_iff_dist_pos zC.1).mp hcfC a b hab
    have hrestR : ∀ b, zR.2 b = 0 := by
      intro b
      simp [zR, reflectPhase, reflectConfiguration, hrestC b]
    have hcenterR : zR.1 0 + zR.1 1 + zR.1 2 = 0 := by
      have h := congrArg reflectPoint hcenterC
      simpa [zR, reflectPhase, reflectConfiguration, reflectPoint_add] using h
    have hareaR : 0 < signedDoubleArea zR.1 := by
      change 0 < signedDoubleArea (reflectConfiguration zC.1)
      rw [signedDoubleArea_reflectConfiguration, hareaC]
      linarith
    have hlongPrevR : sideSq zR.1 i > sideSq zR.1 (cyclicPrev i) := by
      change sideSq (reflectConfiguration zC.1) i >
        sideSq (reflectConfiguration zC.1) (cyclicPrev i)
      rw [sideSq_reflectConfiguration, sideSq_reflectConfiguration]
      exact hlongPrevC
    have hlongNextR : sideSq zR.1 i > sideSq zR.1 (cyclicNext i) := by
      change sideSq (reflectConfiguration zC.1) i >
        sideSq (reflectConfiguration zC.1) (cyclicNext i)
      rw [sideSq_reflectConfiguration, sideSq_reflectConfiguration]
      exact hlongNextC
    obtain ⟨T, hTR, hTpos, hfirstR, hbetweenR⟩ :=
      centeredPositive_firstRegularSyzygy_and_middleBody
        zR hcfR hrestR hcenterR hareaR i hlongPrevR hlongNextR
    have hTC : T ∈ maximalNewtonUnionDomain zC := by
      rw [maximalNewtonUnionDomain_reflect zC] at hTR
      exact hTR
    have hT : T ∈ maximalNewtonUnionDomain z₀ := by
      rw [← maximalNewtonUnionDomain_translate z₀ c]
      exact hTC
    have htrajC : maximalNewtonUnionTrajectory zC T =
        translatePhase c (maximalNewtonUnionTrajectory z₀ T) := by
      simpa [zC] using maximalNewtonUnionTrajectory_translate z₀ c hT
    have htrajR : maximalNewtonUnionTrajectory zR T =
        reflectPhase (maximalNewtonUnionTrajectory zC T) := by
      simpa [zR] using maximalNewtonUnionTrajectory_reflect zC
        hTC
    have hfirst : FirstRegularSyzygy
        (maximalNewtonUnionTrajectory z₀) (maximalNewtonUnionDomain z₀) 0 T := by
      refine ⟨hfirstR.1, ?_, ?_, ?_, ?_⟩
      · intro t ht
        rw [← maximalNewtonUnionDomain_translate z₀ c,
          ← maximalNewtonUnionDomain_reflect zC]
        exact hfirstR.2.1 ht
      · have hareaEnd : signedDoubleArea (maximalNewtonUnionTrajectory zR T).1 =
            - signedDoubleArea (maximalNewtonUnionTrajectory z₀ T).1 := by
          rw [htrajR, htrajC]
          change signedDoubleArea
              (reflectConfiguration (translateConfiguration c
                (maximalNewtonUnionTrajectory z₀ T).1)) = _
          rw [signedDoubleArea_reflectConfiguration,
            signedDoubleArea_translateConfiguration]
        linarith [hareaEnd, hfirstR.2.2.1]
      · intro t ht hzero
        have hdomt : t ∈ maximalNewtonUnionDomain zR :=
          hfirstR.2.1 ⟨ht.1, le_of_lt ht.2⟩
        have hdomtC : t ∈ maximalNewtonUnionDomain zC := by
          rw [maximalNewtonUnionDomain_reflect zC] at hdomt
          exact hdomt
        have hdomt₀ : t ∈ maximalNewtonUnionDomain z₀ := by
          rw [← maximalNewtonUnionDomain_translate z₀ c]
          exact hdomtC
        have htrajtR := maximalNewtonUnionTrajectory_reflect zC hdomtC
        have htrajtC := maximalNewtonUnionTrajectory_translate z₀ c hdomt₀
        have hareaEq : signedDoubleArea (maximalNewtonUnionTrajectory zR t).1 =
            - signedDoubleArea (maximalNewtonUnionTrajectory z₀ t).1 := by
          rw [htrajtR, htrajtC]
          change signedDoubleArea
              (reflectConfiguration (translateConfiguration c
                (maximalNewtonUnionTrajectory z₀ t).1)) = _
          rw [signedDoubleArea_reflectConfiguration,
            signedDoubleArea_translateConfiguration]
        apply hfirstR.2.2.2.1 t ht
        have hzeroR : signedDoubleArea (maximalNewtonUnionTrajectory zR t).1 = 0 := by
          rw [hareaEq, hzero]
          simp
        exact hzeroR
      · exact (maximalNewtonUnionTrajectory_solution z₀).2 T hT |>.1
    have hbetweenReflect : Sbtw ℝ
        (reflectPoint ((translatePhase c
          (maximalNewtonUnionTrajectory z₀ T)).1 (cyclicPrev i)))
        (reflectPoint ((translatePhase c
          (maximalNewtonUnionTrajectory z₀ T)).1 i))
        (reflectPoint ((translatePhase c
          (maximalNewtonUnionTrajectory z₀ T)).1 (cyclicNext i))) := by
      rw [htrajR] at hbetweenR
      rw [htrajC] at hbetweenR
      simpa [reflectPhase, reflectConfiguration] using hbetweenR
    have hinjR : Function.Injective reflectPointAffine := by
      intro x y hxy
      apply reflectPoint_injective
      simpa using hxy
    have hbetweenC : Sbtw ℝ
        ((translatePhase c (maximalNewtonUnionTrajectory z₀ T)).1 (cyclicPrev i))
        ((translatePhase c (maximalNewtonUnionTrajectory z₀ T)).1 i)
        ((translatePhase c (maximalNewtonUnionTrajectory z₀ T)).1 (cyclicNext i)) :=
      (Function.Injective.sbtw_map_iff hinjR).mp
        (by simpa [reflectPointAffine, reflectPointLinear] using hbetweenReflect)
    have hinjT : Function.Injective (translatePointAffine c) :=
      translatePointAffine_injective c
    have hbetweenMap : Sbtw ℝ
        (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicPrev i)))
        (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 i))
        (translatePointAffine c ((maximalNewtonUnionTrajectory z₀ T).1 (cyclicNext i))) := by
      simpa [translatePointAffine, translatePhase, translateConfiguration,
        translatePoint] using hbetweenC
    refine ⟨T, hT, hTpos, hfirst, ?_⟩
    exact (Function.Injective.sbtw_map_iff hinjT).mp hbetweenMap

end

end DroppingThreeBodies
