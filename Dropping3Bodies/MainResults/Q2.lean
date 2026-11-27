module

public import Dropping3Bodies.Dynamics.CompleteEqualMassResult
public import Dropping3Bodies.Dynamics.GeneralReflectionSymmetry
public import Dropping3Bodies.Dynamics.TranslationSymmetry
public import Dropping3Bodies.Geometry.Betweenness
public import Dropping3Bodies.Geometry.ScaleneSideSelection

@[expose] public section

/-! Public Q2 assembly for arbitrary scalene rest data with positive common
mass and gravitational constant. The centered positive-orientation event
certificate is transported by translation, reflection, and (inside its
centered core) gravity time-rescaling. -/

namespace DroppingThreeBodies

noncomputable section

/-- The general Newton field is invariant under translating all positions. -/
theorem generalNewtonField_translatePhase (G : ℝ) (m : Fin 3 → ℝ)
    (c : Point) (z : Phase) :
    generalNewtonField G m (translatePhase c z) = generalNewtonField G m z := by
  cases z with
  | mk q v =>
      apply Prod.ext
      · rfl
      · funext i
        simp [generalNewtonField, generalAcceleration, translatePhase,
          translateConfiguration, translatePoint, inverseCubeDistance,
          add_sub_add_right_eq_sub]

/-- Translating a general-mass solution yields a solution on the same domain. -/
theorem generalClassicalNewtonSolution_translate
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (c : Point) (hsol : GeneralClassicalNewtonSolution G m z I) :
    GeneralClassicalNewtonSolution G m (fun t => translatePhase c (z t)) I := by
  refine ⟨hsol.1, fun t ht => ?_⟩
  obtain ⟨hcf, hderiv⟩ := hsol.2 t ht
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply dist_pos.mp
    change dist (translateConfiguration c (z t).1 i)
      (translateConfiguration c (z t).1 j) > 0
    rw [dist_translateConfiguration]
    exact dist_pos.mpr (hcf i j hij)
  · have hshift : HasDerivAt (fun _ : ℝ => translationPhaseShift c) 0 t :=
      hasDerivAt_const t (translationPhaseShift c)
    have hsum := hderiv.add hshift
    have hcurve : (fun s => translatePhase c (z s)) =
        z + fun _ : ℝ => translationPhaseShift c := by
      funext s
      exact translatePhase_eq_add_shift c (z s)
    have hsum' : HasDerivAt (fun s => translatePhase c (z s))
        (generalNewtonField G m (z t)) t := by
      simpa [hcurve] using hsum
    rw [generalNewtonField_translatePhase]
    exact hsum'

/-- Center a configuration by translation to its centroid. -/
def centroidShift (q : Fin 3 → Point) : Point :=
  -configurationCentroid q

def centroidTranslateConfiguration (q : Fin 3 → Point) : Fin 3 → Point :=
  translateConfiguration (centroidShift q) q

theorem centroidTranslateConfiguration_centered (q : Fin 3 → Point) :
    (centroidTranslateConfiguration q) 0 +
      (centroidTranslateConfiguration q) 1 +
      (centroidTranslateConfiguration q) 2 = 0 := by
  simp [centroidTranslateConfiguration, centroidShift, translateConfiguration,
    translatePoint, configurationCentroid]
  module

/-- For any scalene noncollinear configuration with positive orientation,
there is a common-mass first-regular-syzygy certificate with all side-square
comparisons preserved. -/
theorem exists_completePaperQ2_commonMass_scalene_positiveArea
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ)
    (q : Fin 3 → Point) (hcf : CollisionFree q)
    (harea : 0 < signedDoubleArea q)
    (hscalene : ScaleneConfiguration q) :
    ∃ (z : ℝ → Phase) (I : Set ℝ) (T : ℝ),
      GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ) z I ∧
      z 0 = (q, fun _ => (0 : Point)) ∧ 0 ∈ I ∧ T ∈ I ∧
      FirstRegularSyzygy z I 0 T ∧
      ∃ i : Fin 3,
        Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i) ((z T).1 (cyclicNext i)) ∧
        (∀ t ∈ Set.Icc 0 T,
          sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
          sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
          ((0 < sideGap q i ∧ 0 < sideGap (z t).1 i) ∨
            (sideGap q i < 0 ∧ sideGap (z t).1 i < 0))) ∧
        (∀ j k, sideSq q j < sideSq q k →
          ∀ t ∈ Set.Icc 0 T, sideSq (z t).1 j < sideSq (z t).1 k) := by
  obtain ⟨i, hlong⟩ := exists_strictly_largest_sideSq q hscalene
  have hshort : sideSq q (cyclicPrev i) ≠ sideSq q (cyclicNext i) :=
    hscalene _ _ (cyclicPrev_ne_cyclicNext i)
  let c := centroidShift q
  let qC := centroidTranslateConfiguration q
  let zC₀ : Phase := (qC, fun _ => (0 : Point))
  have hcfC : CollisionFree qC := by
    intro j k hjk
    apply dist_pos.mp
    change dist (translateConfiguration c q j)
      (translateConfiguration c q k) > 0
    rw [dist_translateConfiguration]
    exact dist_pos.mpr (hcf j k hjk)
  have hareaC : 0 < signedDoubleArea qC := by
    change 0 < signedDoubleArea (translateConfiguration c q)
    rw [signedDoubleArea_translateConfiguration]
    exact harea
  have hcenterC : qC 0 + qC 1 + qC 2 = 0 := centroidTranslateConfiguration_centered q
  have hlongCPrev : sideSq qC i > sideSq qC (cyclicPrev i) := by
    change sideSq (translateConfiguration c q) i >
      sideSq (translateConfiguration c q) (cyclicPrev i)
    rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
    exact hlong (cyclicPrev i) (cyclicPrev_ne_self i)
  have hlongCNext : sideSq qC i > sideSq qC (cyclicNext i) := by
    change sideSq (translateConfiguration c q) i >
      sideSq (translateConfiguration c q) (cyclicNext i)
    rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
    exact hlong (cyclicNext i) (cyclicNext_ne_self i)
  have hshortC : sideSq qC (cyclicPrev i) ≠ sideSq qC (cyclicNext i) := by
    change sideSq (translateConfiguration c q) (cyclicPrev i) ≠
      sideSq (translateConfiguration c q) (cyclicNext i)
    rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
    exact hshort
  obtain ⟨zC, IC, TC, hsolC, hinitC, hzeroC, hTmemC, hfirstC,
    hbetweenC, hordersC, hpairC⟩ :=
    exists_completePaperQ2_commonMass_centered_positive G μ hG hμ zC₀
      hcfC (by intro b; simp [zC₀]) hcenterC hareaC i hshortC
      hlongCPrev hlongCNext
  let z := fun t => translatePhase (-c) (zC t)
  have hsol := generalClassicalNewtonSolution_translate (-c) hsolC
  have hzero : (0 : ℝ) ∈ IC := hzeroC
  have hTmem : TC ∈ IC := hTmemC
  have hinit : z 0 = (q, fun _ => (0 : Point)) := by
    dsimp [z, zC₀] at hinitC ⊢
    rw [hinitC]
    apply Prod.ext
    · funext j
      change translatePoint (-c) (translatePoint c (q j)) = q j
      simp [translatePoint]
    · funext j
      change (fun _ : Fin 3 => (0 : Point)) j = 0
      simp
  have hfirst : FirstRegularSyzygy z IC 0 TC := by
    rcases hfirstC with ⟨hTCpos, hsegmentC, hareaTC, hpreC, hcfTC⟩
    refine ⟨hTCpos, hsegmentC, ?_, ?_, ?_⟩
    · change signedDoubleArea (translateConfiguration (-c) (zC TC).1) = 0
      rw [signedDoubleArea_translateConfiguration]
      exact hareaTC
    · intro t ht
      have h := hpreC t ht
      simpa [z, translatePhase, signedDoubleArea_translateConfiguration] using h
    · intro j k hjk
      apply dist_pos.mp
      change dist (translateConfiguration (-c) (zC TC).1 j)
        (translateConfiguration (-c) (zC TC).1 k) > 0
      rw [dist_translateConfiguration]
      exact dist_pos.mpr (hcfTC j k hjk)
  have horders : ∀ t ∈ Set.Icc 0 TC,
      sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
      sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
      ((0 < sideGap q i ∧ 0 < sideGap (z t).1 i) ∨
        (sideGap q i < 0 ∧ sideGap (z t).1 i < 0)) := by
    intro t ht
    have h := hordersC t ht
    rcases h with ⟨hprev, hnext, hgap⟩
    refine ⟨?_, ?_, ?_⟩
    · change sideSq (translateConfiguration (-c) (zC t).1) i >
        sideSq (translateConfiguration (-c) (zC t).1) (cyclicPrev i)
      rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
      exact hprev
    · change sideSq (translateConfiguration (-c) (zC t).1) i >
        sideSq (translateConfiguration (-c) (zC t).1) (cyclicNext i)
      rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
      exact hnext
    · have hgapInit : sideGap qC i = sideGap q i := by
        rw [sideGap_eq_next_sub_prev_sideSq, sideGap_eq_next_sub_prev_sideSq]
        change sideSq (translateConfiguration c q) (cyclicNext i) -
            sideSq (translateConfiguration c q) (cyclicPrev i) = _
        rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
      have hgapNow : sideGap (translateConfiguration (-c) (zC t).1) i =
          sideGap (zC t).1 i := by
        rw [sideGap_eq_next_sub_prev_sideSq, sideGap_eq_next_sub_prev_sideSq]
        rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
      rcases hgap with (⟨hinitg, hnowg⟩ | ⟨hinitg, hnowg⟩)
      · have hinit' : 0 < sideGap q i := by rw [← hgapInit]; exact hinitg
        have hnow' : 0 < sideGap (z t).1 i := by
          change 0 < sideGap (translateConfiguration (-c) (zC t).1) i
          rw [hgapNow]
          exact hnowg
        exact Or.inl ⟨hinit', hnow'⟩
      · have hinit' : sideGap q i < 0 := by rw [← hgapInit]; exact hinitg
        have hnow' : sideGap (z t).1 i < 0 := by
          change sideGap (translateConfiguration (-c) (zC t).1) i < 0
          rw [hgapNow]
          exact hnowg
        exact Or.inr ⟨hinit', hnow'⟩
  have hpairwise : ∀ j k, sideSq q j < sideSq q k →
      ∀ t ∈ Set.Icc 0 TC, sideSq (z t).1 j < sideSq (z t).1 k := by
    intro j k hjk t ht
    have hjkC : sideSq qC j < sideSq qC k := by
      change sideSq (translateConfiguration c q) j <
        sideSq (translateConfiguration c q) k
      rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
      exact hjk
    have h := hpairC j k hjkC t ht
    change sideSq (translateConfiguration (-c) (zC t).1) j <
      sideSq (translateConfiguration (-c) (zC t).1) k
    rw [sideSq_translateConfiguration, sideSq_translateConfiguration]
    exact h
  have hordersT := horders TC ⟨le_of_lt hfirst.1, le_rfl⟩
  have hlongPrevDist :
      dist ((z TC).1 (cyclicPrev i)) ((z TC).1 (cyclicNext i)) ^ 2 ≥
        dist ((z TC).1 i) ((z TC).1 (cyclicPrev i)) ^ 2 := by
    have hbase := sideSq_eq_cyclicNeighborDistance (z TC).1 i
    have hside : sideSq (z TC).1 (cyclicNext i) =
        dist ((z TC).1 i) ((z TC).1 (cyclicPrev i)) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      simp [cyclicPrev_cyclicNext, cyclicNext_cyclicNext]
    rw [← hbase, ← hside]
    exact le_of_lt hordersT.2.1
  have hlongNextDist :
      dist ((z TC).1 (cyclicPrev i)) ((z TC).1 (cyclicNext i)) ^ 2 ≥
        dist ((z TC).1 (cyclicNext i)) ((z TC).1 i) ^ 2 := by
    have hbase := sideSq_eq_cyclicNeighborDistance (z TC).1 i
    have hside : sideSq (z TC).1 (cyclicPrev i) =
        dist ((z TC).1 (cyclicNext i)) ((z TC).1 i) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance]
      simp [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev]
    rw [← hbase, ← hside]
    exact le_of_lt hordersT.1
  have hdistinct : ∀ j k, j ≠ k → (z TC).1 j ≠ (z TC).1 k := by
    intro j k hjk heq
    have hpos := hfirst.2.2.2.2 j k hjk
    exact hpos heq
  have hbetween := sbtw_of_longest_opposite_side (z TC).1 i
    hfirst.2.2.1 hdistinct hlongPrevDist hlongNextDist
  refine ⟨z, IC, TC, hsol, hinit, hzero, hTmem, hfirst,
    i, hbetween, horders, hpairwise⟩

/-- Orientation-free common-mass Q2 certificate for an arbitrary scalene
noncollinear rest configuration. The negative orientation is reduced by
reflection, preserving all labels and side comparisons. -/
theorem exists_completePaperQ2_commonMass_scalene
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ)
    (q : Fin 3 → Point) (hcf : CollisionFree q)
    (harea : signedDoubleArea q ≠ 0)
    (hscalene : ScaleneConfiguration q) :
    ∃ (z : ℝ → Phase) (I : Set ℝ) (T : ℝ),
      GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ) z I ∧
      z 0 = (q, fun _ => (0 : Point)) ∧ 0 ∈ I ∧ T ∈ I ∧
      FirstRegularSyzygy z I 0 T ∧
      ∃ i : Fin 3,
        Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i) ((z T).1 (cyclicNext i)) ∧
        (∀ t ∈ Set.Icc 0 T,
          sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
          sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
          ((0 < sideGap q i ∧ 0 < sideGap (z t).1 i) ∨
            (sideGap q i < 0 ∧ sideGap (z t).1 i < 0))) ∧
        (∀ j k, sideSq q j < sideSq q k →
          ∀ t ∈ Set.Icc 0 T, sideSq (z t).1 j < sideSq (z t).1 k) := by
  rcases lt_or_gt_of_ne harea with hareaNeg | hareaPos
  · let qR := reflectConfiguration q
    have hcfR : CollisionFree qR := by
      intro j k hjk heq
      apply hcf j k hjk
      apply reflectPoint_injective
      simpa [qR, reflectConfiguration] using heq
    have hareaR : 0 < signedDoubleArea qR := by
      rw [show qR = reflectConfiguration q by rfl,
        signedDoubleArea_reflectConfiguration]
      linarith
    have hscaleneR : ScaleneConfiguration qR := by
      intro j k hjk
      rw [show qR = reflectConfiguration q by rfl,
        sideSq_reflectConfiguration, sideSq_reflectConfiguration]
      exact hscalene j k hjk
    obtain ⟨zR, IR, TR, hsolR, hinitR, hzeroR, hTRmem, hfirstR,
      ⟨i, hbetweenR, hordersR, hpairR⟩⟩ :=
      exists_completePaperQ2_commonMass_scalene_positiveArea G μ hG hμ
        qR hcfR hareaR hscaleneR
    let z := fun t => reflectGeneralPhase (zR t)
    have hsol := generalClassicalNewtonSolution_reflect hsolR
    have hinit : z 0 = (q, fun _ => (0 : Point)) := by
      dsimp [z]
      rw [hinitR]
      apply Prod.ext
      · funext j
        change reflectPoint (reflectPoint (q j)) = q j
        exact reflectPoint_involutive (q j)
      · funext j
        simp [reflectGeneralPhase, reflectConfiguration]
    have hfirst : FirstRegularSyzygy z IR 0 TR := by
      rcases hfirstR with ⟨hTRpos, hsegmentR, hareaTR, hpreR, hcfTR⟩
      refine ⟨hTRpos, hsegmentR, ?_, ?_, ?_⟩
      · change signedDoubleArea (reflectConfiguration (zR TR).1) = 0
        rw [signedDoubleArea_reflectConfiguration]
        linarith
      · intro t ht
        have h := hpreR t ht
        change signedDoubleArea (reflectConfiguration (zR t).1) ≠ 0
        rw [signedDoubleArea_reflectConfiguration]
        exact fun heq => h (by linarith)
      · intro j k hjk heq
        have hback : (zR TR).1 j = (zR TR).1 k := by
          apply reflectPoint_injective
          simpa [z, reflectGeneralPhase, reflectConfiguration] using heq
        exact hcfTR j k hjk hback
    have horders : ∀ t ∈ Set.Icc 0 TR,
        sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
        sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
        ((0 < sideGap q i ∧ 0 < sideGap (z t).1 i) ∨
          (sideGap q i < 0 ∧ sideGap (z t).1 i < 0)) := by
      intro t ht
      rcases hordersR t ht with ⟨hprev, hnext, hgap⟩
      have hgapInit : sideGap qR i = sideGap q i := by
        rw [sideGap_eq_next_sub_prev_sideSq, sideGap_eq_next_sub_prev_sideSq,
          sideSq_reflectConfiguration, sideSq_reflectConfiguration]
      have hgapNow : sideGap (reflectConfiguration (zR t).1) i =
          sideGap (zR t).1 i := by
        rw [sideGap_eq_next_sub_prev_sideSq, sideGap_eq_next_sub_prev_sideSq,
          sideSq_reflectConfiguration, sideSq_reflectConfiguration]
      refine ⟨?_, ?_, ?_⟩
      · change sideSq (reflectConfiguration (zR t).1) i >
          sideSq (reflectConfiguration (zR t).1) (cyclicPrev i)
        rw [sideSq_reflectConfiguration, sideSq_reflectConfiguration]
        exact hprev
      · change sideSq (reflectConfiguration (zR t).1) i >
          sideSq (reflectConfiguration (zR t).1) (cyclicNext i)
        rw [sideSq_reflectConfiguration, sideSq_reflectConfiguration]
        exact hnext
      · rcases hgap with (⟨hinitg, hnowg⟩ | ⟨hinitg, hnowg⟩)
        · have hinit' : 0 < sideGap q i := by rw [← hgapInit]; exact hinitg
          have hnow' : 0 < sideGap (z t).1 i := by
            change 0 < sideGap (reflectConfiguration (zR t).1) i
            rw [hgapNow]
            exact hnowg
          exact Or.inl ⟨hinit', hnow'⟩
        · have hinit' : sideGap q i < 0 := by rw [← hgapInit]; exact hinitg
          have hnow' : sideGap (z t).1 i < 0 := by
            change sideGap (reflectConfiguration (zR t).1) i < 0
            rw [hgapNow]
            exact hnowg
          exact Or.inr ⟨hinit', hnow'⟩
    have hpairwise : ∀ j k, sideSq q j < sideSq q k →
        ∀ t ∈ Set.Icc 0 TR, sideSq (z t).1 j < sideSq (z t).1 k := by
      intro j k hjk t ht
      have hjkR : sideSq qR j < sideSq qR k := by
        rw [show qR = reflectConfiguration q by rfl,
          sideSq_reflectConfiguration, sideSq_reflectConfiguration]
        exact hjk
      have h := hpairR j k hjkR t ht
      change sideSq (reflectConfiguration (zR t).1) j <
        sideSq (reflectConfiguration (zR t).1) k
      rw [sideSq_reflectConfiguration, sideSq_reflectConfiguration]
      exact h
    have hordersT := horders TR ⟨le_of_lt hfirst.1, le_rfl⟩
    have hlongPrevDist :
        dist ((z TR).1 (cyclicPrev i)) ((z TR).1 (cyclicNext i)) ^ 2 ≥
          dist ((z TR).1 i) ((z TR).1 (cyclicPrev i)) ^ 2 := by
      have hbase := sideSq_eq_cyclicNeighborDistance (z TR).1 i
      have hside : sideSq (z TR).1 (cyclicNext i) =
          dist ((z TR).1 i) ((z TR).1 (cyclicPrev i)) ^ 2 := by
        rw [sideSq_eq_cyclicNeighborDistance]
        simp [cyclicPrev_cyclicNext, cyclicNext_cyclicNext]
      rw [← hbase, ← hside]
      exact le_of_lt hordersT.2.1
    have hlongNextDist :
        dist ((z TR).1 (cyclicPrev i)) ((z TR).1 (cyclicNext i)) ^ 2 ≥
          dist ((z TR).1 (cyclicNext i)) ((z TR).1 i) ^ 2 := by
      have hbase := sideSq_eq_cyclicNeighborDistance (z TR).1 i
      have hside : sideSq (z TR).1 (cyclicPrev i) =
          dist ((z TR).1 (cyclicNext i)) ((z TR).1 i) ^ 2 := by
        rw [sideSq_eq_cyclicNeighborDistance]
        simp [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev]
      rw [← hbase, ← hside]
      exact le_of_lt hordersT.1
    have hdistinct : ∀ j k, j ≠ k → (z TR).1 j ≠ (z TR).1 k := by
      intro j k hjk heq
      exact hfirst.2.2.2.2 j k hjk heq
    have hbetween := sbtw_of_longest_opposite_side (z TR).1 i
      hfirst.2.2.1 hdistinct hlongPrevDist hlongNextDist
    exact ⟨z, IR, TR, hsol, hinit, hzeroR, hTRmem, hfirst,
      i, hbetween, horders, hpairwise⟩
  · exact exists_completePaperQ2_commonMass_scalene_positiveArea G μ hG hμ
      q hcf hareaPos hscalene

/-- Public initial-data form of the orientation-free common-mass Q2 theorem.
The labels of the three bodies are retained, and the returned trajectory
starts at the supplied positions with all velocities zero. -/
theorem exists_completePaperQ2_initialData_commonMass_scalene
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ)
    (d : InitialData) (hmass : ∀ i, d.mass i = μ)
    (hscalene : ScaleneConfiguration d.position) :
    ∃ (z : ℝ → Phase) (I : Set ℝ) (T : ℝ),
      GeneralClassicalNewtonSolution G d.mass z I ∧
      z 0 = (d.position, initialVelocity d) ∧ 0 ∈ I ∧ T ∈ I ∧
      FirstRegularSyzygy z I 0 T ∧
      ∃ i : Fin 3,
        Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i) ((z T).1 (cyclicNext i)) ∧
        (∀ t ∈ Set.Icc 0 T,
          sideSq (z t).1 i > sideSq (z t).1 (cyclicPrev i) ∧
          sideSq (z t).1 i > sideSq (z t).1 (cyclicNext i) ∧
          ((0 < sideGap d.position i ∧ 0 < sideGap (z t).1 i) ∨
            (sideGap d.position i < 0 ∧ sideGap (z t).1 i < 0))) ∧
        (∀ j k, sideSq d.position j < sideSq d.position k →
          ∀ t ∈ Set.Icc 0 T, sideSq (z t).1 j < sideSq (z t).1 k) := by
  have hcf : CollisionFree d.position := d.pairwise_distinct
  obtain ⟨z, I, T, hsol, hinit, hzero, hTmem, hfirst,
    ⟨i, hbetween, horders, hpairwise⟩⟩ :=
    exists_completePaperQ2_commonMass_scalene G μ hG hμ d.position hcf
      d.noncollinear hscalene
  have hmassEq : (fun _ : Fin 3 => μ) = d.mass := funext fun i => (hmass i).symm
  have hsolD : GeneralClassicalNewtonSolution G d.mass z I := by
    rw [← hmassEq]
    exact hsol
  refine ⟨z, I, T, hsolD, ?_, hzero, hTmem, hfirst,
    i, hbetween, horders, hpairwise⟩
  change z 0 = (d.position, fun _ => (0 : Point))
  exact hinit

end

end DroppingThreeBodies
