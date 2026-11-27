module

public import Dropping3Bodies.EqualMass.SolutionCooperativeSystem
public import Dropping3Bodies.Support.CooperativePair
public import Dropping3Bodies.Support.CooperativeUniqueness
public import Dropping3Bodies.Support.IntervalEndpoint
public import Dropping3Bodies.Geometry.SyzygyMidpoint
public import Dropping3Bodies.Geometry.Betweenness
public import Mathlib.Tactic

@[expose] public section

namespace DroppingThreeBodies

/-- The positive coefficient multiplying Y in the normalized-gap equation. -/
noncomputable def sideGapCoefficientX
    (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) /
    (signedDoubleArea (z t).1) ^ 2

/-- The positive coefficient multiplying X in the negative-rotation equation. -/
noncomputable def sideGapCoefficientY
    (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  (signedDoubleArea (z t).1) ^ 2 *
    inverseCubeGapFactor
      (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
      (dist ((z t).1 (cyclicNext i)) ((z t).1 i))

/-- A classical phase-space trajectory is continuous on every compact interval
    contained in its solution domain. -/
theorem classicalNewton_continuousOn_phase
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I)
    {a T : ℝ} (hsegment : Set.Icc a T ⊆ I) :
    ContinuousOn z (Set.Icc a T) := by
  intro t ht
  exact ((hsol.2 t (hsegment ht)).2.continuousAt.continuousWithinAt)

/-- Both scalar coefficient functions in the cooperative Newton system are
    continuous on every compact collision-free segment of positive area. -/
theorem classicalNewton_sideGap_coefficients_continuousOn
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I)
    {a T : ℝ} (hsegment : Set.Icc a T ⊆ I)
    (i : Fin 3)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ContinuousOn (sideGapCoefficientX z i) (Set.Icc a T) ∧
    ContinuousOn (sideGapCoefficientY z i) (Set.Icc a T) := by
  let J := Set.Icc a T
  have hphase : ContinuousOn z J := classicalNewton_continuousOn_phase hsol hsegment
  have hposition : ContinuousOn (fun t => (z t).1) J := hphase.fst
  have hq (b : Fin 3) : ContinuousOn (fun t => (z t).1 b) J := by
    have happly := (continuousOn_apply b Set.univ).comp hposition
      (by intro t ht; trivial)
    convert happly using 1
    ext t
    rfl
  have hmoment : ContinuousOn
      (fun t => frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i)) J := by
    fin_cases i <;> simp [frameMoment, sideVector, sideOffset] <;> fun_prop
  have hareaCont : ContinuousOn (fun t => signedDoubleArea (z t).1) J := by
    simp only [signedDoubleArea, cross]
    fun_prop
  have hdenX : ContinuousOn (fun t => (signedDoubleArea (z t).1) ^ 2) J := by
    fun_prop
  have hcoeffX : ContinuousOn
      (fun t => 3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) /
        (signedDoubleArea (z t).1) ^ 2) J := by
    apply (continuousOn_const.mul hmoment).div hdenX
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (harea t ht))
  have hdistX : ContinuousOn
      (fun t => dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) J := by
    fun_prop
  have hdistY : ContinuousOn
      (fun t => dist ((z t).1 (cyclicNext i)) ((z t).1 i)) J := by
    fun_prop
  have hdistXpos : ∀ t ∈ J, 0 < dist ((z t).1 (cyclicPrev i)) ((z t).1 i) := by
    intro t ht
    exact (collisionFree_iff_dist_pos (z t).1).1
      (hsol.2 t (hsegment ht)).1 (cyclicPrev i) i (by fin_cases i <;> decide)
  have hdistYpos : ∀ t ∈ J, 0 < dist ((z t).1 (cyclicNext i)) ((z t).1 i) := by
    intro t ht
    exact (collisionFree_iff_dist_pos (z t).1).1
      (hsol.2 t (hsegment ht)).1 (cyclicNext i) i (by fin_cases i <;> decide)
  have hfactor : ContinuousOn
      (fun t => inverseCubeGapFactor
        (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
        (dist ((z t).1 (cyclicNext i)) ((z t).1 i))) J := by
    unfold inverseCubeGapFactor
    apply (by fun_prop : ContinuousOn
      (fun t => (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 +
        dist ((z t).1 (cyclicPrev i)) ((z t).1 i) *
          dist ((z t).1 (cyclicNext i)) ((z t).1 i) +
        (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) ^ 2) J).div
      (by fun_prop : ContinuousOn
        (fun t => (dist ((z t).1 (cyclicPrev i)) ((z t).1 i) +
          dist ((z t).1 (cyclicNext i)) ((z t).1 i)) *
            (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 3 *
            (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) ^ 3) J)
    intro t ht
    have hx := hdistXpos t ht
    have hy := hdistYpos t ht
    positivity
  have hcoeffY : ContinuousOn
      (fun t => (signedDoubleArea (z t).1) ^ 2 *
        inverseCubeGapFactor
          (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
          (dist ((z t).1 (cyclicNext i)) ((z t).1 i))) J := by
    fun_prop
  constructor
  · change ContinuousOn
      (fun t => 3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) /
        (signedDoubleArea (z t).1) ^ 2) (Set.Icc a T)
    exact hcoeffX
  · change ContinuousOn
      (fun t => (signedDoubleArea (z t).1) ^ 2 *
        inverseCubeGapFactor
          (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
          (dist ((z t).1 (cyclicNext i)) ((z t).1 i))) (Set.Icc a T)
    exact hcoeffY

/-- The cooperative coefficients have a common finite absolute bound on a
    compact positive-area solution interval. -/
theorem classicalNewton_sideGap_coefficients_boundedOn_Icc
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I)
    {a T : ℝ} (hsegment : Set.Icc a T ⊆ I)
    (i : Fin 3) (haT : a ≤ T)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc a T,
      |sideGapCoefficientX z i t| ≤ K ∧
      |sideGapCoefficientY z i t| ≤ K := by
  have hcoeff := classicalNewton_sideGap_coefficients_continuousOn
    hsol hsegment i harea
  let C := fun t => max |sideGapCoefficientX z i t| |sideGapCoefficientY z i t|
  have hcx : ContinuousOn (fun t => |sideGapCoefficientX z i t|)
      (Set.Icc a T) := hcoeff.1.abs
  have hcy : ContinuousOn (fun t => |sideGapCoefficientY z i t|)
      (Set.Icc a T) := hcoeff.2.abs
  have hC : ContinuousOn C (Set.Icc a T) := by
    dsimp [C]
    fun_prop
  have hcompact : IsCompact (C '' Set.Icc a T) :=
    isCompact_Icc.image_of_continuousOn hC
  obtain ⟨K, hK⟩ := hcompact.bddAbove
  change ∀ y ∈ C '' Set.Icc a T, y ≤ K at hK
  have haIcc : a ∈ Set.Icc a T := ⟨le_rfl, haT⟩
  have hKnonneg : 0 ≤ K := by
    have hval := hK (C a) ⟨a, haIcc, rfl⟩
    dsimp [C] at hval
    exact le_trans (le_max_of_le_left (abs_nonneg _)) hval
  refine ⟨K, hKnonneg, ?_⟩
  intro t ht
  have hval := hK (C t) ⟨t, ht, rfl⟩
  dsimp [C] at hval
  exact ⟨le_trans (le_max_left _ _) hval, le_trans (le_max_right _ _) hval⟩

/-- On a positive-area compact trajectory segment, the two cooperative
    variables are continuous. The quotient is continuous because its signed
    area denominator never vanishes. -/
theorem classicalNewton_sideGap_variables_continuousOn
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I)
    {a T : ℝ} (hsegment : Set.Icc a T ⊆ I)
    (i : Fin 3)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ContinuousOn (sideGapRatioCurve (solutionPositionCurve z) i)
      (Set.Icc a T) ∧
    ContinuousOn
      (sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i) (Set.Icc a T) := by
  let J := Set.Icc a T
  have hphase : ContinuousOn z J := classicalNewton_continuousOn_phase hsol hsegment
  have hposition : ContinuousOn (fun t => (z t).1) J := hphase.fst
  have hvelocity : ContinuousOn (fun t => (z t).2) J := hphase.snd
  have hq (b : Fin 3) : ContinuousOn (fun t => (z t).1 b) J := by
    have happly := (continuousOn_apply b Set.univ).comp hposition
      (by intro t ht; trivial)
    convert happly using 1
    ext t
    rfl
  have hv (b : Fin 3) : ContinuousOn (fun t => (z t).2 b) J := by
    have happly := (continuousOn_apply b Set.univ).comp hvelocity
      (by intro t ht; trivial)
    convert happly using 1
    ext t
    rfl
  have hgap : ContinuousOn (fun t => sideGap (z t).1 i) J := by
    fin_cases i <;> simp only [sideGap] <;> fun_prop
  have hareaCont : ContinuousOn (fun t => signedDoubleArea (z t).1) J := by
    simp only [signedDoubleArea, cross]
    fun_prop
  have hratio : ContinuousOn
      (fun t => sideGap (z t).1 i / signedDoubleArea (z t).1) J := by
    apply hgap.div hareaCont
    intro t ht
    exact ne_of_gt (harea t ht)
  have hrotation : ContinuousOn
      (fun t => sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t) J := by
    fin_cases i <;>
      simp [sideGapRotationSignCurve, sidePairRotationCurve, sideVectorCurve,
        solutionPositionCurve, solutionVelocityCurve, sideVector, cross] <;>
      fun_prop
  constructor
  · apply hratio.congr
    intro t ht
    simpa [solutionPositionCurve] using
      (sideGapRatioCurve_eq_sideGap_div_signedDoubleArea
        (solutionPositionCurve z) i t)
  · simpa only [J] using hrotation

/-- Interval ordering theorem under continuity of the Newton cooperative
    variables. The trajectory-level corollary below derives that continuity
    from classical-solution differentiability and positive signed area. -/
theorem classicalNewton_sideGap_positive_on_Icc_of_continuous
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 < sideGap (z a).1 i)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1)
    (hXcont : ContinuousOn (sideGapRatioCurve (solutionPositionCurve z) i)
      (Set.Icc a T))
    (hYcont : ContinuousOn
      (sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i) (Set.Icc a T)) :
    ∀ t ∈ Set.Icc a T, 0 < sideGap (z t).1 i := by
  have ha : a ∈ I := hsegment ⟨le_rfl, haT.le⟩
  have hX₀ : 0 < sideGapRatioCurve (solutionPositionCurve z) i a := by
    exact sideGapRatio_pos_of_sideGap_pos (solutionPositionCurve z) i a hgap₀
      (by simpa [solutionPositionCurve] using harea a ⟨le_rfl, haT.le⟩)
  have hY₀ : sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i a = 0 :=
    sideGapRotationSign_eq_zero_of_rest i a hrest
  have hderivX : ∀ t ∈ Set.Icc a T,
      HasDerivAt (sideGapRatioCurve (solutionPositionCurve z) i)
        (sideGapCoefficientX z i t *
          sideGapRotationSignCurve (solutionPositionCurve z)
            (solutionVelocityCurve z) i t) t := by
    intro t ht
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := t) ha (hsegment ht) hrest hcenter
      (ne_of_gt (harea t ht))
    exact hsys.1
  have hderivY : ∀ t ∈ Set.Icc a T,
      HasDerivAt
        (sideGapRotationSignCurve (solutionPositionCurve z)
          (solutionVelocityCurve z) i)
        (sideGapCoefficientY z i t * sideGapRatioCurve (solutionPositionCurve z) i t) t := by
    intro t ht
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := t) ha (hsegment ht) hrest hcenter
      (ne_of_gt (harea t ht))
    exact hsys.2
  have hcoeffX : ∀ t ∈ Set.Icc a T, 0 ≤ sideGapCoefficientX z i t := by
    intro t ht
    have hpos := classicalNewton_sideGap_coefficients_pos i hsol (hsegment ht)
      (ne_of_gt (harea t ht))
    exact le_of_lt (by simpa [sideGapCoefficientX] using hpos.1)
  have hcoeffY : ∀ t ∈ Set.Icc a T, 0 < sideGapCoefficientY z i t := by
    intro t ht
    have hpos := classicalNewton_sideGap_coefficients_pos i hsol (hsegment ht)
      (ne_of_gt (harea t ht))
    simpa [sideGapCoefficientY] using hpos.2
  have hsigns := cooperative_pair_signs haT.le hXcont hYcont hX₀ hY₀
    hderivX hderivY hcoeffX hcoeffY
  intro t ht
  have hXpos := hsigns.1 t ht
  have hareaPos := harea t ht
  have hratio : sideGapRatioCurve (solutionPositionCurve z) i t =
      sideGap (z t).1 i / signedDoubleArea (z t).1 := by
    simpa [solutionPositionCurve] using
      sideGapRatioCurve_eq_sideGap_div_signedDoubleArea
        (solutionPositionCurve z) i t
  have hgapEq : sideGap (z t).1 i =
      signedDoubleArea (z t).1 * sideGapRatioCurve (solutionPositionCurve z) i t := by
    rw [hratio]
    field_simp [ne_of_gt hareaPos]
  rw [hgapEq]
  exact mul_pos hareaPos hXpos

/-- On a compact, positive-area segment of a centered initially resting
    classical solution, an initially strict squared-side ordering remains
    strict. Continuity of both cooperative variables is derived from the
    solution's differentiability. -/
theorem classicalNewton_sideGap_positive_on_Icc
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 < sideGap (z a).1 i)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∀ t ∈ Set.Icc a T, 0 < sideGap (z t).1 i := by
  have hcontinuous := classicalNewton_sideGap_variables_continuousOn
    hsol hsegment i harea
  exact classicalNewton_sideGap_positive_on_Icc_of_continuous i hsol hconn
    haT hsegment hrest hcenter hgap₀ harea hcontinuous.1 hcontinuous.2

/-- Before a regular endpoint, the negative pair rotation has strictly
    increasing values whenever the chosen physical side gap starts positive.
    This is a compact-interval statement and does not divide at the endpoint. -/
theorem classicalNewton_sideGapRotationSign_strictMono_on_Icc
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t : ℝ} (hat : a < t)
    (hsegment : Set.Icc a t ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 < sideGap (z a).1 i)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1) :
    StrictMonoOn
      (sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i) (Set.Icc a t) := by
  let X := sideGapRatioCurve (solutionPositionCurve z) i
  let Y := sideGapRotationSignCurve (solutionPositionCurve z)
    (solutionVelocityCurve z) i
  have ha : a ∈ I := hsegment ⟨le_rfl, hat.le⟩
  have hgapPos := classicalNewton_sideGap_positive_on_Icc i hsol hconn
    hat hsegment hrest hcenter hgap₀ harea
  have hderivY : ∀ s ∈ Set.Icc a t,
      HasDerivAt Y (sideGapCoefficientY z i s * X s) s := by
    intro s hs
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := s) ha (hsegment hs) hrest hcenter
      (ne_of_gt (harea s hs))
    exact hsys.2
  have hXpos : ∀ s ∈ Set.Icc a t, 0 < X s := by
    intro s hs
    change 0 < sideGapRatioCurve (solutionPositionCurve z) i s
    rw [sideGapRatioCurve_eq_sideGap_div_signedDoubleArea]
    exact div_pos (hgapPos s hs) (harea s hs)
  have hbpos : ∀ s ∈ Set.Icc a t, 0 < sideGapCoefficientY z i s := by
    intro s hs
    exact (classicalNewton_sideGap_coefficients_pos i hsol (hsegment hs)
      (ne_of_gt (harea s hs))).2
  exact cooperative_second_strictMono hderivY hXpos hbpos

/-- If a chosen side gap starts positive and the trajectory remains in the
    positive-area component until a regular collinear endpoint, its physical
    negative pair rotation is still strictly positive at the endpoint. -/
theorem classicalNewton_sideGapRotationSign_pos_at_regular_syzygy
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 < sideGap (z a).1 i)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (_hsyzygy : signedDoubleArea (z T).1 = 0) :
    0 < sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i T := by
  let Y := sideGapRotationSignCurve (solutionPositionCurve z)
    (solutionVelocityCurve z) i
  have hphase : ContinuousOn z (Set.Icc a T) :=
    classicalNewton_continuousOn_phase hsol hsegment
  have hYcont : ContinuousOn Y (Set.Icc a T) := by
    have hpos : ContinuousOn (fun t => (z t).1) (Set.Icc a T) := hphase.fst
    have hvel : ContinuousOn (fun t => (z t).2) (Set.Icc a T) := hphase.snd
    have hq (b : Fin 3) : ContinuousOn (fun t => (z t).1 b) (Set.Icc a T) := by
      have happly := (continuousOn_apply b Set.univ).comp hpos
        (by intro t ht; trivial)
      convert happly using 1
      ext t
      rfl
    have hv (b : Fin 3) : ContinuousOn (fun t => (z t).2 b) (Set.Icc a T) := by
      have happly := (continuousOn_apply b Set.univ).comp hvel
        (by intro t ht; trivial)
      convert happly using 1
      ext t
      rfl
    change ContinuousOn
      (fun t => sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t) (Set.Icc a T)
    fin_cases i <;>
      simp [sideGapRotationSignCurve, sidePairRotationCurve, sideVectorCurve,
        solutionPositionCurve, solutionVelocityCurve, sideVector, cross] <;>
      fun_prop
  let s := (a + T) / 2
  have has : a < s := by dsimp [s]; linarith
  have hsT : s < T := by dsimp [s]; linarith
  have hareaToS : ∀ t ∈ Set.Icc a s, 0 < signedDoubleArea (z t).1 := by
    intro t ht
    exact hareaPre t ⟨ht.1, lt_of_le_of_lt ht.2 hsT⟩
  have hsegToS : Set.Icc a s ⊆ I := by
    intro t ht
    exact hsegment ⟨ht.1, le_trans ht.2 hsT.le⟩
  have hmonoS := classicalNewton_sideGapRotationSign_strictMono_on_Icc
    i hsol hconn has hsegToS hrest hcenter hgap₀ hareaToS
  have hY0 : Y a = 0 := by
    simp [Y, sideGapRotationSign_eq_zero_of_rest i a hrest]
  have hYs : Y s > 0 := by
    have hlt := hmonoS ⟨le_rfl, has.le⟩ ⟨has.le, le_rfl⟩ has
    change Y a < Y s at hlt
    rw [hY0] at hlt
    exact hlt
  have hshiftNonneg : ∀ t ∈ Set.Ico s T, 0 ≤ Y t - Y s := by
    intro t ht
    by_cases hts : t = s
    · simp [hts]
    · have hst : s < t := lt_of_le_of_ne ht.1 (Ne.symm hts)
      have hareaTot : ∀ r ∈ Set.Icc a t, 0 < signedDoubleArea (z r).1 := by
        intro r hr
        exact hareaPre r ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
      have hsegTot : Set.Icc a t ⊆ I := by
        intro r hr
        exact hsegment ⟨hr.1, le_trans hr.2 ht.2.le⟩
      have hmonoT := classicalNewton_sideGapRotationSign_strictMono_on_Icc
        i hsol hconn (lt_trans has hst) hsegTot hrest hcenter hgap₀ hareaTot
      have hlt := hmonoT ⟨le_of_lt has, le_of_lt hst⟩
        ⟨le_trans has.le (le_of_lt hst), le_rfl⟩ hst
      change Y s < Y t at hlt
      linarith
  have hYcontST : ContinuousOn Y (Set.Icc s T) := hYcont.mono (by
    intro x hx
    exact ⟨le_trans has.le hx.1, hx.2⟩)
  have hshiftCont : ContinuousOn (fun x => Y x - Y s) (Set.Icc s T) := by
    exact hYcontST.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => Y s)
      (Set.Icc s T))
  have hshiftT := continuousOn_nonneg_right_of_nonneg_Ico hsT hshiftCont
    hshiftNonneg
  have hYT : Y T - Y s ≥ 0 := hshiftT
  change 0 < Y T
  linarith

/-- A strictly ordered pair of adjacent sides cannot become tied at a
    collision-free regular syzygy. The proof uses the unnormalized gap
    identity at the endpoint, where the area itself is zero. -/
theorem classicalNewton_sideGap_pos_at_regular_syzygy_of_pos_and_nonneg
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 < sideGap (z a).1 i)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hgapWeak : 0 ≤ sideGap (z T).1 i)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    0 < sideGap (z T).1 i := by
  have hrotPos := classicalNewton_sideGapRotationSign_pos_at_regular_syzygy
    i hsol hconn haT hsegment hrest hcenter hgap₀ hareaPre hsyzygy
  have hT : T ∈ I := hsegment ⟨le_of_lt haT, le_rfl⟩
  have hcf : CollisionFree (z T).1 := (hsol.2 T hT).1
  have hside : sideVector (z T).1 i ≠ 0 := by
    fin_cases i
    · intro hz
      have heq : (z T).1 2 = (z T).1 1 := sub_eq_zero.mp (by simpa [sideVector] using hz)
      exact hcf 2 1 (by decide) heq
    · intro hz
      have heq : (z T).1 0 = (z T).1 2 := sub_eq_zero.mp (by simpa [sideVector] using hz)
      exact hcf 0 2 (by decide) heq
    · intro hz
      have heq : (z T).1 1 = (z T).1 0 := sub_eq_zero.mp (by simpa [sideVector] using hz)
      exact hcf 1 0 (by decide) heq
  have hIm : 0 < frameMoment (sideVector (z T).1 i) (sideOffset (z T).1 i) := by
    have hr : 0 < ‖sideVector (z T).1 i‖ := norm_pos_iff.mpr hside
    unfold frameMoment
    positivity
  have hIdentity := classicalNewton_bodyCurve_gap_derivative_identity
    i hsol hconn (t₀ := a) (t := T)
    (hsegment ⟨le_rfl, haT.le⟩) hT hrest hcenter
  have hB : frameAreaCurve
      (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
      (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ) T =
        signedDoubleArea (z T).1 := by
    simp [frameAreaCurve, sideVectorCurve, sideOffsetCurve,
      solutionPositionCurve, signedDoubleArea_eq_cross_sideFrame]
  have hF : frameGapCurve
      (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
      (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ) T =
        sideGap (z T).1 i := by
    simp [frameGapCurve, sideVectorCurve, sideOffsetCurve,
      solutionPositionCurve, sideGap_eq_neg_two_dot_sideFrame]
  have hR : framePairRotation (sideVector (z T).1 i)
      (sideVector (z T).2 i) =
      -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i T := by
    simp [framePairRotation, sideGapRotationSignCurve, sidePairRotationCurve,
      sideVectorCurve, solutionPositionCurve, solutionVelocityCurve]
  by_contra hnot
  have hgapZero : sideGap (z T).1 i = 0 := le_antisymm
    (le_of_not_gt hnot) hgapWeak
  rw [hB, hF, hsyzygy, hgapZero] at hIdentity
  rw [hR] at hIdentity
  have hprod : frameMoment (sideVector (z T).1 i)
      (sideOffset (z T).1 i) *
      sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i T = 0 := by
    nlinarith [hIdentity]
  exact (mul_ne_zero (ne_of_gt hIm) (ne_of_gt hrotPos)) hprod

/-- An initially negative side gap remains strictly negative on a compact
    positive-area interval. Apply the cooperative sign theorem to `(-X,-Y)`. -/
theorem classicalNewton_sideGap_negative_on_Icc
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i < 0)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∀ t ∈ Set.Icc a T, sideGap (z t).1 i < 0 := by
  let X := sideGapRatioCurve (solutionPositionCurve z) i
  let Y := sideGapRotationSignCurve (solutionPositionCurve z)
    (solutionVelocityCurve z) i
  have ha : a ∈ I := hsegment ⟨le_rfl, haT.le⟩
  have hcontinuous := classicalNewton_sideGap_variables_continuousOn
    hsol hsegment i harea
  have hX₀ : 0 < -X a := by
    change 0 < -sideGapRatioCurve (solutionPositionCurve z) i a
    rw [sideGapRatioCurve_eq_sideGap_div_signedDoubleArea]
    exact neg_pos.mpr (div_neg_of_neg_of_pos hgap₀
      (harea a ⟨le_rfl, haT.le⟩))
  have hY₀ : -Y a = 0 := by
    simp [Y, sideGapRotationSign_eq_zero_of_rest i a hrest]
  have hderivX : ∀ t ∈ Set.Icc a T,
      HasDerivAt (fun s => -X s) (sideGapCoefficientX z i t * (-Y t)) t := by
    intro t ht
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := t) ha (hsegment ht) hrest hcenter
      (ne_of_gt (harea t ht))
    have hval :
        -(3 * frameMoment (sideVector (z t).1 i) (sideOffset (z t).1 i) /
          (signedDoubleArea (z t).1) ^ 2 *
          sideGapRotationSignCurve (solutionPositionCurve z)
            (solutionVelocityCurve z) i t) = sideGapCoefficientX z i t * (-Y t) := by
      dsimp [sideGapCoefficientX, Y]
      ring
    have hneg := hsys.1.neg.congr_deriv hval
    convert hneg using 1 <;> rfl
  have hderivY : ∀ t ∈ Set.Icc a T,
      HasDerivAt (fun s => -Y s) (sideGapCoefficientY z i t * (-X t)) t := by
    intro t ht
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := t) ha (hsegment ht) hrest hcenter
      (ne_of_gt (harea t ht))
    have hval :
        -((signedDoubleArea (z t).1) ^ 2 *
          inverseCubeGapFactor
            (dist ((z t).1 (cyclicPrev i)) ((z t).1 i))
            (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) *
          sideGapRatioCurve (solutionPositionCurve z) i t) =
          sideGapCoefficientY z i t * (-X t) := by
      dsimp [sideGapCoefficientY, X]
      ring
    have hneg := hsys.2.neg.congr_deriv hval
    convert hneg using 1 <;> rfl
  have hcoeffX : ∀ t ∈ Set.Icc a T, 0 ≤ sideGapCoefficientX z i t := by
    intro t ht
    have hpos := classicalNewton_sideGap_coefficients_pos i hsol (hsegment ht)
      (ne_of_gt (harea t ht))
    exact le_of_lt (by simpa [sideGapCoefficientX] using hpos.1)
  have hcoeffY : ∀ t ∈ Set.Icc a T, 0 < sideGapCoefficientY z i t := by
    intro t ht
    have hpos := classicalNewton_sideGap_coefficients_pos i hsol (hsegment ht)
      (ne_of_gt (harea t ht))
    simpa [sideGapCoefficientY] using hpos.2
  have hsigns := cooperative_pair_signs haT.le
    (by simpa only [X, Function.comp_def] using continuous_neg.comp_continuousOn hcontinuous.1)
    (by simpa only [Y, Function.comp_def] using continuous_neg.comp_continuousOn hcontinuous.2)
    hX₀ hY₀ hderivX hderivY hcoeffX hcoeffY
  intro t ht
  have hXneg : X t < 0 := by linarith [hsigns.1 t ht]
  have hareaPos := harea t ht
  have hratio : X t = sideGap (z t).1 i / signedDoubleArea (z t).1 := by
    simpa [X, solutionPositionCurve] using
      sideGapRatioCurve_eq_sideGap_div_signedDoubleArea
        (solutionPositionCurve z) i t
  have hgapEq : sideGap (z t).1 i =
      signedDoubleArea (z t).1 * X t := by
    rw [hratio]
    field_simp [ne_of_gt hareaPos]
  rw [hgapEq]
  exact mul_neg_of_pos_of_neg hareaPos hXneg

/-- A pair of initially tied squared sides remains tied on a compact
    positive-area segment. This is the isosceles case of the side-gap system;
    uniqueness follows from Grönwall after bounding its continuous
    coefficients on the compact interval. -/
theorem classicalNewton_sideGap_eq_zero_on_Icc_of_tie
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i = 0)
    (harea : ∀ t ∈ Set.Icc a T, 0 < signedDoubleArea (z t).1) :
    ∀ t ∈ Set.Icc a T, sideGap (z t).1 i = 0 := by
  have ha : a ∈ I := hsegment ⟨le_rfl, haT.le⟩
  have hcontinuous := classicalNewton_sideGap_variables_continuousOn
    hsol hsegment i harea
  have hX₀ : sideGapRatioCurve (solutionPositionCurve z) i a = 0 := by
    rw [sideGapRatioCurve_eq_sideGap_div_signedDoubleArea]
    apply (div_eq_zero_iff).2
    left
    simpa [solutionPositionCurve] using hgap₀
  have hY₀ : sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i a = 0 :=
    sideGapRotationSign_eq_zero_of_rest i a hrest
  have hderivX : ∀ t ∈ Set.Ico a T,
      HasDerivAt (sideGapRatioCurve (solutionPositionCurve z) i)
        (sideGapCoefficientX z i t * sideGapRotationSignCurve
          (solutionPositionCurve z) (solutionVelocityCurve z) i t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc a T := ⟨ht.1, ht.2.le⟩
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := t) ha (hsegment htIcc) hrest hcenter
      (ne_of_gt (harea t htIcc))
    exact hsys.1
  have hderivY : ∀ t ∈ Set.Ico a T,
      HasDerivAt (sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i)
        (sideGapCoefficientY z i t * sideGapRatioCurve
          (solutionPositionCurve z) i t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc a T := ⟨ht.1, ht.2.le⟩
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := t) ha (hsegment htIcc) hrest hcenter
      (ne_of_gt (harea t htIcc))
    exact hsys.2
  obtain ⟨K, hK, hcoeffBound⟩ := classicalNewton_sideGap_coefficients_boundedOn_Icc
    hsol hsegment i haT.le harea
  have hzero := cooperative_pair_eq_zero_of_zero_initial
    hcontinuous.1 hcontinuous.2 hderivX hderivY hX₀ hY₀ hK
    (by
      intro t ht
      have htIcc : t ∈ Set.Icc a T := ⟨ht.1, ht.2.le⟩
      exact hcoeffBound t htIcc)
  intro t ht
  have hXt := (hzero t ht).1
  have hratio := sideGapRatioCurve_eq_sideGap_div_signedDoubleArea
    (solutionPositionCurve z) i t
  rw [hratio] at hXt
  rcases (div_eq_zero_iff).mp hXt with hgap | hareaZero
  · simpa [solutionPositionCurve] using hgap
  · exact False.elim ((ne_of_gt (harea t ht)) (by simpa [solutionPositionCurve] using hareaZero))

/-- The physical squared-side gap is continuous on every compact segment of a
    classical Newton trajectory, including a regular collinear endpoint. -/
theorem classicalNewton_sideGap_continuousOn
    {z : ℝ → Phase} {I : Set ℝ} (hsol : ClassicalNewtonSolution z I)
    {a T : ℝ} (hsegment : Set.Icc a T ⊆ I) (i : Fin 3) :
    ContinuousOn (fun t => sideGap (z t).1 i) (Set.Icc a T) := by
  let J := Set.Icc a T
  have hphase : ContinuousOn z J := classicalNewton_continuousOn_phase hsol hsegment
  have hposition : ContinuousOn (fun t => (z t).1) J := hphase.fst
  have hq (b : Fin 3) : ContinuousOn (fun t => (z t).1 b) J := by
    have happly := (continuousOn_apply b Set.univ).comp hposition
      (by intro t ht; trivial)
    convert happly using 1
    ext t
    rfl
  have hgap : ContinuousOn (fun t => sideGap (z t).1 i) J := by
    fin_cases i <;> simp only [sideGap] <;> fun_prop
  simpa [J] using hgap

/-- An initially positive side gap stays weakly positive at a regular
    collinear endpoint, assuming positive area before that endpoint. -/
theorem classicalNewton_sideGap_nonneg_at_regular_syzygy_of_pos
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 < sideGap (z a).1 i)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (_hsyzygy : signedDoubleArea (z T).1 = 0) :
    0 ≤ sideGap (z T).1 i := by
  have hgapIco : ∀ t ∈ Set.Ico a T, 0 < sideGap (z t).1 i := by
    intro t ht
    by_cases hta : t = a
    · simpa [hta] using hgap₀
    · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      have hsubsegment : Set.Icc a t ⊆ I := by
        intro s hs
        apply hsegment
        exact ⟨hs.1, le_trans hs.2 ht.2.le⟩
      have hsubarea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1 := by
        intro s hs
        exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      exact (classicalNewton_sideGap_positive_on_Icc i hsol hconn hat
        hsubsegment hrest hcenter hgap₀ hsubarea) t ⟨ht.1, le_rfl⟩
  exact continuousOn_nonneg_right_of_nonneg_Ico haT
    (classicalNewton_sideGap_continuousOn hsol hsegment i)
    (fun t ht => le_of_lt (hgapIco t ht))

/-- An initially negative side gap stays weakly nonpositive at a regular
    collinear endpoint, assuming positive area before that endpoint. -/
theorem classicalNewton_sideGap_nonpos_at_regular_syzygy_of_neg
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i < 0)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (_hsyzygy : signedDoubleArea (z T).1 = 0) :
    sideGap (z T).1 i ≤ 0 := by
  have hgapIco : ∀ t ∈ Set.Ico a T, sideGap (z t).1 i < 0 := by
    intro t ht
    by_cases hta : t = a
    · simpa [hta] using hgap₀
    · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      have hsubsegment : Set.Icc a t ⊆ I := by
        intro s hs
        apply hsegment
        exact ⟨hs.1, le_trans hs.2 ht.2.le⟩
      have hsubarea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1 := by
        intro s hs
        exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      exact (classicalNewton_sideGap_negative_on_Icc i hsol hconn hat
        hsubsegment hrest hcenter hgap₀ hsubarea) t ⟨ht.1, le_rfl⟩
  exact continuousOn_nonpos_right_of_nonpos_Ico haT
    (classicalNewton_sideGap_continuousOn hsol hsegment i)
    (fun t ht => le_of_lt (hgapIco t ht))

/-- The sign-reversed pair rotation is strictly increasing when the chosen
    physical side gap starts negative. -/
theorem classicalNewton_negSideGapRotationSign_strictMono_on_Icc
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t : ℝ} (hat : a < t)
    (hsegment : Set.Icc a t ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i < 0)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1) :
    StrictMonoOn
      (fun s => -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i s) (Set.Icc a t) := by
  let X := fun s => -sideGapRatioCurve (solutionPositionCurve z) i s
  let Y := fun s => -sideGapRotationSignCurve (solutionPositionCurve z)
    (solutionVelocityCurve z) i s
  have ha : a ∈ I := hsegment ⟨le_rfl, hat.le⟩
  have hgapNeg := classicalNewton_sideGap_negative_on_Icc i hsol hconn
    hat hsegment hrest hcenter hgap₀ harea
  have hderivY : ∀ s ∈ Set.Icc a t,
      HasDerivAt Y (sideGapCoefficientY z i s * X s) s := by
    intro s hs
    have hsys := classicalNewton_sideGap_cooperative_derivatives i hsol hconn
      (t₀ := a) (t := s) ha (hsegment hs) hrest hcenter
      (ne_of_gt (harea s hs))
    have hval : -(signedDoubleArea (z s).1 ^ 2 *
        inverseCubeGapFactor
          (dist ((z s).1 (cyclicPrev i)) ((z s).1 i))
          (dist ((z s).1 (cyclicNext i)) ((z s).1 i)) *
        sideGapRatioCurve (solutionPositionCurve z) i s) =
        sideGapCoefficientY z i s * X s := by
      dsimp [sideGapCoefficientY, X]
      ring
    exact hsys.2.neg.congr_deriv hval
  have hXpos : ∀ s ∈ Set.Icc a t, 0 < X s := by
    intro s hs
    change 0 < -sideGapRatioCurve (solutionPositionCurve z) i s
    rw [sideGapRatioCurve_eq_sideGap_div_signedDoubleArea]
    exact neg_pos.mpr (div_neg_of_neg_of_pos (hgapNeg s hs) (harea s hs))
  have hbpos : ∀ s ∈ Set.Icc a t, 0 < sideGapCoefficientY z i s := by
    intro s hs
    exact (classicalNewton_sideGap_coefficients_pos i hsol (hsegment hs)
      (ne_of_gt (harea s hs))).2
  exact cooperative_second_strictMono hderivY hXpos hbpos

/-- A nonzero initial side gap makes the appropriately oriented physical pair
    rotation strictly positive at every later time while the area stays
    positive. -/
theorem classicalNewton_orientedRotation_pos_of_nonzero_sideGap
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a t : ℝ} (hat : a < t)
    (hsegment : Set.Icc a t ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap : sideGap (z a).1 i ≠ 0)
    (harea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1) :
    if 0 < sideGap (z a).1 i then
      0 < sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t
    else
      0 < -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t := by
  by_cases hpos : 0 < sideGap (z a).1 i
  · simp only [if_pos hpos]
    have hmono := classicalNewton_sideGapRotationSign_strictMono_on_Icc
      i hsol hconn hat hsegment hrest hcenter hpos harea
    have hzero : sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i a = 0 :=
      sideGapRotationSign_eq_zero_of_rest i a hrest
    have hlt := hmono ⟨le_rfl, hat.le⟩ ⟨hat.le, le_rfl⟩ hat
    change sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i a <
      sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t at hlt
    rw [hzero] at hlt
    exact hlt
  · have hneg : sideGap (z a).1 i < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hgap
    simp only [if_neg hpos]
    have hmono := classicalNewton_negSideGapRotationSign_strictMono_on_Icc
      i hsol hconn hat hsegment hrest hcenter hneg harea
    have hzero : -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i a = 0 := by
      simp [sideGapRotationSign_eq_zero_of_rest i a hrest]
    have hlt := hmono ⟨le_rfl, hat.le⟩ ⟨hat.le, le_rfl⟩ hat
    change -sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i a <
      -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t at hlt
    rw [hzero] at hlt
    exact hlt

/-- Once oriented by the initial gap sign, the physical pair rotation is
    nondecreasing on a compact positive-area interval. -/
theorem classicalNewton_orientedRotation_nondecreasing_on_Icc
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap : sideGap (z a).1 i ≠ 0)
    (harea : ∀ s ∈ Set.Icc a T, 0 < signedDoubleArea (z s).1)
    {s t : ℝ} (hs : s ∈ Set.Icc a T) (ht : t ∈ Set.Icc a T)
    (hst : s ≤ t) :
    (if 0 < sideGap (z a).1 i then
      sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i s
     else -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i s) ≤
    (if 0 < sideGap (z a).1 i then
      sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t
     else -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i t) := by
  by_cases hpos : 0 < sideGap (z a).1 i
  · simp only [if_pos hpos]
    have hmono := classicalNewton_sideGapRotationSign_strictMono_on_Icc
      i hsol hconn haT hsegment hrest hcenter hpos harea
    by_cases hstEq : s = t
    · simp [hstEq]
    · exact le_of_lt (hmono hs ht (lt_of_le_of_ne hst hstEq))
  · have hneg : sideGap (z a).1 i < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hgap
    simp only [if_neg hpos]
    have hmono := classicalNewton_negSideGapRotationSign_strictMono_on_Icc
      i hsol hconn haT hsegment hrest hcenter hneg harea
    by_cases hstEq : s = t
    · simp [hstEq]
    · exact le_of_lt (hmono hs ht (lt_of_le_of_ne hst hstEq))

/-- For a negative initial gap, the sign-reversed physical rotation remains
    strictly positive at an assumed regular syzygy endpoint. -/
theorem classicalNewton_negSideGapRotationSign_pos_at_regular_syzygy
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i < 0)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (_hsyzygy : signedDoubleArea (z T).1 = 0) :
    0 < -sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i T := by
  let Y := fun t => -sideGapRotationSignCurve (solutionPositionCurve z)
    (solutionVelocityCurve z) i t
  have hphase : ContinuousOn z (Set.Icc a T) :=
    classicalNewton_continuousOn_phase hsol hsegment
  have hYcont : ContinuousOn Y (Set.Icc a T) := by
    have hpos : ContinuousOn (fun t => (z t).1) (Set.Icc a T) := hphase.fst
    have hvel : ContinuousOn (fun t => (z t).2) (Set.Icc a T) := hphase.snd
    have hq (b : Fin 3) : ContinuousOn (fun t => (z t).1 b) (Set.Icc a T) := by
      have happly := (continuousOn_apply b Set.univ).comp hpos
        (by intro t ht; trivial)
      convert happly using 1
      ext t
      rfl
    have hv (b : Fin 3) : ContinuousOn (fun t => (z t).2 b) (Set.Icc a T) := by
      have happly := (continuousOn_apply b Set.univ).comp hvel
        (by intro t ht; trivial)
      convert happly using 1
      ext t
      rfl
    change ContinuousOn (fun t => -sideGapRotationSignCurve
      (solutionPositionCurve z) (solutionVelocityCurve z) i t) (Set.Icc a T)
    fin_cases i <;>
      simp [sideGapRotationSignCurve, sidePairRotationCurve, sideVectorCurve,
        solutionPositionCurve, solutionVelocityCurve, sideVector, cross] <;>
      fun_prop
  let s := (a + T) / 2
  have has : a < s := by dsimp [s]; linarith
  have hsT : s < T := by dsimp [s]; linarith
  have hareaToS : ∀ t ∈ Set.Icc a s, 0 < signedDoubleArea (z t).1 := by
    intro t ht
    exact hareaPre t ⟨ht.1, lt_of_le_of_lt ht.2 hsT⟩
  have hsegToS : Set.Icc a s ⊆ I := by
    intro t ht
    exact hsegment ⟨ht.1, le_trans ht.2 hsT.le⟩
  have hmonoS := classicalNewton_negSideGapRotationSign_strictMono_on_Icc
    i hsol hconn has hsegToS hrest hcenter hgap₀ hareaToS
  have hY0 : Y a = 0 := by
    simp [Y, sideGapRotationSign_eq_zero_of_rest i a hrest]
  have hYs : 0 < Y s := by
    have hlt := hmonoS ⟨le_rfl, has.le⟩ ⟨has.le, le_rfl⟩ has
    change Y a < Y s at hlt
    rw [hY0] at hlt
    exact hlt
  have hshiftNonneg : ∀ t ∈ Set.Ico s T, 0 ≤ Y t - Y s := by
    intro t ht
    by_cases hts : t = s
    · simp [hts]
    · have hst : s < t := lt_of_le_of_ne ht.1 (Ne.symm hts)
      have hareaTot : ∀ r ∈ Set.Icc a t, 0 < signedDoubleArea (z r).1 := by
        intro r hr
        exact hareaPre r ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
      have hsegTot : Set.Icc a t ⊆ I := by
        intro r hr
        exact hsegment ⟨hr.1, le_trans hr.2 ht.2.le⟩
      have hmonoT := classicalNewton_negSideGapRotationSign_strictMono_on_Icc
        i hsol hconn (lt_trans has hst) hsegTot hrest hcenter hgap₀ hareaTot
      have hlt := hmonoT ⟨le_of_lt has, le_of_lt hst⟩
        ⟨le_trans has.le (le_of_lt hst), le_rfl⟩ hst
      change Y s < Y t at hlt
      linarith
  have hYcontST : ContinuousOn Y (Set.Icc s T) := hYcont.mono (by
    intro t ht
    exact ⟨le_trans has.le ht.1, ht.2⟩)
  have hshiftCont : ContinuousOn (fun t => Y t - Y s) (Set.Icc s T) :=
    hYcontST.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => Y s)
      (Set.Icc s T))
  have hshiftT := continuousOn_nonneg_right_of_nonneg_Ico hsT hshiftCont
    hshiftNonneg
  change 0 < Y T
  linarith

/- A negative initial side gap cannot become tied at a collision-free
   regular endpoint. -/
theorem classicalNewton_sideGap_neg_at_regular_syzygy_of_neg_and_nonpos
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i < 0)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hgapWeak : sideGap (z T).1 i ≤ 0)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    sideGap (z T).1 i < 0 := by
  have hrotPos := classicalNewton_negSideGapRotationSign_pos_at_regular_syzygy
    i hsol hconn haT hsegment hrest hcenter hgap₀ hareaPre hsyzygy
  have hT : T ∈ I := hsegment ⟨le_of_lt haT, le_rfl⟩
  have hcf : CollisionFree (z T).1 := (hsol.2 T hT).1
  have hside : sideVector (z T).1 i ≠ 0 := by
    fin_cases i
    · intro hz
      have heq : (z T).1 2 = (z T).1 1 := sub_eq_zero.mp (by simpa [sideVector] using hz)
      exact hcf 2 1 (by decide) heq
    · intro hz
      have heq : (z T).1 0 = (z T).1 2 := sub_eq_zero.mp (by simpa [sideVector] using hz)
      exact hcf 0 2 (by decide) heq
    · intro hz
      have heq : (z T).1 1 = (z T).1 0 := sub_eq_zero.mp (by simpa [sideVector] using hz)
      exact hcf 1 0 (by decide) heq
  have hIm : 0 < frameMoment (sideVector (z T).1 i) (sideOffset (z T).1 i) := by
    have hr : 0 < ‖sideVector (z T).1 i‖ := norm_pos_iff.mpr hside
    unfold frameMoment
    positivity
  have hIdentity := classicalNewton_bodyCurve_gap_derivative_identity
    i hsol hconn (t₀ := a) (t := T)
    (hsegment ⟨le_rfl, haT.le⟩) hT hrest hcenter
  have hB : frameAreaCurve
      (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
      (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ) T =
        signedDoubleArea (z T).1 := by
    simp [frameAreaCurve, sideVectorCurve, sideOffsetCurve,
      solutionPositionCurve, signedDoubleArea_eq_cross_sideFrame]
  have hF : frameGapCurve
      (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
      (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ) T =
        sideGap (z T).1 i := by
    simp [frameGapCurve, sideVectorCurve, sideOffsetCurve,
      solutionPositionCurve, sideGap_eq_neg_two_dot_sideFrame]
  have hR : framePairRotation (sideVector (z T).1 i)
      (sideVector (z T).2 i) =
      -sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i T := by
    simp [framePairRotation, sideGapRotationSignCurve, sidePairRotationCurve,
      sideVectorCurve, solutionPositionCurve, solutionVelocityCurve]
  by_contra hnot
  have hgapZero : sideGap (z T).1 i = 0 := le_antisymm
    hgapWeak (not_lt.mp hnot)
  rw [hB, hF, hsyzygy, hgapZero] at hIdentity
  rw [hR] at hIdentity
  have hprod : frameMoment (sideVector (z T).1 i)
      (sideOffset (z T).1 i) *
      (-sideGapRotationSignCurve (solutionPositionCurve z)
        (solutionVelocityCurve z) i T) = 0 := by
    nlinarith [hIdentity]
  have hrotation : 0 < -sideGapRotationSignCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) i T := by
    simpa using hrotPos
  exact (mul_ne_zero (ne_of_gt hIm) (ne_of_gt hrotation)) hprod

theorem classicalNewton_sideGap_neg_at_regular_syzygy_of_neg
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i < 0)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    sideGap (z T).1 i < 0 := by
  have hweak := classicalNewton_sideGap_nonpos_at_regular_syzygy_of_neg
    i hsol hconn haT hsegment hrest hcenter hgap₀ hareaPre hsyzygy
  exact classicalNewton_sideGap_neg_at_regular_syzygy_of_neg_and_nonpos
    i hsol hconn haT hsegment hrest hcenter hgap₀ hareaPre hweak hsyzygy

/-- An initially tied side pair stays tied at a regular first syzygy, provided
    the signed area remains positive before the endpoint. -/
theorem classicalNewton_sideGap_eq_zero_at_regular_syzygy_of_tie
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i = 0)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (_hareaT : signedDoubleArea (z T).1 = 0) :
    sideGap (z T).1 i = 0 := by
  have hgapIco : ∀ t ∈ Set.Ico a T, sideGap (z t).1 i = 0 := by
    intro t ht
    by_cases hta : t = a
    · simpa [hta] using hgap₀
    · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      have hsubsegment : Set.Icc a t ⊆ I := by
        intro s hs
        apply hsegment
        exact ⟨hs.1, le_trans hs.2 ht.2.le⟩
      have hsubarea : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1 := by
        intro s hs
        exact hareaPre s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      have htie := classicalNewton_sideGap_eq_zero_on_Icc_of_tie i hsol hconn
        hat hsubsegment hrest hcenter hgap₀ hsubarea
      exact htie t ⟨ht.1, le_rfl⟩
  exact continuousOn_eq_zero_right_of_eq_zero_Ico haT
    (classicalNewton_sideGap_continuousOn hsol hsegment i) hgapIco

/-- A weakly nonnegative initial side gap remains weakly nonnegative at a
    regular syzygy. The equality case uses the tied-gap endpoint theorem. -/
theorem classicalNewton_sideGap_nonneg_at_regular_syzygy
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 ≤ sideGap (z a).1 i)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    0 ≤ sideGap (z T).1 i := by
  by_cases hzero : sideGap (z a).1 i = 0
  · rw [classicalNewton_sideGap_eq_zero_at_regular_syzygy_of_tie
      i hsol hconn haT hsegment hrest hcenter hzero hareaPre hsyzygy]
  · have hpos : 0 < sideGap (z a).1 i := lt_of_le_of_ne hgap₀ (Ne.symm hzero)
    exact classicalNewton_sideGap_nonneg_at_regular_syzygy_of_pos
      i hsol hconn haT hsegment hrest hcenter hpos hareaPre hsyzygy

/-- A weakly nonpositive initial side gap remains weakly nonpositive at a
    regular syzygy. The equality case uses the tied-gap endpoint theorem. -/
theorem classicalNewton_sideGap_nonpos_at_regular_syzygy
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i ≤ 0)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    sideGap (z T).1 i ≤ 0 := by
  by_cases hzero : sideGap (z a).1 i = 0
  · rw [classicalNewton_sideGap_eq_zero_at_regular_syzygy_of_tie
      i hsol hconn haT hsegment hrest hcenter hzero hareaPre hsyzygy]
  · have hneg : sideGap (z a).1 i < 0 := lt_of_le_of_ne hgap₀ hzero
    exact classicalNewton_sideGap_nonpos_at_regular_syzygy_of_neg
      i hsol hconn haT hsegment hrest hcenter hneg hareaPre hsyzygy

/-- If the side opposite body `0` is initially at least as long as both
    adjacent sides, it remains weakly longest at any assumed regular
    syzygy. This is the first assembled endpoint-order criterion. -/
theorem classicalNewton_oppositeSide0_remains_weakly_longest
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlong01 : dist ((z a).1 1) ((z a).1 2) ^ 2 ≥
      dist ((z a).1 0) ((z a).1 1) ^ 2)
    (hlong02 : dist ((z a).1 1) ((z a).1 2) ^ 2 ≥
      dist ((z a).1 2) ((z a).1 0) ^ 2)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    dist ((z T).1 1) ((z T).1 2) ^ 2 ≥
      dist ((z T).1 0) ((z T).1 1) ^ 2 ∧
    dist ((z T).1 1) ((z T).1 2) ^ 2 ≥
      dist ((z T).1 2) ((z T).1 0) ^ 2 := by
  have hgap1 : sideGap (z a).1 1 ≤ 0 := by
    simpa [sideGap, dist_eq_norm] using hlong01
  have hgap2 : 0 ≤ sideGap (z a).1 2 := by
    simpa [sideGap, dist_eq_norm] using hlong02
  have hgap1T := classicalNewton_sideGap_nonpos_at_regular_syzygy
    1 hsol hconn haT hsegment hrest hcenter hgap1 hareaPre hsyzygy
  have hgap2T := classicalNewton_sideGap_nonneg_at_regular_syzygy
    2 hsol hconn haT hsegment hrest hcenter hgap2 hareaPre hsyzygy
  constructor
  · simpa [sideGap, dist_eq_norm] using hgap1T
  · simpa [sideGap, dist_eq_norm] using hgap2T

/-- Any initially weakly longest opposite side remains weakly longest at an
    assumed regular syzygy endpoint. -/
theorem classicalNewton_oppositeSide_remains_weakly_longest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : dist ((z a).1 (cyclicPrev i)) ((z a).1 (cyclicNext i)) ^ 2 ≥
      dist ((z a).1 i) ((z a).1 (cyclicPrev i)) ^ 2)
    (hlongNext : dist ((z a).1 (cyclicPrev i)) ((z a).1 (cyclicNext i)) ^ 2 ≥
      dist ((z a).1 (cyclicNext i)) ((z a).1 i) ^ 2)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    dist ((z T).1 (cyclicPrev i)) ((z T).1 (cyclicNext i)) ^ 2 ≥
        dist ((z T).1 i) ((z T).1 (cyclicPrev i)) ^ 2 ∧
      dist ((z T).1 (cyclicPrev i)) ((z T).1 (cyclicNext i)) ^ 2 ≥
        dist ((z T).1 (cyclicNext i)) ((z T).1 i) ^ 2 := by
  have hlongPrevSq : sideSq (z a).1 i ≥ sideSq (z a).1 (cyclicNext i) := by
    have hfirst : sideSq (z a).1 i =
        dist ((z a).1 (cyclicPrev i)) ((z a).1 (cyclicNext i)) ^ 2 :=
      sideSq_eq_cyclicNeighborDistance (z a).1 i
    have hsecond : sideSq (z a).1 (cyclicNext i) =
        dist ((z a).1 i) ((z a).1 (cyclicPrev i)) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance (z a).1 (cyclicNext i)]
      simp [cyclicPrev_cyclicNext, cyclicNext_cyclicNext]
    rw [hfirst, hsecond]
    exact hlongPrev
  have hlongNextSq : sideSq (z a).1 i ≥ sideSq (z a).1 (cyclicPrev i) := by
    have hfirst : sideSq (z a).1 i =
        dist ((z a).1 (cyclicPrev i)) ((z a).1 (cyclicNext i)) ^ 2 :=
      sideSq_eq_cyclicNeighborDistance (z a).1 i
    have hsecond : sideSq (z a).1 (cyclicPrev i) =
        dist ((z a).1 (cyclicNext i)) ((z a).1 i) ^ 2 := by
      rw [sideSq_eq_cyclicNeighborDistance (z a).1 (cyclicPrev i)]
      simp [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev]
    rw [hfirst, hsecond]
    exact hlongNext
  have hgapPrev : 0 ≤ sideGap (z a).1 (cyclicPrev i) := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    simpa [cyclicNext_cyclicPrev, cyclicPrev_cyclicPrev] using
      (sub_nonneg.mpr hlongPrevSq)
  have hgapNext : sideGap (z a).1 (cyclicNext i) ≤ 0 := by
    rw [sideGap_eq_next_sub_prev_sideSq]
    simpa [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] using
      (sub_nonpos.mpr hlongNextSq)
  have hprev := classicalNewton_sideGap_nonneg_at_regular_syzygy
    (cyclicPrev i) hsol hconn haT hsegment hrest hcenter hgapPrev hareaPre hsyzygy
  have hnext := classicalNewton_sideGap_nonpos_at_regular_syzygy
    (cyclicNext i) hsol hconn haT hsegment hrest hcenter hgapNext hareaPre hsyzygy
  have hprevSq : sideSq (z T).1 i ≥ sideSq (z T).1 (cyclicNext i) := by
    rw [sideGap_eq_next_sub_prev_sideSq] at hprev
    simpa [cyclicNext_cyclicPrev, cyclicPrev_cyclicPrev] using hprev
  have hnextSq : sideSq (z T).1 i ≥ sideSq (z T).1 (cyclicPrev i) := by
    rw [sideGap_eq_next_sub_prev_sideSq] at hnext
    simpa [cyclicNext_cyclicNext, cyclicPrev_cyclicNext] using hnext
  constructor
  · calc
      dist ((z T).1 (cyclicPrev i)) ((z T).1 (cyclicNext i)) ^ 2 =
          sideSq (z T).1 i := by
            exact (sideSq_eq_cyclicNeighborDistance (z T).1 i).symm
      _ ≥ sideSq (z T).1 (cyclicNext i) := hprevSq
      _ = dist ((z T).1 i) ((z T).1 (cyclicPrev i)) ^ 2 := by
            rw [sideSq_eq_cyclicNeighborDistance]
            simp [cyclicPrev_cyclicNext, cyclicNext_cyclicNext]
  · calc
      dist ((z T).1 (cyclicPrev i)) ((z T).1 (cyclicNext i)) ^ 2 =
          sideSq (z T).1 i := by
            exact (sideSq_eq_cyclicNeighborDistance (z T).1 i).symm
      _ ≥ sideSq (z T).1 (cyclicPrev i) := hnextSq
      _ = dist ((z T).1 (cyclicNext i)) ((z T).1 i) ^ 2 := by
            rw [sideSq_eq_cyclicNeighborDistance]
            simp [cyclicPrev_cyclicPrev, cyclicNext_cyclicPrev]

/-- The longest-side rule at an assumed regular first syzygy, stated with
    Mathlib's open-segment predicate for every body index. -/
theorem classicalNewton_body_between_sbtw_at_regular_syzygy_of_initial_longest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongPrev : dist ((z a).1 (cyclicPrev i)) ((z a).1 (cyclicNext i)) ^ 2 ≥
      dist ((z a).1 i) ((z a).1 (cyclicPrev i)) ^ 2)
    (hlongNext : dist ((z a).1 (cyclicPrev i)) ((z a).1 (cyclicNext i)) ^ 2 ≥
      dist ((z a).1 (cyclicNext i)) ((z a).1 i) ^ 2)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    Sbtw ℝ ((z T).1 (cyclicPrev i)) ((z T).1 i)
      ((z T).1 (cyclicNext i)) := by
  have hlongest := classicalNewton_oppositeSide_remains_weakly_longest
    i hsol hconn haT hsegment hrest hcenter hlongPrev hlongNext hareaPre hsyzygy
  have hcf : CollisionFree (z T).1 :=
    (hsol.2 T (hsegment ⟨le_of_lt haT, le_rfl⟩)).1
  exact sbtw_of_longest_opposite_side (z T).1 i hsyzygy hcf hlongest.1 hlongest.2

/-- Under the same hypotheses, a collision-free first collinear endpoint
    places body `0` between bodies `1` and `2`, expressed by the positive
    dot product of the two endpoint-directed vectors. -/
theorem classicalNewton_body0_between_dot_at_regular_syzygy_of_initial_longest
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlong01 : dist ((z a).1 1) ((z a).1 2) ^ 2 ≥
      dist ((z a).1 0) ((z a).1 1) ^ 2)
    (hlong02 : dist ((z a).1 1) ((z a).1 2) ^ 2 ≥
      dist ((z a).1 2) ((z a).1 0) ^ 2)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    0 < dot2 ((z T).1 0 - (z T).1 1) ((z T).1 2 - (z T).1 0) := by
  have hlongest := classicalNewton_oppositeSide0_remains_weakly_longest
    hsol hconn haT hsegment hrest hcenter hlong01 hlong02 hareaPre hsyzygy
  have hcollision : CollisionFree (z T).1 :=
    (hsol.2 T (hsegment ⟨le_of_lt haT, le_rfl⟩)).1
  exact syzygy_longest_opposite_side0_forces_positive_between_dot
    (z T).1 hsyzygy hcollision hlongest.1 hlongest.2

/-- A positive initial side gap stays strictly positive through an assumed
    regular endpoint of the positive-area component. -/
theorem classicalNewton_sideGap_pos_at_regular_syzygy_of_pos
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : 0 < sideGap (z a).1 i)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    0 < sideGap (z T).1 i := by
  have hweak := classicalNewton_sideGap_nonneg_at_regular_syzygy_of_pos
    i hsol hconn haT hsegment hrest hcenter hgap₀ hareaPre hsyzygy
  exact classicalNewton_sideGap_pos_at_regular_syzygy_of_pos_and_nonneg
    i hsol hconn haT hsegment hrest hcenter hgap₀ hareaPre hweak hsyzygy

/-- At a regular syzygy, an initially tied pair adjacent to body `i` places
    `i` exactly at the midpoint between the other two bodies. -/
theorem classicalNewton_tied_body_is_midpoint_at_regular_syzygy
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T)
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hgap₀ : sideGap (z a).1 i = 0)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hsyzygy : signedDoubleArea (z T).1 = 0) :
    (z T).1 i = (1 / 2 : ℝ) • oppositePairSum (z T).1 i := by
  have hgapT := classicalNewton_sideGap_eq_zero_at_regular_syzygy_of_tie
    i hsol hconn haT hsegment hrest hcenter hgap₀ hareaPre hsyzygy
  have hcollision : CollisionFree (z T).1 := (hsol.2 T (hsegment ⟨le_of_lt haT, le_rfl⟩)).1
  have hside : sideVector (z T).1 i ≠ 0 := by
    fin_cases i
    · intro hz
      have hEq : (z T).1 2 = (z T).1 1 := sub_eq_zero.mp (by
        simpa [sideVector] using hz)
      exact hcollision 2 1 (by decide) hEq
    · intro hz
      have hEq : (z T).1 0 = (z T).1 2 := sub_eq_zero.mp (by
        simpa [sideVector] using hz)
      exact hcollision 0 2 (by decide) hEq
    · intro hz
      have hEq : (z T).1 1 = (z T).1 0 := sub_eq_zero.mp (by
        simpa [sideVector] using hz)
      exact hcollision 1 0 (by decide) hEq
  exact syzygy_tied_gap_body_is_midpoint (z T).1 i hsyzygy hgapT hside

end DroppingThreeBodies
