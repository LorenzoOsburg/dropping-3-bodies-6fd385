module

public import Dropping3Bodies.Dynamics.SolutionDerivatives
public import Dropping3Bodies.EqualMass.SolutionPairRotation
public import Dropping3Bodies.EqualMass.SolutionSideOrdering
public import Dropping3Bodies.Geometry.Coordinates
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# Branch-free interior angle along a Newton trajectory

The angle is expressed with an arctangent of dot product over oriented area,
so no global direction-angle branch is chosen.
-/

namespace DroppingThreeBodies

noncomputable section

/-- The ray from body i toward its cyclic successor. -/
def angleNextRayCurve (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : Point :=
  (z t).1 (cyclicNext i) - (z t).1 i

/-- The ray from body i toward its cyclic predecessor. -/
def anglePrevRayCurve (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : Point :=
  (z t).1 (cyclicPrev i) - (z t).1 i

/-- Dot product of the two rays bounding the interior angle at body i. -/
def triangleAngleDotCurve (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  dot2 (angleNextRayCurve z i t) (anglePrevRayCurve z i t)

/-- Oriented area of the two rays bounding the interior angle at body i. -/
def triangleAngleAreaCurve (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  cross (angleNextRayCurve z i t) (anglePrevRayCurve z i t)

/-- With the cyclic order, this ray area is the global signed double area. -/
theorem triangleAngleAreaCurve_eq_signedDoubleArea
    (z : ℝ → Phase) (i : Fin 3) (t : ℝ) :
    triangleAngleAreaCurve z i t = signedDoubleArea (z t).1 := by
  fin_cases i <;>
    simp [triangleAngleAreaCurve, angleNextRayCurve, anglePrevRayCurve,
      cyclicNext, cyclicPrev, signedDoubleArea, cross] <;> ring

/-- Instantaneous derivative of the dot product of the two angle rays. -/
def triangleAngleDotRate (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  dot2 ((z t).2 (cyclicNext i) - (z t).2 i) (anglePrevRayCurve z i t) +
    dot2 (angleNextRayCurve z i t)
      ((z t).2 (cyclicPrev i) - (z t).2 i)

/-- Instantaneous derivative of the oriented double area of the angle rays. -/
def triangleAngleAreaRate (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  cross ((z t).2 (cyclicNext i) - (z t).2 i) (anglePrevRayCurve z i t) +
    cross (angleNextRayCurve z i t)
      ((z t).2 (cyclicPrev i) - (z t).2 i)
/-- The interior angle at body i, valued in (0,π) when the orientation is
    positive. -/
def triangleAngleCurve (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  Real.pi / 2 -
    Real.arctan (triangleAngleDotCurve z i t / triangleAngleAreaCurve z i t)

/-- The successor ray has the relative velocity as its derivative. -/
theorem classicalNewton_angleNextRayCurve_deriv
    {z : ℝ → Phase} {I : Set ℝ} {i : Fin 3} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (angleNextRayCurve z i)
      ((z t).2 (cyclicNext i) - (z t).2 i) t := by
  have hnext := classicalNewton_body_vector_derivatives (cyclicNext i) hsol ht
  have hi := classicalNewton_body_vector_derivatives i hsol ht
  change HasDerivAt
    (fun s => (z s).1 (cyclicNext i) - (z s).1 i)
    ((z t).2 (cyclicNext i) - (z t).2 i) t
  exact hnext.1.sub hi.1

/-- The predecessor ray has the relative velocity as its derivative. -/
theorem classicalNewton_anglePrevRayCurve_deriv
    {z : ℝ → Phase} {I : Set ℝ} {i : Fin 3} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    HasDerivAt (anglePrevRayCurve z i)
      ((z t).2 (cyclicPrev i) - (z t).2 i) t := by
  have hprev := classicalNewton_body_vector_derivatives (cyclicPrev i) hsol ht
  have hi := classicalNewton_body_vector_derivatives i hsol ht
  change HasDerivAt
    (fun s => (z s).1 (cyclicPrev i) - (z s).1 i)
    ((z t).2 (cyclicPrev i) - (z t).2 i) t
  exact hprev.1.sub hi.1

/-- Simplified instantaneous rate of the branch-free interior angle.
    This algebraic form is ready for the pair-torque identities. -/
def triangleAngleRate (z : ℝ → Phase) (i : Fin 3) (t : ℝ) : ℝ :=
  (dot2 (angleNextRayCurve z i t) (angleNextRayCurve z i t) *
      cross (anglePrevRayCurve z i t)
        ((z t).2 (cyclicPrev i) - (z t).2 i) -
    dot2 (anglePrevRayCurve z i t) (anglePrevRayCurve z i t) *
      cross (angleNextRayCurve z i t)
        ((z t).2 (cyclicNext i) - (z t).2 i)) /
    (triangleAngleAreaCurve z i t ^ 2 + triangleAngleDotCurve z i t ^ 2)

/-- Positive orientation places the branch-free angle strictly between
    zero and pi. -/
theorem triangleAngleCurve_mem_Ioo
    (z : ℝ → Phase) (i : Fin 3) (t : ℝ) :
    triangleAngleCurve z i t ∈ Set.Ioo 0 Real.pi := by
  have hlow := Real.neg_pi_div_two_lt_arctan
    (triangleAngleDotCurve z i t / triangleAngleAreaCurve z i t)
  have hhigh := Real.arctan_lt_pi_div_two
    (triangleAngleDotCurve z i t / triangleAngleAreaCurve z i t)
  constructor
  · dsimp [triangleAngleCurve]
    linarith
  · dsimp [triangleAngleCurve]
    linarith [Real.pi_pos]
/-- Differentiate the interior-angle curve on a positive-area Newton
    interval. Source: [DroppingMontgomery2026], frozen 2026-10-29,
    sec:firstsyzygy, eq:anglegrowth; this is the angle-coordinate adapter,
    not yet its force-sign estimate. -/
theorem classicalNewton_triangleAngleCurve_hasDerivAt
    {z : ℝ → Phase} {I : Set ℝ} {i : Fin 3} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I)
    (harea : 0 < signedDoubleArea (z t).1) :
    (letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
     letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
     HasDerivAt (triangleAngleCurve z i) (triangleAngleRate z i t) t) := by
  have hu := classicalNewton_angleNextRayCurve_deriv (i := i) hsol ht
  have hv := classicalNewton_anglePrevRayCurve_deriv (i := i) hsol ht
  have hD := hasDerivAt_dot2_curve hu hv
  have hB := hasDerivAt_cross_curve hu hv
  have hBpos : 0 < triangleAngleAreaCurve z i t := by
    rw [triangleAngleAreaCurve_eq_signedDoubleArea]
    exact harea
  have hBne : triangleAngleAreaCurve z i t ≠ 0 := ne_of_gt hBpos
  have hquot := hD.div hB hBne
  have hquot' : HasDerivAt
      (fun s => triangleAngleDotCurve z i s / triangleAngleAreaCurve z i s)
      ((triangleAngleDotRate z i t * triangleAngleAreaCurve z i t -
        triangleAngleDotCurve z i t * triangleAngleAreaRate z i t) /
        (triangleAngleAreaCurve z i t) ^ 2) t := by
    apply hquot.congr_deriv
    simp [triangleAngleDotCurve, triangleAngleAreaCurve, triangleAngleDotRate,
      triangleAngleAreaRate]
  have hArctan := (Real.hasDerivAt_arctan
      (triangleAngleDotCurve z i t / triangleAngleAreaCurve z i t)).comp t hquot'
  have hAngle := HasDerivAt.const_sub (Real.pi / 2) hArctan
  have halg := dotCross_derivativeNumerator_identity
    (angleNextRayCurve z i t) (anglePrevRayCurve z i t)
    ((z t).2 (cyclicNext i) - (z t).2 i)
    ((z t).2 (cyclicPrev i) - (z t).2 i)
  have hrate : (-(1 / (1 + (triangleAngleDotCurve z i t /
        triangleAngleAreaCurve z i t) ^ 2) *
      ((triangleAngleDotRate z i t * triangleAngleAreaCurve z i t -
        triangleAngleDotCurve z i t * triangleAngleAreaRate z i t) /
        (triangleAngleAreaCurve z i t) ^ 2))) = triangleAngleRate z i t := by
    have hBne' : cross (angleNextRayCurve z i t) (anglePrevRayCurve z i t) ≠ 0 := by
      simpa [triangleAngleAreaCurve] using hBne
    simp only [triangleAngleDotCurve, triangleAngleAreaCurve, triangleAngleDotRate,
      triangleAngleAreaRate, triangleAngleRate]
    field_simp [hBne']
    nlinarith [halg]
  have hAngleRate := hAngle.congr_deriv hrate
  apply hAngleRate.congr_of_eventuallyEq
  filter_upwards [] with s
  simp [triangleAngleCurve]
/-- The angle rate is the difference of the two adjacent pair rotations,
    each normalized by the squared length of its side. The cyclic index
    convention is fixed by the definitions of sideVector and angle rays. -/
theorem classicalNewton_triangleAngleRate_eq_sidePairRotationRatios
    {z : ℝ → Phase} {I : Set ℝ} {i : Fin 3} {t : ℝ}
    (hsol : ClassicalNewtonSolution z I) (ht : t ∈ I) :
    triangleAngleRate z i t =
      sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
          (cyclicNext i) t /
        (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 -
      sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
          (cyclicPrev i) t /
        (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) ^ 2 := by
  let u := angleNextRayCurve z i t
  let v := anglePrevRayCurve z i t
  let du := (z t).2 (cyclicNext i) - (z t).2 i
  let dv := (z t).2 (cyclicPrev i) - (z t).2 i
  have hnextIdx : cyclicNext i ≠ i := by
    fin_cases i <;> decide
  have hprevIdx : cyclicPrev i ≠ i := by
    fin_cases i <;> decide
  have hcf : CollisionFree (z t).1 := (hsol.2 t ht).1
  have hdist := (collisionFree_iff_dist_pos (z t).1).mp hcf
  have hnextPos : 0 < dist ((z t).1 (cyclicNext i)) ((z t).1 i) :=
    hdist (cyclicNext i) i hnextIdx
  have hprevPos : 0 < dist ((z t).1 (cyclicPrev i)) ((z t).1 i) :=
    hdist (cyclicPrev i) i hprevIdx
  have hnextDot : 0 < dot2 u u := by
    rw [← norm_sq_eq_dot2]
    have : 0 < ‖u‖ := by
      simpa [u, angleNextRayCurve, dist_eq_norm, norm_sub_rev] using hnextPos
    exact sq_pos_of_pos this
  have hprevDot : 0 < dot2 v v := by
    rw [← norm_sq_eq_dot2]
    have : 0 < ‖v‖ := by
      simpa [v, anglePrevRayCurve, dist_eq_norm, norm_sub_rev] using hprevPos
    exact sq_pos_of_pos this
  have hlag := cross_sq_add_dot2_sq u v
  rw [norm_sq_eq_dot2, norm_sq_eq_dot2] at hlag
  have hden : triangleAngleAreaCurve z i t ^ 2 +
      triangleAngleDotCurve z i t ^ 2 = dot2 u u * dot2 v v := by
    simpa [u, v, triangleAngleAreaCurve, triangleAngleDotCurve] using hlag
  have hnextRot :
      sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
          (cyclicNext i) t = cross v dv := by
    fin_cases i <;>
      simp [sidePairRotationCurve, sideVectorCurve, solutionPositionCurve,
        solutionVelocityCurve, sideVector, anglePrevRayCurve, cyclicNext,
        cyclicPrev, v, dv, cross] <;> ring
  have hprevRot :
      sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
          (cyclicPrev i) t = cross u du := by
    fin_cases i <;>
      simp [sidePairRotationCurve, sideVectorCurve, solutionPositionCurve,
        solutionVelocityCurve, sideVector, angleNextRayCurve, cyclicNext,
        cyclicPrev, u, du, cross]
  have hnextLen :
      (dist ((z t).1 (cyclicNext i)) ((z t).1 i)) ^ 2 = dot2 u u := by
    rw [dist_eq_norm]
    rw [← norm_sq_eq_dot2]
    simp [u, angleNextRayCurve, norm_sub_rev]
  have hprevLen :
      (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 = dot2 v v := by
    rw [dist_eq_norm]
    rw [← norm_sq_eq_dot2]
    simp [v, anglePrevRayCurve, norm_sub_rev]
  rw [triangleAngleRate, hnextRot, hprevRot, hden, hprevLen, hnextLen]
  field_simp [ne_of_gt hnextDot, ne_of_gt hprevDot]
  ring

/-- If the side opposite `i` is initially strictly longest, then the angle
    at `i` has strictly positive instantaneous rate at every later time of a
    compact collision-free positive-area segment. This is conditional on an
    already-given classical Newton solution and does not give a uniform lower
    bound for the rate. -/
theorem classicalNewton_triangleAngleRate_pos_on_Icc_of_initial_opposite_side_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ}
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (harea : ∀ s ∈ Set.Icc a T, 0 < signedDoubleArea (z s).1)
    {t : ℝ} (ht : t ∈ Set.Icc a T) (hat : a < t) :
    0 < triangleAngleRate z i t := by
  have hgapNext : sideGap (z a).1 (cyclicNext i) < 0 := by
    rw [sideGap_eq_next_sub_prev_sideSq, cyclicNext_cyclicNext,
      cyclicPrev_cyclicNext]
    exact sub_neg.mpr hlongPrev
  have hgapPrev : 0 < sideGap (z a).1 (cyclicPrev i) := by
    rw [sideGap_eq_next_sub_prev_sideSq, cyclicNext_cyclicPrev,
      cyclicPrev_cyclicPrev]
    exact sub_pos.mpr hlongNext
  have hsegmentT : Set.Icc a t ⊆ I := by
    intro s hs
    exact hsegment ⟨hs.1, le_trans hs.2 ht.2⟩
  have hareaT : ∀ s ∈ Set.Icc a t, 0 < signedDoubleArea (z s).1 := by
    intro s hs
    exact harea s ⟨hs.1, le_trans hs.2 ht.2⟩
  have hnextRot := classicalNewton_orientedRotation_pos_of_nonzero_sideGap
    (cyclicNext i) hsol hconn hat hsegmentT hrest hcenter
    (ne_of_lt hgapNext) hareaT
  have hprevRot := classicalNewton_orientedRotation_pos_of_nonzero_sideGap
    (cyclicPrev i) hsol hconn hat hsegmentT hrest hcenter
    (ne_of_gt hgapPrev) hareaT
  have hnextL : 0 < sidePairRotationCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) (cyclicNext i) t := by
    rw [if_neg (not_lt_of_ge (le_of_lt hgapNext))] at hnextRot
    simpa [sideGapRotationSignCurve] using hnextRot
  have hprevL : sidePairRotationCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) (cyclicPrev i) t < 0 := by
    rw [if_pos hgapPrev] at hprevRot
    simpa [sideGapRotationSignCurve] using hprevRot
  have hcf : CollisionFree (z t).1 := (hsol.2 t (hsegment ht)).1
  have hdist := (collisionFree_iff_dist_pos (z t).1).mp hcf
  have hnextIdx : cyclicNext i ≠ i := by fin_cases i <;> decide
  have hprevIdx : cyclicPrev i ≠ i := by fin_cases i <;> decide
  have hnextDist : 0 < dist ((z t).1 (cyclicNext i)) ((z t).1 i) :=
    hdist (cyclicNext i) i hnextIdx
  have hprevDist : 0 < dist ((z t).1 (cyclicPrev i)) ((z t).1 i) :=
    hdist (cyclicPrev i) i hprevIdx
  have hnextQuotient : 0 < (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 :=
    sq_pos_of_pos hprevDist
  have hnextFraction : 0 <
      sidePairRotationCurve (solutionPositionCurve z) (solutionVelocityCurve z)
        (cyclicNext i) t / (dist ((z t).1 (cyclicPrev i)) ((z t).1 i)) ^ 2 :=
    div_pos hnextL hnextQuotient
  have hprevFraction : sidePairRotationCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) (cyclicPrev i) t / (dist ((z t).1 (cyclicNext i))
        ((z t).1 i)) ^ 2 < 0 :=
    div_neg_of_neg_of_pos hprevL (sq_pos_of_pos hnextDist)
  rw [classicalNewton_triangleAngleRate_eq_sidePairRotationRatios hsol
    (hsegment ht)]
  linarith [hnextFraction, hprevFraction]

/-- Under the same hypotheses, the branch-free angle is strictly increasing
    after the initial time. The interval excludes `a`, where initial rest
    makes the derivative zero. -/
theorem classicalNewton_triangleAngleCurve_strictMonoOn_Ioc_of_initial_opposite_side_strictLongest
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {a T : ℝ}
    (hsegment : Set.Icc a T ⊆ I)
    (hrest : ∀ b, (z a).2 b = 0)
    (hcenter : (z a).1 0 + (z a).1 1 + (z a).1 2 = 0)
    (hlongNext : sideSq (z a).1 i > sideSq (z a).1 (cyclicNext i))
    (hlongPrev : sideSq (z a).1 i > sideSq (z a).1 (cyclicPrev i))
    (harea : ∀ s ∈ Set.Icc a T, 0 < signedDoubleArea (z s).1) :
    StrictMonoOn (triangleAngleCurve z i) (Set.Ioc a T) := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  apply strictMonoOn_of_hasDerivAt_pos (convex_Ioc a T)
  · intro t ht
    have htIcc : t ∈ Set.Icc a T := ⟨le_of_lt ht.1, ht.2⟩
    exact classicalNewton_triangleAngleCurve_hasDerivAt hsol
      (hsegment htIcc) (harea t htIcc)
  · intro t ht
    exact classicalNewton_triangleAngleRate_pos_on_Icc_of_initial_opposite_side_strictLongest
      i hsol hconn hsegment hrest hcenter hlongNext hlongPrev harea
      ⟨le_of_lt ht.1, ht.2⟩ ht.1
end

end DroppingThreeBodies
