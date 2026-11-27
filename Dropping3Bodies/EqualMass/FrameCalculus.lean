module

public import Dropping3Bodies.EqualMass.GapIdentity
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
Calculus adapters connecting the fixed-frame algebra to differentiable curves.
-/

namespace DroppingThreeBodies

/-- A componentwise derivative witness for a planar curve. -/
def HasCoordDerivAt (q : ℝ → Point) (v : Point) (t : ℝ) : Prop :=
  ∀ k : Fin 2, HasDerivAt (fun τ => q τ k) (v k) t

/-- Product rule for the coordinate dot product under componentwise
    differentiability witnesses. -/
theorem hasDerivAt_dot2Curve_of_coordDerivAt
    {r s : ℝ → Point} {rd sd : Point} {t : ℝ}
    (hr : HasCoordDerivAt r rd t) (hs : HasCoordDerivAt s sd t) :
    HasDerivAt (fun τ => dot2 (r τ) (s τ))
      (dot2 rd (s t) + dot2 (r t) sd) t := by
  have h0 := (hr 0).mul (hs 0)
  have h1 := (hr 1).mul (hs 1)
  have hpair := h0.add h1
  change HasDerivAt (fun τ => r τ 0 * s τ 0 + r τ 1 * s τ 1)
    (dot2 rd (s t) + dot2 (r t) sd) t
  exact hpair.congr_deriv (by simp [dot2]; ring)

/-- Norm-square product rule derived from componentwise differentiability. -/
theorem hasDerivAt_normSqCurve_of_coordDerivAt
    {r : ℝ → Point} {rd : Point} {t : ℝ}
    (hr : HasCoordDerivAt r rd t) :
    HasDerivAt (fun τ => ‖r τ‖ ^ 2) (2 * dot2 (r t) rd) t := by
  have h := hasDerivAt_dot2Curve_of_coordDerivAt hr hr
  have hnorm : HasDerivAt (fun τ => ‖r τ‖ ^ 2)
      (dot2 rd (r t) + dot2 (r t) rd) t := by
    simpa only [norm_sq_eq_dot2] using h
  exact hnorm.congr_deriv (by simp [dot2]; ring)

/-- The frame area along two curves. -/
def frameAreaCurve (r s : ℝ → Point) (t : ℝ) : ℝ :=
  cross (r t) (s t)

/-- The frame gap along two curves. -/
def frameGapCurve (r s : ℝ → Point) (t : ℝ) : ℝ :=
  -2 * dot2 (r t) (s t)

/-- Product-rule derivative of frame area, requiring only coordinate derivatives. -/
theorem hasDerivAt_frameAreaCurve {r s : ℝ → Point} {rd sd : Point} {t : ℝ}
    (hr : HasCoordDerivAt r rd t) (hs : HasCoordDerivAt s sd t) :
    HasDerivAt (frameAreaCurve r s) (frameAreaRate (r t) (s t) rd sd) t := by
  have h₁ := (hr 0).mul (hs 1)
  have h₂ := (hr 1).mul (hs 0)
  have h := HasDerivAt.sub h₁ h₂
  have hder : HasDerivAt (fun τ => (r τ 0) * (s τ 1) - (r τ 1) * (s τ 0))
      (frameAreaRate (r t) (s t) rd sd) t :=
    h.congr_deriv (by simp [frameAreaRate, cross]; ring)
  change HasDerivAt (fun τ => (r τ).ofLp 0 * (s τ).ofLp 1 -
    (r τ).ofLp 1 * (s τ).ofLp 0) (frameAreaRate (r t) (s t) rd sd) t
  exact hder

/-- Product-rule derivative of frame gap, requiring only coordinate derivatives. -/
theorem hasDerivAt_frameGapCurve {r s : ℝ → Point} {rd sd : Point} {t : ℝ}
    (hr : HasCoordDerivAt r rd t) (hs : HasCoordDerivAt s sd t) :
    HasDerivAt (frameGapCurve r s) (frameGapRate (r t) (s t) rd sd) t := by
  have h₁ := (hr 0).mul (hs 0)
  have h₂ := (hr 1).mul (hs 1)
  have h := HasDerivAt.const_mul (-2 : ℝ) (HasDerivAt.add h₁ h₂)
  have hder : HasDerivAt (fun τ => -2 * ((r τ 0) * (s τ 0) + (r τ 1) * (s τ 1)))
      (frameGapRate (r t) (s t) rd sd) t :=
    h.congr_deriv (by simp [frameGapRate, dot2]; ring)
  change HasDerivAt (fun τ => -2 * ((r τ).ofLp 0 * (s τ).ofLp 0 +
    (r τ).ofLp 1 * (s τ).ofLp 1)) (frameGapRate (r t) (s t) rd sd) t
  exact hder

/-- D3B-S02; PAPER-20261029 `eq:gap`; curve-level undivided identity at
    a zero-angular-momentum instant, including area-zero instants. -/
theorem frame_gap_curve_derivative_identity
    {r s : ℝ → Point} {rd sd : Point} {t : ℝ}
    (hr : HasCoordDerivAt r rd t) (hs : HasCoordDerivAt s sd t)
    (hL : frameAngularMomentum (r t) (s t) rd sd = 0) :
    frameAreaCurve r s t * deriv (frameGapCurve r s) t -
      frameGapCurve r s t * deriv (frameAreaCurve r s) t =
        -3 * frameMoment (r t) (s t) * framePairRotation (r t) rd := by
  have hgap := (hasDerivAt_frameGapCurve hr hs).deriv
  have harea := (hasDerivAt_frameAreaCurve hr hs).deriv
  have halg := frame_gap_rate_identity (r t) (s t) rd sd
  simp [hL] at halg
  rw [hgap, harea]
  simpa [frameAreaCurve, frameGapCurve, frameArea, frameGap] using halg


/-- On a nonzero-area instant with zero side-frame angular momentum, the
    normalized squared-side gap `f/B` has derivative `-3 I K/B²`. -/
theorem hasDerivAt_frameGapRatioCurve
    {r s : ℝ → Point} {rd sd : Point} {t : ℝ}
    (hr : HasCoordDerivAt r rd t) (hs : HasCoordDerivAt s sd t)
    (hL : frameAngularMomentum (r t) (s t) rd sd = 0)
    (hB : frameArea (r t) (s t) ≠ 0) :
    HasDerivAt (fun τ => frameGapCurve r s τ / frameAreaCurve r s τ)
      ((-3 * frameMoment (r t) (s t) * framePairRotation (r t) rd) /
        (frameArea (r t) (s t)) ^ 2) t := by
  have hgap := hasDerivAt_frameGapCurve hr hs
  have harea := hasDerivAt_frameAreaCurve hr hs
  have hquot := hgap.div harea (by simpa [frameAreaCurve, frameArea] using hB)
  have hkin := frame_gap_rate_identity (r t) (s t) rd sd
  rw [hL] at hkin
  have hnum :
      frameGapRate (r t) (s t) rd sd * frameArea (r t) (s t) -
        frameGap (r t) (s t) * frameAreaRate (r t) (s t) rd sd =
          -3 * frameMoment (r t) (s t) * framePairRotation (r t) rd := by
    nlinarith [hkin]
  apply hquot.congr_deriv
  change (frameGapRate (r t) (s t) rd sd * frameArea (r t) (s t) -
      frameGap (r t) (s t) * frameAreaRate (r t) (s t) rd sd) /
      (frameArea (r t) (s t)) ^ 2 =
    (-3 * frameMoment (r t) (s t) * framePairRotation (r t) rd) /
      (frameArea (r t) (s t)) ^ 2
  rw [hnum]

/-- The full normalized-gap derivative without assuming zero frame angular
    momentum. The extra term records exactly what must be controlled when the
    equal-mass centered-frame identity is unavailable. -/
theorem hasDerivAt_frameGapRatioCurve_general
    {r s : ℝ → Point} {rd sd : Point} {t : ℝ}
    (hr : HasCoordDerivAt r rd t) (hs : HasCoordDerivAt s sd t)
    (hB : frameArea (r t) (s t) ≠ 0) :
    HasDerivAt (fun τ => frameGapCurve r s τ / frameAreaCurve r s τ)
      ((-3 * frameMoment (r t) (s t) * framePairRotation (r t) rd +
          3 * ‖r t‖ ^ 2 * frameAngularMomentum (r t) (s t) rd sd) /
        (frameArea (r t) (s t)) ^ 2) t := by
  have hgap := hasDerivAt_frameGapCurve hr hs
  have harea := hasDerivAt_frameAreaCurve hr hs
  have hquot := hgap.div harea (by simpa [frameAreaCurve, frameArea] using hB)
  have hkin := frame_gap_rate_identity (r t) (s t) rd sd
  have hnum :
      frameGapRate (r t) (s t) rd sd * frameArea (r t) (s t) -
        frameGap (r t) (s t) * frameAreaRate (r t) (s t) rd sd =
          -3 * frameMoment (r t) (s t) * framePairRotation (r t) rd +
            3 * ‖r t‖ ^ 2 * frameAngularMomentum (r t) (s t) rd sd := by
    nlinarith [hkin]
  apply hquot.congr_deriv
  change (frameGapRate (r t) (s t) rd sd * frameArea (r t) (s t) -
      frameGap (r t) (s t) * frameAreaRate (r t) (s t) rd sd) /
      (frameArea (r t) (s t)) ^ 2 =
    (-3 * frameMoment (r t) (s t) * framePairRotation (r t) rd +
        3 * ‖r t‖ ^ 2 * frameAngularMomentum (r t) (s t) rd sd) /
      (frameArea (r t) (s t)) ^ 2
  rw [hnum]


/-- Componentwise differentiability data for all three body positions. -/
def HasBodyCoordDerivAt (q : Fin 3 → ℝ → Point) (v : Fin 3 → Point) (t : ℝ) : Prop :=
  ∀ i k, HasDerivAt (fun τ => q i τ k) (v i k) t

/-- The cyclic side vector along body-position curves. -/
noncomputable def sideVectorCurve (q : Fin 3 → ℝ → Point) (i : Fin 3) (t : ℝ) : Point :=
  sideVector (fun b => q b t) i

/-- The cyclic midpoint offset along body-position curves. -/
noncomputable def sideOffsetCurve (q : Fin 3 → ℝ → Point) (i : Fin 3) (t : ℝ) : Point :=
  sideOffset (fun b => q b t) i

/-- The side-vector curve has the expected relative velocity. -/
theorem hasCoordDerivAt_sideVectorCurve
    {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {t : ℝ}
    (h : HasBodyCoordDerivAt q v t) (i : Fin 3) :
    HasCoordDerivAt (fun τ => sideVectorCurve q i τ) (sideVector v i) t := by
  intro k
  fin_cases i
  · change HasDerivAt (fun τ => q 2 τ k - q 1 τ k) (v 2 k - v 1 k) t
    exact (h 2 k).sub (h 1 k)
  · change HasDerivAt (fun τ => q 0 τ k - q 2 τ k) (v 0 k - v 2 k) t
    exact (h 0 k).sub (h 2 k)
  · change HasDerivAt (fun τ => q 1 τ k - q 0 τ k) (v 1 k - v 0 k) t
    exact (h 1 k).sub (h 0 k)

/-- Derivative of each squared side length along body-position curves. -/
theorem hasDerivAt_sideSqCurve
    {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {t : ℝ}
    (h : HasBodyCoordDerivAt q v t) (i : Fin 3) :
    HasDerivAt (fun τ => sideSq (fun b => q b τ) i)
      (2 * dot2 (sideVector (fun b => q b t) i) (sideVector v i)) t := by
  have hside := hasCoordDerivAt_sideVectorCurve h i
  have hsquare := hasDerivAt_normSqCurve_of_coordDerivAt hside
  simpa [sideSq, sideVectorCurve] using hsquare

/-- The integral of a frame-area rate is the oriented area change, assuming
    the rate is interval-integrable. -/
theorem intervalIntegral_frameAreaRate_eq_sub
    {r s rd sd : ℝ → Point} {a b : ℝ}
    (hderiv : ∀ τ ∈ Set.uIcc a b,
      HasCoordDerivAt r (rd τ) τ ∧ HasCoordDerivAt s (sd τ) τ)
    (hint : IntervalIntegrable
      (fun τ => frameAreaRate (r τ) (s τ) (rd τ) (sd τ))
      MeasureTheory.volume a b) :
    ∫ τ in a..b, frameAreaRate (r τ) (s τ) (rd τ) (sd τ) =
      frameAreaCurve r s b - frameAreaCurve r s a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro τ hτ
    exact hasDerivAt_frameAreaCurve (hderiv τ hτ).1 (hderiv τ hτ).2
  · exact hint

/-- The integral of a frame-gap rate is the endpoint gap change, under the
    explicit interval-integrability hypothesis. -/
theorem intervalIntegral_frameGapRate_eq_sub
    {r s rd sd : ℝ → Point} {a b : ℝ}
    (hderiv : ∀ τ ∈ Set.uIcc a b,
      HasCoordDerivAt r (rd τ) τ ∧ HasCoordDerivAt s (sd τ) τ)
    (hint : IntervalIntegrable
      (fun τ => frameGapRate (r τ) (s τ) (rd τ) (sd τ))
      MeasureTheory.volume a b) :
    ∫ τ in a..b, frameGapRate (r τ) (s τ) (rd τ) (sd τ) =
      frameGapCurve r s b - frameGapCurve r s a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro τ hτ
    exact hasDerivAt_frameGapCurve (hderiv τ hτ).1 (hderiv τ hτ).2
  · exact hint

/-- The integrated squared-side rate equals the change of the squared side.
    Its integrability is intentionally a separate assumption. -/
theorem intervalIntegral_sideSqRate_eq_sub
    {q : Fin 3 → ℝ → Point} {v : ℝ → Fin 3 → Point}
    {a b : ℝ} (i : Fin 3)
    (hderiv : ∀ τ ∈ Set.uIcc a b, HasBodyCoordDerivAt q (v τ) τ)
    (hint : IntervalIntegrable
      (fun τ => 2 * dot2 (sideVector (fun j => q j τ) i) (sideVector (v τ) i))
      MeasureTheory.volume a b) :
    ∫ τ in a..b,
      2 * dot2 (sideVector (fun j => q j τ) i) (sideVector (v τ) i) =
      sideSq (fun j => q j b) i - sideSq (fun j => q j a) i := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro τ hτ
    exact hasDerivAt_sideSqCurve (hderiv τ hτ) i
  · exact hint

/-- A continuous position curve and velocity curve make the squared-side
    rate interval-integrable on the compact interval. -/
theorem intervalIntegrable_sideSqRate_of_continuousOn
    {q v : ℝ → Fin 3 → Point} {a b : ℝ} (i : Fin 3)
    (hq : ContinuousOn q (Set.uIcc a b))
    (hv : ContinuousOn v (Set.uIcc a b)) :
    IntervalIntegrable
      (fun τ => 2 * dot2 (sideVector (q τ) i) (sideVector (v τ) i))
      MeasureTheory.volume a b := by
  have hq0 : ContinuousOn (fun τ => q τ 0) (Set.uIcc a b) := by fun_prop
  have hq1 : ContinuousOn (fun τ => q τ 1) (Set.uIcc a b) := by fun_prop
  have hq2 : ContinuousOn (fun τ => q τ 2) (Set.uIcc a b) := by fun_prop
  have hv0 : ContinuousOn (fun τ => v τ 0) (Set.uIcc a b) := by fun_prop
  have hv1 : ContinuousOn (fun τ => v τ 1) (Set.uIcc a b) := by fun_prop
  have hv2 : ContinuousOn (fun τ => v τ 2) (Set.uIcc a b) := by fun_prop
  have hsideQ : ContinuousOn (fun τ => sideVector (q τ) i) (Set.uIcc a b) := by
    fin_cases i
    · change ContinuousOn (fun τ => q τ 2 - q τ 1) _
      exact hq2.sub hq1
    · change ContinuousOn (fun τ => q τ 0 - q τ 2) _
      exact hq0.sub hq2
    · change ContinuousOn (fun τ => q τ 1 - q τ 0) _
      exact hq1.sub hq0
  have hsideV : ContinuousOn (fun τ => sideVector (v τ) i) (Set.uIcc a b) := by
    fin_cases i
    · change ContinuousOn (fun τ => v τ 2 - v τ 1) _
      exact hv2.sub hv1
    · change ContinuousOn (fun τ => v τ 0 - v τ 2) _
      exact hv0.sub hv2
    · change ContinuousOn (fun τ => v τ 1 - v τ 0) _
      exact hv1.sub hv0
  have hdot : ContinuousOn
      (fun τ => dot2 (sideVector (q τ) i) (sideVector (v τ) i))
      (Set.uIcc a b) := by
    simp only [dot2]
    fun_prop
  exact (hdot.const_mul 2).intervalIntegrable

/-- The offset curve has the expected velocity relative to the opposite midpoint. -/
theorem hasCoordDerivAt_sideOffsetCurve
    {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {t : ℝ}
    (h : HasBodyCoordDerivAt q v t) (i : Fin 3) :
    HasCoordDerivAt (fun τ => sideOffsetCurve q i τ) (sideOffset v i) t := by
  intro k
  fin_cases i
  · have hmid := HasDerivAt.const_mul (1 / 2 : ℝ) (HasDerivAt.add (h 1 k) (h 2 k))
    have hsub := HasDerivAt.sub (h 0 k) hmid
    have hv : (v 0).ofLp k - 1 / 2 * ((v 1).ofLp k + (v 2).ofLp k) =
        sideOffset v 0 k := by simp [sideOffset]; ring
    have hder : HasDerivAt
        (fun τ => (q 0 τ).ofLp k - 1 / 2 * ((q 1 τ).ofLp k + (q 2 τ).ofLp k))
        (sideOffset v 0 k) t := hsub.congr_deriv hv
    simpa [sideOffsetCurve, sideOffset] using
      hder.congr_of_eventuallyEq (by filter_upwards [] with τ; ring)
  · have hmid := HasDerivAt.const_mul (1 / 2 : ℝ) (HasDerivAt.add (h 2 k) (h 0 k))
    have hsub := HasDerivAt.sub (h 1 k) hmid
    have hv : (v 1).ofLp k - 1 / 2 * ((v 2).ofLp k + (v 0).ofLp k) =
        sideOffset v 1 k := by simp [sideOffset]; ring
    have hder : HasDerivAt
        (fun τ => (q 1 τ).ofLp k - 1 / 2 * ((q 2 τ).ofLp k + (q 0 τ).ofLp k))
        (sideOffset v 1 k) t := hsub.congr_deriv hv
    simpa [sideOffsetCurve, sideOffset] using
      hder.congr_of_eventuallyEq (by filter_upwards [] with τ; ring)
  · have hmid := HasDerivAt.const_mul (1 / 2 : ℝ) (HasDerivAt.add (h 0 k) (h 1 k))
    have hsub := HasDerivAt.sub (h 2 k) hmid
    have hv : (v 2).ofLp k - 1 / 2 * ((v 0).ofLp k + (v 1).ofLp k) =
        sideOffset v 2 k := by simp [sideOffset]; ring
    have hder : HasDerivAt
        (fun τ => (q 2 τ).ofLp k - 1 / 2 * ((q 0 τ).ofLp k + (q 1 τ).ofLp k))
        (sideOffset v 2 k) t := hsub.congr_deriv hv
    simpa [sideOffsetCurve, sideOffset] using
      hder.congr_of_eventuallyEq (by filter_upwards [] with τ; ring)


/-- The curve-level gap identity for the cyclic frame induced by three body
    position curves, assuming the frame angular momentum vanishes. -/
theorem bodyCurve_gap_derivative_identity
    {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {t : ℝ} (i : Fin 3)
    (h : HasBodyCoordDerivAt q v t)
    (hL : frameAngularMomentum (sideVector (fun b => q b t) i)
      (sideOffset (fun b => q b t) i) (sideVector v i) (sideOffset v i) = 0) :
    frameAreaCurve (fun τ => sideVectorCurve q i τ)
        (fun τ => sideOffsetCurve q i τ) t *
      deriv (frameGapCurve (fun τ => sideVectorCurve q i τ)
        (fun τ => sideOffsetCurve q i τ)) t -
      frameGapCurve (fun τ => sideVectorCurve q i τ)
        (fun τ => sideOffsetCurve q i τ) t *
      deriv (frameAreaCurve (fun τ => sideVectorCurve q i τ)
        (fun τ => sideOffsetCurve q i τ)) t =
      -3 * frameMoment (sideVector (fun b => q b t) i)
        (sideOffset (fun b => q b t) i) *
        framePairRotation (sideVector (fun b => q b t) i) (sideVector v i) := by
  exact frame_gap_curve_derivative_identity
    (hasCoordDerivAt_sideVectorCurve h i)
    (hasCoordDerivAt_sideOffsetCurve h i) (by simpa [sideVectorCurve, sideOffsetCurve] using hL)


/-- Physical total angular momentum for three unit masses. -/
def totalAngularMomentum (q v : Fin 3 → Point) : ℝ :=
  ∑ i : Fin 3, cross (q i) (v i)

/-- In the center-of-mass frame, the side-frame angular momentum equals the
    physical total angular momentum, for each cyclic side frame. -/
theorem frameAngularMomentum_eq_total_of_centered
    (q v : Fin 3 → Point) (i : Fin 3)
    (hq : q 0 + q 1 + q 2 = 0) (hv : v 0 + v 1 + v 2 = 0) :
    frameAngularMomentum (sideVector q i) (sideOffset q i)
      (sideVector v i) (sideOffset v i) = totalAngularMomentum q v := by
  have hq0 : q 0 0 + q 1 0 + q 2 0 = 0 := by
    simpa using congrArg (fun p : Point => p 0) hq
  have hq1 : q 0 1 + q 1 1 + q 2 1 = 0 := by
    simpa using congrArg (fun p : Point => p 1) hq
  have hv0 : v 0 0 + v 1 0 + v 2 0 = 0 := by
    simpa using congrArg (fun p : Point => p 0) hv
  have hv1 : v 0 1 + v 1 1 + v 2 1 = 0 := by
    simpa using congrArg (fun p : Point => p 1) hv
  fin_cases i <;>
    simp [frameAngularMomentum, sideVector, sideOffset, totalAngularMomentum,
      cross, Fin.sum_univ_succ] <;>
    nlinarith

end DroppingThreeBodies
