module

public import Dropping3Bodies.EqualMass.SideFrame
public import Mathlib.Tactic

@[expose] public section

/-!
The undivided kinematic side-gap identity, in a fixed side frame.  The rate
arguments are independent vectors: the theorem is an algebraic directional-
derivative identity and does not assume a trajectory or a nonzero area.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Signed area in a fixed side frame. -/
def frameArea (r s : Point) : ℝ := cross r s

/-- The squared-side gap in side-frame coordinates. -/
def frameGap (r s : Point) : ℝ := -2 * dot2 r s

/-- Directional rate of the frame area. -/
def frameAreaRate (r s rd sd : Point) : ℝ := cross rd s + cross r sd

/-- Directional rate of the squared-side gap. -/
def frameGapRate (r s rd sd : Point) : ℝ :=
  -2 * (dot2 rd s + dot2 r sd)

/-- Pair rotation in the frame. -/
def framePairRotation (r rd : Point) : ℝ := cross r rd

/-- Equal-unit-mass moment in side-frame coordinates. -/
def frameMoment (r s : Point) : ℝ := ‖r‖ ^ 2 / 2 + 2 * ‖s‖ ^ 2 / 3

/-- Zero-center-of-mass angular momentum in side-frame coordinates. -/
def frameAngularMomentum (r s rd sd : Point) : ℝ :=
  cross r rd / 2 + 2 * cross s sd / 3

/-- D3B-S02; PAPER-20261029 `eq:gap`; own algebraic directional-derivative
    identity. It is undivided and valid even when the area is zero. -/
theorem frame_gap_rate_identity (r s rd sd : Point) :
    frameArea r s * frameGapRate r s rd sd -
      frameGap r s * frameAreaRate r s rd sd =
        -3 * frameMoment r s * framePairRotation r rd +
          3 * ‖r‖ ^ 2 * frameAngularMomentum r s rd sd := by
  simp [frameArea, frameGap, frameAreaRate, frameGapRate, frameMoment,
    framePairRotation, frameAngularMomentum, cross, dot2,
    EuclideanSpace.real_norm_sq_eq]
  ring

end

end DroppingThreeBodies
