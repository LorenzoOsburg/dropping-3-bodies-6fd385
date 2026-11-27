module

public import Dropping3Bodies.Geometry.Inertia
public import Dropping3Bodies.Geometry.BodyIndex

@[expose] public section

/-!
Basic side-frame quantities for equal-mass centered configurations.
-/

namespace DroppingThreeBodies

noncomputable section

/-- D3B-S01; PAPER-20261029 `eq:rs`; relative side vector in the cyclic frame. -/
def sideVector (q : Fin 3 → Point) (i : Fin 3) : Point :=
  match i with
  | 0 => q 2 - q 1
  | 1 => q 0 - q 2
  | _ => q 1 - q 0

/-- Offset of body `i` from the midpoint of the opposite side. -/
def sideOffset (q : Fin 3 → Point) (i : Fin 3) : Point :=
  match i with
  | 0 => q 0 - ((1 / 2 : ℝ) • (q 1 + q 2))
  | 1 => q 1 - ((1 / 2 : ℝ) • (q 2 + q 0))
  | _ => q 2 - ((1 / 2 : ℝ) • (q 0 + q 1))

/-- Geometric centroid of a three-body configuration with equal weights. -/
def configurationCentroid (q : Fin 3 → Point) : Point :=
  (1 / 3 : ℝ) • (q 0 + q 1 + q 2)

/-- Recover the distinguished body position from its frame offset and centroid. -/
theorem sideFrame_reconstruct_body (q : Fin 3 → Point) (i : Fin 3) :
    q i = configurationCentroid q + (2 / 3 : ℝ) • sideOffset q i := by
  fin_cases i <;> ext k <;>
    simp [configurationCentroid, sideOffset] <;> ring

/-- Recover the previous cyclic body from the centroid and side frame. -/
theorem sideFrame_reconstruct_prev (q : Fin 3 → Point) (i : Fin 3) :
    q (cyclicPrev i) = configurationCentroid q - (1 / 3 : ℝ) • sideOffset q i +
      (1 / 2 : ℝ) • sideVector q i := by
  fin_cases i <;> ext k <;>
    simp [configurationCentroid, sideOffset, sideVector, cyclicPrev] <;> ring

/-- Recover the next cyclic body from the centroid and side frame. -/
theorem sideFrame_reconstruct_next (q : Fin 3 → Point) (i : Fin 3) :
    q (cyclicNext i) = configurationCentroid q - (1 / 3 : ℝ) • sideOffset q i -
      (1 / 2 : ℝ) • sideVector q i := by
  fin_cases i <;> ext k <;>
    simp [configurationCentroid, sideOffset, sideVector, cyclicNext] <;> ring

/-- Squared-side gap opposite `i`, with a cyclic convention. -/
def sideGap (q : Fin 3 → Point) (i : Fin 3) : ℝ :=
  match i with
  | 0 => ‖q 2 - q 0‖ ^ 2 - ‖q 0 - q 1‖ ^ 2
  | 1 => ‖q 0 - q 1‖ ^ 2 - ‖q 1 - q 2‖ ^ 2
  | _ => ‖q 1 - q 2‖ ^ 2 - ‖q 2 - q 0‖ ^ 2

/-- Squared length of the side opposite the cyclic body index. -/
def sideSq (q : Fin 3 → Point) (i : Fin 3) : ℝ :=
  ‖sideVector q i‖ ^ 2

/-- The gap convention is the cyclic difference of the two adjacent sides:
`gap i = sideSq (next i) - sideSq (prev i)`. -/
theorem sideGap_eq_next_sub_prev_sideSq (q : Fin 3 → Point) (i : Fin 3) :
    sideGap q i = sideSq q (cyclicNext i) - sideSq q (cyclicPrev i) := by
  fin_cases i <;>
    simp [sideGap, sideSq, sideVector, cyclicNext, cyclicPrev, norm_sub_rev]

/-- The side opposite `i` joins its cyclic predecessor and successor. -/
theorem sideSq_eq_cyclicNeighborDistance (q : Fin 3 → Point) (i : Fin 3) :
    sideSq q i = dist (q (cyclicPrev i)) (q (cyclicNext i)) ^ 2 := by
  fin_cases i <;>
    simp [sideSq, sideVector, cyclicNext, cyclicPrev, dist_eq_norm, norm_sub_rev]
/-- D3B-S01; PAPER-20261029 `eq:Brs`; cyclic-frame area matches global orientation. -/
theorem signedDoubleArea_eq_cross_sideFrame (q : Fin 3 → Point) (i : Fin 3) :
    cross (sideVector q i) (sideOffset q i) = signedDoubleArea q := by
  fin_cases i <;> simp [sideVector, sideOffset, signedDoubleArea, cross] <;> ring

/-- D3B-S01; PAPER-20261029 `eq:frs`; squared-side gap is minus twice
    the side-offset dot product. -/
theorem sideGap_eq_neg_two_dot_sideFrame (q : Fin 3 → Point) (i : Fin 3) :
    sideGap q i = -2 * dot2 (sideVector q i) (sideOffset q i) := by
  fin_cases i <;> simp [sideGap, sideVector, sideOffset, dot2,
    EuclideanSpace.real_norm_sq_eq] <;> ring

/-- D3B-S01; PAPER-20261029 `eq:Irs`; centered equal-unit-mass inertia formula. -/
theorem massMoment_eq_sideFrame (q : Fin 3 → Point) (i : Fin 3)
    (hcenter : q 0 + q 1 + q 2 = 0) :
    massMoment (fun _ : Fin 3 => (1 : ℝ)) q =
      ‖sideVector q i‖ ^ 2 / 2 + 2 * ‖sideOffset q i‖ ^ 2 / 3 := by
  have hc0 : q 0 0 + q 1 0 + q 2 0 = 0 := by
    simpa using congrArg (fun p : Point => p 0) hcenter
  have hc1 : q 0 1 + q 1 1 + q 2 1 = 0 := by
    simpa using congrArg (fun p : Point => p 1) hcenter
  fin_cases i <;>
    simp [massMoment, sideVector, sideOffset, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succ] <;>
    nlinarith [sq_nonneg (q 0 0), sq_nonneg (q 0 1)]

end

end DroppingThreeBodies
