module

public import Dropping3Bodies.Geometry.Coordinates
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-!
Algebraic relations between the mass moment and the pair moment.
-/

namespace DroppingThreeBodies

noncomputable section

/-- D3B-F02; PAPER-20261029 `eq:Im`; own finite algebraic expansion.
    Pair-moment identity, valid without centering. -/
theorem pairMoment_eq_totalMass_mul_massMoment_sub_weightedPosition_sq
    (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    pairMoment m q = totalMass m * massMoment m q - ‖weightedPosition m q‖ ^ 2 := by
  classical
  simp [pairMoment, totalMass, massMoment, weightedPosition,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ, Real.dist_eq, sq_abs]
  ring

/-- D3B-F02; PAPER-20261029 `eq:Im`; centered pair moment equals total mass
    times the mass moment about the origin. -/
theorem pairMoment_eq_totalMass_mul_massMoment_of_centered
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hcenter : weightedPosition m q = 0) :
    pairMoment m q = totalMass m * massMoment m q := by
  rw [pairMoment_eq_totalMass_mul_massMoment_sub_weightedPosition_sq, hcenter]
  simp

end

end DroppingThreeBodies
