module

public import Dropping3Bodies.EqualMass.Torque
public import Dropping3Bodies.Dynamics.Domain
public import Dropping3Bodies.Geometry.BodyIndex
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-!
The unit-mass Newton acceleration and its pair-torque identity.  This module
states the vector field on all configurations; physical interpretations and
smoothness are restricted to the collision-free domain in a later module.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Inverse-cube distance kernel, totalized at zero by Lean's integer power. -/
def inverseCubeDistance (q : Fin 3 → Point) (i j : Fin 3) : ℝ :=
  dist (q i) (q j) ^ (-3 : ℤ)

/-- Newton acceleration for three unit masses with gravitational constant one. -/
def unitAcceleration (q : Fin 3 → Point) (i : Fin 3) : Point :=
  match i with
  | 0 =>
      inverseCubeDistance q 0 1 • (q 1 - q 0) +
      inverseCubeDistance q 0 2 • (q 2 - q 0)
  | 1 =>
      inverseCubeDistance q 1 0 • (q 0 - q 1) +
      inverseCubeDistance q 1 2 • (q 2 - q 1)
  | _ =>
      inverseCubeDistance q 2 0 • (q 0 - q 2) +
      inverseCubeDistance q 2 1 • (q 1 - q 2)

/-- Newton's first-order phase-space vector field for three unit masses and G=1. -/
def unitNewtonField (z : Phase) : Phase :=
  (z.2, fun i => unitAcceleration z.1 i)

/-- A classical collision-free Newton solution on an open time set. -/
def ClassicalNewtonSolution (z : ℝ → Phase) (I : Set ℝ) : Prop :=
  IsOpen I ∧ ∀ t ∈ I, CollisionFree (z t).1 ∧
    HasDerivAt z (unitNewtonField (z t)) t

/-- D3B-S03; PAPER-20261029 `eq:torque`; force contribution to the pair torque.
    This is the algebraic acceleration identity; interpreting it as `K̇`
    additionally requires a twice differentiable solution of Newton's ODE. -/
theorem unit_pair_torque_acceleration (q : Fin 3 → Point) (i : Fin 3) :
    cross (sideVector q i)
      (unitAcceleration q (cyclicPrev i) - unitAcceleration q (cyclicNext i)) =
      signedDoubleArea q *
        (inverseCubeDistance q (cyclicPrev i) i -
          inverseCubeDistance q (cyclicNext i) i) := by
  fin_cases i <;>
    simp [cyclicNext, cyclicPrev, sideVector, unitAcceleration,
      inverseCubeDistance, signedDoubleArea, cross] <;>
    ring
/-- Newton's cyclic pair torque is the negative area times a positive
    inverse-cube factor and the corresponding squared-side gap. This is the
    configuration-level input for the cooperative side-order system. -/
theorem unit_pair_torque_eq_neg_area_gap
    (q : Fin 3 → Point) (i : Fin 3)
    (hprev : 0 < dist (q (cyclicPrev i)) (q i))
    (hnext : 0 < dist (q (cyclicNext i)) (q i)) :
    cross (sideVector q i)
        (unitAcceleration q (cyclicPrev i) - unitAcceleration q (cyclicNext i)) =
      -signedDoubleArea q *
        inverseCubeGapFactor
          (dist (q (cyclicPrev i)) (q i))
          (dist (q (cyclicNext i)) (q i)) * sideGap q i := by
  rw [unit_pair_torque_acceleration]
  simp only [inverseCubeDistance]
  rw [inverse_cube_gap_factorization hprev hnext]
  have hgap : sideGap q i =
      dist (q (cyclicPrev i)) (q i) ^ 2 -
        dist (q (cyclicNext i)) (q i) ^ 2 := by
    fin_cases i <;>
      simp [sideGap, cyclicPrev, cyclicNext, dist_eq_norm] <;>
      rw [norm_sub_rev]
  rw [hgap]
  ring

end

end DroppingThreeBodies
