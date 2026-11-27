module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-!
# Basic objects for the planar Dropping Three Bodies problem

The current project is a formalization scaffold.  The analytical theorem
statements and proof milestones are recorded in `docs/formalization-roadmap.md`.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Montgomery's pair-sum moment. -/
def pairMoment (m : Fin 3 → ℝ) (q : Fin 3 → Point) : ℝ :=
  m 0 * m 1 * dist (q 0) (q 1) ^ 2 +
  m 1 * m 2 * dist (q 1) (q 2) ^ 2 +
  m 0 * m 2 * dist (q 0) (q 2) ^ 2

/-- Admissible rest data: positive point masses at distinct noncollinear points. -/
structure InitialData where
  mass : Fin 3 → ℝ
  position : Fin 3 → Point
  positive_mass : ∀ i, 0 < mass i
  pairwise_distinct : ∀ i j, i ≠ j → position i ≠ position j
  noncollinear : signedDoubleArea position ≠ 0

/-- Initial zero velocities, kept separate to make the rest condition explicit. -/
def initialVelocity (_data : InitialData) : Fin 3 → Point := fun _ => 0

end

end DroppingThreeBodies
