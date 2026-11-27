module

public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

namespace NBody

noncomputable section

/-- McGehee polar variables for a homogeneous attractive potential: radius,
normalized shape, scaled radial velocity, and tangential shape velocity. -/
structure McGeheeState (E : Type*) where
  radius : ℝ
  shape : E
  radialVelocity : ℝ
  shapeVelocity : E

/-- The rescaled McGehee vector field on shapes where `U` and its tangential
gradient are regular. Binary-collision shapes must be excluded by the caller. -/
def mcGeheeField {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (U : E → ℝ) (gradT : E → E) (x : McGeheeState E) :
    McGeheeState E :=
  { radius := x.radius * x.radialVelocity
    shape := x.shapeVelocity
    radialVelocity := α / 2 * x.radialVelocity ^ 2 +
      ‖x.shapeVelocity‖ ^ 2 - α * U x.shape
    shapeVelocity := gradT x.shape +
      (α / 2 - 1) • (x.radialVelocity • x.shapeVelocity) -
        ‖x.shapeVelocity‖ ^ 2 • x.shape }

/-- The algebraic constraint surface for normalized shapes and tangent shape
velocities. -/
def McGeheeConstraint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : McGeheeState E) : Prop :=
  ‖x.shape‖ = 1 ∧ inner ℝ x.shape x.shapeVelocity = 0

/-- On the collision boundary, the rescaled radius has zero derivative. -/
theorem mcGehee_collisionBoundary_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (U : E → ℝ) (gradT : E → E) (x : McGeheeState E)
    (hr : x.radius = 0) : (mcGeheeField α U gradT x).radius = 0 := by
  simp [mcGeheeField, hr]

/-- On the collision boundary, the energy relation reduces the McGehee radial
equation to `(1 - α/2) ‖w‖²`. The sign therefore changes at `α = 2`. -/
theorem mcGehee_radialVelocity_eq_boundary_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (U : E → ℝ) (gradT : E → E) (x : McGeheeState E)
    (henergy : (x.radialVelocity ^ 2 + ‖x.shapeVelocity‖ ^ 2) / 2 =
      U x.shape) :
    (mcGeheeField α U gradT x).radialVelocity =
      (1 - α / 2) * ‖x.shapeVelocity‖ ^ 2 := by
  simp only [mcGeheeField]
  rw [← henergy]
  ring

theorem mcGehee_boundary_radialVelocity_nonneg_of_alpha_lt_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α : ℝ} (_hα0 : 0 < α) (hα2 : α < 2)
    (U : E → ℝ) (gradT : E → E) (x : McGeheeState E)
    (henergy : (x.radialVelocity ^ 2 + ‖x.shapeVelocity‖ ^ 2) / 2 =
      U x.shape) :
    0 ≤ (mcGeheeField α U gradT x).radialVelocity := by
  rw [mcGehee_radialVelocity_eq_boundary_energy α U gradT x henergy]
  exact mul_nonneg (by linarith) (sq_nonneg ‖x.shapeVelocity‖)

end

end NBody
