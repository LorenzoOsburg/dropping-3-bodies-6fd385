module

public import Dropping3Bodies.Basic
public import Dropping3Bodies.EqualMass.SideFrame
public import Mathlib.Tactic

@[expose] public section

/-!
# Reflection in the planar configuration space

The coordinate reflection across the horizontal axis reverses orientation while
preserving Euclidean geometry. These lemmas prepare the negative-orientation
reduction for the equal-mass first-syzygy theorem.
-/

namespace DroppingThreeBodies

noncomputable section

/-- Reflection of a planar point across the horizontal axis. -/
def reflectPoint (p : Point) : Point :=
  EuclideanSpace.single 0 (p 0) + EuclideanSpace.single 1 (-p 1)

@[simp] theorem reflectPoint_apply_zero (p : Point) : reflectPoint p 0 = p 0 := by
  simp [reflectPoint]

@[simp] theorem reflectPoint_apply_one (p : Point) : reflectPoint p 1 = -p 1 := by
  simp [reflectPoint]

theorem reflectPoint_sub (p q : Point) :
    reflectPoint (p - q) = reflectPoint p - reflectPoint q := by
  ext i
  fin_cases i
  · simp [reflectPoint]
  · simp [reflectPoint]
    ring

theorem reflectPoint_add (p q : Point) :
    reflectPoint (p + q) = reflectPoint p + reflectPoint q := by
  ext i
  fin_cases i
  · simp [reflectPoint]
  · simp [reflectPoint]
    ring

theorem reflectPoint_smul (c : ℝ) (p : Point) :
    reflectPoint (c • p) = c • reflectPoint p := by
  ext i
  fin_cases i <;> simp [reflectPoint]

@[simp] theorem reflectPoint_zero : reflectPoint (0 : Point) = 0 := by
  ext i
  fin_cases i <;> simp [reflectPoint]

def reflectPointLinear : Point →ₗ[ℝ] Point where
  toFun := reflectPoint
  map_add' := reflectPoint_add
  map_smul' := reflectPoint_smul

def reflectPointAffine : Point →ᵃ[ℝ] Point := reflectPointLinear.toAffineMap

@[simp] theorem reflectPointAffine_apply (p : Point) :
    reflectPointAffine p = reflectPoint p := rfl

theorem reflectPoint_involutive (p : Point) : reflectPoint (reflectPoint p) = p := by
  ext i
  fin_cases i <;> simp [reflectPoint]

theorem reflectPoint_injective : Function.Injective reflectPoint := by
  intro p q hpq
  calc
    p = reflectPoint (reflectPoint p) := (reflectPoint_involutive p).symm
    _ = reflectPoint (reflectPoint q) := congrArg reflectPoint hpq
    _ = q := reflectPoint_involutive q

theorem reflectPoint_norm_sq (p : Point) :
    ‖reflectPoint p‖ ^ 2 = ‖p‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [reflectPoint]

theorem reflectPoint_norm (p : Point) : ‖reflectPoint p‖ = ‖p‖ := by
  have hsq := reflectPoint_norm_sq p
  have hleft := norm_nonneg (reflectPoint p)
  have hright := norm_nonneg p
  nlinarith

@[simp] theorem reflectPoint_dist (p q : Point) :
    dist (reflectPoint p) (reflectPoint q) = dist p q := by
  rw [dist_eq_norm, dist_eq_norm, ← reflectPoint_sub]
  exact reflectPoint_norm (p - q)

/-- Apply the same reflection to each vertex of a configuration. -/
def reflectConfiguration (q : Fin 3 → Point) : Fin 3 → Point :=
  fun i => reflectPoint (q i)

theorem signedDoubleArea_reflectConfiguration (q : Fin 3 → Point) :
    signedDoubleArea (reflectConfiguration q) = -signedDoubleArea q := by
  simp [signedDoubleArea, reflectConfiguration, cross, reflectPoint]
  ring

theorem dist_reflectConfiguration (q : Fin 3 → Point) (i j : Fin 3) :
    dist (reflectConfiguration q i) (reflectConfiguration q j) = dist (q i) (q j) := by
  exact reflectPoint_dist (q i) (q j)

theorem sideSq_reflectConfiguration (q : Fin 3 → Point) (i : Fin 3) :
    sideSq (reflectConfiguration q) i = sideSq q i := by
  rw [sideSq_eq_cyclicNeighborDistance, sideSq_eq_cyclicNeighborDistance,
    dist_reflectConfiguration]

end

end DroppingThreeBodies

