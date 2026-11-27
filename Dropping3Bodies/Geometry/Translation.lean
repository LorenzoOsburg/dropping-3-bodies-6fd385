module

public import Dropping3Bodies.Basic
public import Dropping3Bodies.EqualMass.SideFrame
public import Mathlib.Tactic

@[expose] public section

/-! Constant translations preserve planar triangle geometry. -/

namespace DroppingThreeBodies

noncomputable section

def translatePoint (c p : Point) : Point := p + c

def translateConfiguration (c : Point) (q : Fin 3 → Point) : Fin 3 → Point :=
  fun i => translatePoint c (q i)

theorem translatePoint_dist (c p q : Point) :
    dist (translatePoint c p) (translatePoint c q) = dist p q := by
  rw [translatePoint, translatePoint, dist_eq_norm, dist_eq_norm]
  congr 1
  abel

theorem signedDoubleArea_translateConfiguration (c : Point) (q : Fin 3 → Point) :
    signedDoubleArea (translateConfiguration c q) = signedDoubleArea q := by
  simp [signedDoubleArea, translateConfiguration, translatePoint, cross]

theorem dist_translateConfiguration (c : Point) (q : Fin 3 → Point) (i j : Fin 3) :
    dist (translateConfiguration c q i) (translateConfiguration c q j) =
      dist (q i) (q j) := by
  exact translatePoint_dist c (q i) (q j)

theorem sideSq_translateConfiguration (c : Point) (q : Fin 3 → Point) (i : Fin 3) :
    sideSq (translateConfiguration c q) i = sideSq q i := by
  rw [sideSq_eq_cyclicNeighborDistance, sideSq_eq_cyclicNeighborDistance,
    dist_translateConfiguration]

end

end DroppingThreeBodies
