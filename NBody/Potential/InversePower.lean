module

public import NBody.Potential.RadialPair
public import PrincipiaThreeBodies.Definitions

@[expose] public section

namespace NBody

noncomputable section

/-- Attractive or repulsive inverse-power potential, with real exponent α.
The convention is V = -½ Σᵢⱼ cᵢⱼ rᵢⱼ^(-α). -/
def inversePowerPotential {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (α : ℝ) (c : SymmetricCouplings ι) (q : Config ι d) : ℝ :=
  -(1 / 2 : ℝ) * ∑ i, ∑ j, if i = j then 0 else
    c.coeff i j * Real.rpow (dist (q i) (q j)) (-α)

/-- Formal inverse-power force expression. Its identity with the negative
potential gradient remains to be proved. -/
def inversePowerForce {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (α : ℝ) (c : SymmetricCouplings ι) (q : Config ι d) (i : ι) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ j, if i = j then 0 else
    (α * c.coeff i j *
      Real.rpow (dist (q i) (q j)) (-α - 2)) • (q j - q i)

end

end NBody
