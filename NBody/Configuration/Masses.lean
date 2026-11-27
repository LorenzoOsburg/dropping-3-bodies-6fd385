module

public import NBody.Basic
public import PrincipiaThreeBodies.Definitions

@[expose] public section

namespace NBody

noncomputable section

/-- The linear subspace of configurations centered at the origin for the given
mass vector. -/
def centeredConfigurationSet {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) : Set (Config ι d) := {q | weightedPosition m q = 0}

theorem centerOfMass_eq_zero_iff_weightedPosition_eq_zero
    {ι : Type*} [Fintype ι] {d : ℕ} (m : ι → ℝ) (q : Config ι d)
    (hM : totalMass m ≠ 0) :
    centerOfMass m q = 0 ↔ weightedPosition m q = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun x : EuclideanSpace ℝ (Fin d) => totalMass m • x) h
    simpa [centerOfMass, smul_smul, hM] using h'
  · intro h
    simp [centerOfMass, h]

/-- Kinetic energy, in the positive-mass convention. -/
def kineticEnergy {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (v : Config ι d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, m i * ‖v i‖ ^ 2

/-- Positive magnitude of the Newtonian potential, with each unordered pair
counted by half of the symmetric off-diagonal double sum. -/
def potentialMagnitude {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (G : ℝ) (m : ι → ℝ) (q : Config ι d) : ℝ :=
  (G / 2) * ∑ i, ∑ j, if i = j then 0 else
    m i * m j / dist (q i) (q j)

end

end NBody
