module

public import NBody.Potential.RadialPair

@[expose] public section

namespace NBody

noncomputable section

/-- The action of a linear isometry on a particle configuration. -/
def isometryAction {ι : Type*} [Fintype ι] {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (q : Config ι d) : Config ι d := fun i => L (q i)

/-- Invariance of a potential on a domain under every orthogonal action.
This condition alone asserts no translation or momentum symmetry. -/
def IsometryInvariantPotential {ι : Type*} [Fintype ι] {d : ℕ}
    (Ω : Set (Config ι d)) (V : Config ι d → ℝ) : Prop :=
  ∀ L q, q ∈ Ω → isometryAction L q ∈ Ω →
    V (isometryAction L q) = V q

theorem radialPairPotential_isometry_invariant {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (W : RadialPairProfile ι) (q : Config ι d)
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    radialPairPotential W (isometryAction L q) = radialPairPotential W q := by
  unfold radialPairPotential isometryAction
  simp [L.isometry.dist_eq]

end

end NBody
