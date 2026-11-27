module

public import NBody.Basic

@[expose] public section

namespace NBody

/-- Uniform positive scaling of every particle position about the origin. -/
def scaleConfiguration {ι : Type*} [Fintype ι] {d : ℕ}
    (r : ℝ) (q : Config ι d) : Config ι d := fun i => r • q i

/-- Homogeneity of degree -α on a domain invariant under positive scaling. -/
def HomogeneousPotential {ι : Type*} [Fintype ι] {d : ℕ}
    (Ω : Set (Config ι d)) (α : ℝ) (V : Config ι d → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ q, q ∈ Ω →
    scaleConfiguration r q ∈ Ω ∧
      V (scaleConfiguration r q) = Real.rpow r (-α) * V q

end NBody
