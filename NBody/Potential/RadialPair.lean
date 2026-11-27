module

public import NBody.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace NBody

noncomputable section

/-- Pair radial profiles, symmetric in the particle labels. -/
structure RadialPairProfile (ι : Type*) where
  value : ι → ι → ℝ → ℝ
  symmetric : ∀ i j r, value i j r = value j i r

/-- Pairwise radial potential, with each unordered pair counted once. -/
def radialPairPotential {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (W : RadialPairProfile ι) (q : Config ι d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, if i = j then 0 else
    W.value i j (dist (q i) (q j))

/-- Formal central-force expression for a differentiable radial profile. Its
identity with the negative potential gradient remains to be proved. -/
def radialPairForce {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (W : RadialPairProfile ι) (q : Config ι d) (i : ι) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ j, if i = j then 0 else
    (deriv (W.value i j) (dist (q i) (q j)) /
      dist (q i) (q j)) • (q j - q i)

end

end NBody
