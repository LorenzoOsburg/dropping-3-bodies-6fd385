module

public import NBody.Solution
public import NBody.ODE.Solution

@[expose] public section

namespace NBody

open Filter
open scoped Topology

/-- A configuration has a binary collision; labels are required to be
distinct. -/
def HasBinaryCollision {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (q : Config ι d) : Prop := ∃ i j, i ≠ j ∧ q i = q j

/-- A classical trajectory on an interval with a finite right endpoint.
The endpoint itself is not in the classical solution domain. -/
structure FiniteRightSolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (a T : ℝ) where
  left_lt_right : a < T
  trajectory : ℝ → E
  solution : SolutionOn Ω X trajectory (Set.Ioo a T)

/-- A finite position limit with a binary collision at the endpoint. No phase
limit is required; velocities or momenta may diverge. -/
def HasCollidingPositionLimit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (z : ℝ → Phase ι d) (T : ℝ) : Prop :=
  ∃ qT : Config ι d,
    Tendsto (fun t => (z t).1) (nhdsWithin T (Set.Iio T)) (𝓝 qT) ∧
      HasBinaryCollision qT

/-- Every sufficiently late time window contains arbitrarily close pairs.
This is the correct negation target for a uniform pair-separation bound at a
finite right endpoint. -/
def NearEncounterOn {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (z : ℝ → Phase ι d) (a T : ℝ) : Prop :=
  ∀ t₀, a ≤ t₀ → t₀ < T → ∀ ε, 0 < ε →
    ∃ t, t₀ < t ∧ t < T ∧ ∃ i j, i ≠ j ∧
      dist ((z t).1 i) ((z t).1 j) < ε

/-- A uniform lower bound on all pair distances along a left-endpoint solution
segment. -/
def UniformlyPairSeparatedOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (z : ℝ → Phase ι d) (a T δ : ℝ) : Prop :=
  0 < δ ∧ ∀ t ∈ Set.Ioo a T, ∀ i j, i ≠ j →
    δ ≤ dist ((z t).1 i) ((z t).1 j)

theorem not_nearEncounterOn_of_uniformlyPairSeparated
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    {z : ℝ → Phase ι d} {a T δ : ℝ} (haT : a < T)
    (hsep : UniformlyPairSeparatedOn z a T δ) : ¬ NearEncounterOn z a T := by
  intro hnear
  let t₀ := (a + T) / 2
  have hat₀ : a ≤ t₀ := by dsimp [t₀]; linarith
  have ht₀T : t₀ < T := by dsimp [t₀]; linarith
  obtain ⟨t, ht₀t, htT, i, j, hij, hdist⟩ := hnear t₀ hat₀ ht₀T δ hsep.1
  have hdist' := hsep.2 t ⟨by linarith [hat₀, ht₀t], htT⟩ i j hij
  linarith

/-- A finite-endpoint noncollision singularity is a maximal regular solution
whose positions do not have a finite colliding limit. It is not defined merely
by absence of collisions at times strictly before the endpoint. -/
def NonCollisionSingularity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (G : ℝ) (m : ι → ℝ) (z : ℝ → Phase ι d) (a T : ℝ) : Prop :=
  a < T ∧ ClassicalSolution G m z (Set.Ioo a T) ∧
    ¬ HasCollidingPositionLimit z T

end NBody
