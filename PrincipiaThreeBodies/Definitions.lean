module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# Three-body statement definitions

This module contains the model definitions used by Solution and the proof development.
Challenge states the same model locally so it can be checked with Mathlib alone.
The interval-coverage lemma supplies the witness used in the maximal trajectory
definition. The source map records where each declaration originated.
-/

noncomputable section

namespace NBody

/-- Position or velocity configuration of a finite particle family. -/
abbrev Config (ι : Type*) [Fintype ι] (d : ℕ) := ι → EuclideanSpace ℝ (Fin d)

/-- First-order position/velocity phase space. -/
abbrev Phase (ι : Type*) [Fintype ι] (d : ℕ) := Config ι d × Config ι d

/-- Pairwise distinct positions. -/
def CollisionFree {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (q : Config ι d) : Prop := ∀ i j, i ≠ j → q i ≠ q j

/-- The regular phase domain of the gravitational vector field. -/
def regularPhaseSet (ι : Type*) [Fintype ι] [DecidableEq ι] (d : ℕ) : Set (Phase ι d) :=
  {z | CollisionFree z.1}

/-- Total mass of a finite particle family. -/
def totalMass {ι : Type*} [Fintype ι] (m : ι → ℝ) : ℝ := ∑ i, m i

/-- Mass-weighted position sum (the center of mass before normalization). -/
def weightedPosition {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (q : Config ι d) : EuclideanSpace ℝ (Fin d) :=
  ∑ i, m i • q i

/-- Center of mass when the total mass is nonzero. -/
def centerOfMass {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → ℝ) (q : Config ι d) : EuclideanSpace ℝ (Fin d) :=
  (totalMass m)⁻¹ • weightedPosition m q

/-- A classical integral curve of an autonomous vector field on a prescribed
state domain, restricted to an open time domain. -/
def SolutionOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (X : E → E) (z : ℝ → E) (I : Set ℝ) : Prop :=
  IsOpen I ∧ ∀ t ∈ I, z t ∈ Ω ∧ HasDerivAt z (X (z t)) t

/-- A local solution interval through fixed initial data. -/
structure InitialIntervalWitness {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (x₀ : E) (a : ℝ) where
  left : ℝ
  right : ℝ
  trajectory : ℝ → E
  left_lt : left < a
  lt_right : a < right
  initial : trajectory a = x₀
  solution : SolutionOn Ω X trajectory (Set.Ioo left right)

/-- The union of all open intervals carrying a solution with the same initial
state. -/
def maximalUnionDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (X : E → E) (x₀ : E) (a : ℝ) : Set ℝ :=
  ⋃₀ {s : Set ℝ | ∃ w : InitialIntervalWitness Ω X x₀ a,
    s = Set.Ioo w.left w.right}

/-- Every time in the maximal union belongs to an interval with a solution witness. -/
theorem maximalUnionDomain_covered {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (x₀ : E) (a t : ℝ)
    (ht : t ∈ maximalUnionDomain Ω X x₀ a) :
    ∃ w : InitialIntervalWitness Ω X x₀ a, t ∈ Set.Ioo w.left w.right := by
  rcases Set.mem_sUnion.mp ht with ⟨s, hs, ht⟩
  rcases hs with ⟨w, rfl⟩
  exact ⟨w, ht⟩

/-- Choose an interval and a solution through the initial data whose domain contains the given time. -/
noncomputable def maximalChosenWitness {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (x₀ : E) (a t : ℝ)
    (ht : t ∈ maximalUnionDomain Ω X x₀ a) : InitialIntervalWitness Ω X x₀ a :=
  Classical.choose (maximalUnionDomain_covered Ω X x₀ a t ht)

/-- Evaluate a chosen regular solution at each time in the maximal union. Outside the union, return the initial state. -/
noncomputable def maximalUnionTrajectory {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Ω : Set E) (X : E → E) (x₀ : E) (a t : ℝ) : E := by
  classical
  exact if ht : t ∈ maximalUnionDomain Ω X x₀ a then
    (maximalChosenWitness Ω X x₀ a t ht).trajectory t
  else x₀

/-- Symmetric real interaction coefficients independent of the inertial masses. -/
structure SymmetricCouplings (ι : Type*) where
  coeff : ι → ι → ℝ
  symmetric : ∀ i j, coeff i j = coeff j i
  diagonal_zero : ∀ i, coeff i i = 0

end NBody

namespace DroppingThreeBodies

/-- Planar position or velocity vector. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The oriented determinant of two planar vectors. -/
def cross (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Twice the signed area of the triangle with vertices `q 0`, `q 1`, `q 2`. -/
def signedDoubleArea (q : Fin 3 → Point) : ℝ :=
  cross (q 1 - q 0) (q 2 - q 0)

/-- The mass-weighted moment about the origin. -/
def massMoment (m : Fin 3 → ℝ) (q : Fin 3 → Point) : ℝ :=
  ∑ i : Fin 3, m i * ‖q i‖ ^ 2

/-- A configuration has no binary collision. -/
def CollisionFree (q : Fin 3 → Point) : Prop :=
  ∀ i j, i ≠ j → q i ≠ q j

/-- Configuration and velocity pairs form the phase space. -/
abbrev Phase := (Fin 3 → Point) × (Fin 3 → Point)

/-- The mass-weighted position vector. -/
def weightedPosition (m : Fin 3 → ℝ) (q : Fin 3 → Point) : Point :=
  ∑ i : Fin 3, (m i) • q i

/-- The total mass. -/
def totalMass (m : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, m i

/-- Mass moment about the instantaneous center of mass, written as the
    parallel-axis identity. -/
def centerOfMassMoment (m : Fin 3 → ℝ) (q : Fin 3 → Point) : ℝ :=
  massMoment m q - ‖weightedPosition m q‖ ^ 2 / totalMass m

/-- The scalar moment about the center of mass along a time-dependent configuration. -/
def centerOfMassMomentCurve (m : Fin 3 → ℝ)
    (q : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  centerOfMassMoment m (fun i => q i t)

/-- Quadratic form of a two-by-two real matrix on a coefficient vector. -/
def matrixQuadratic (K : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, w i * ∑ j : Fin 2, K i j * w j

/-- Mass-weighted spatial second moment about the instantaneous center of mass. -/
def centeredSpatialMoment (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    Matrix (Fin 2) (Fin 2) ℝ := fun r s =>
  ∑ i : Fin 3, m i * (q i - NBody.centerOfMass m q) r *
    (q i - NBody.centerOfMass m q) s

/-- Times up to which the entire segment from the initial time remains in the
solution domain and noncollinear. The closed-interval condition also keeps
the endpoint inside the domain; a singular endpoint is not included. -/
def BeforeFirstCollinearity (z : ℝ → Phase) (I : Set ℝ) (a : ℝ) : Set ℝ :=
  {t | a ≤ t ∧ Set.Icc a t ⊆ I ∧
    ∀ s ∈ Set.Icc a t, signedDoubleArea (z s).1 ≠ 0}

/-- A regular first syzygy on the interval beginning at `a`. -/
def FirstRegularSyzygy (z : ℝ → Phase) (I : Set ℝ) (a T : ℝ) : Prop :=
  a < T ∧ Set.Icc a T ⊆ I ∧
    signedDoubleArea (z T).1 = 0 ∧
    (∀ t ∈ Set.Ico a T, signedDoubleArea (z t).1 ≠ 0) ∧
    CollisionFree (z T).1

end DroppingThreeBodies

namespace DroppingThreeBodies.CentralForce

/-- The same radial coefficient is used for the two directed forces of a pair.
Values at nonpositive distances and on the diagonal do not enter a regular
solution. -/
structure Coefficients where
  value : Fin 3 → Fin 3 → ℝ → ℝ
  symmetric : ∀ i j r, value i j r = value j i r

/-- Every off-diagonal radial coefficient is positive at positive separations. -/
def Coefficients.Positive (κ : Coefficients) : Prop :=
  ∀ i j, i ≠ j → ∀ r, 0 < r → 0 < κ.value i j r

/-- Each off-diagonal coefficient is continuously differentiable near every positive separation. -/
def Coefficients.C1 (κ : Coefficients) : Prop :=
  ∀ i j, i ≠ j → ∀ r, 0 < r → ContDiffAt ℝ 1 (κ.value i j) r

/-- Pair coefficient evaluated at the physical distance. -/
def weight (κ : Coefficients) (q : Fin 3 → Point) (i j : Fin 3) : ℝ :=
  κ.value i j (dist (q i) (q j))

/-- Physical force divided by the target body's inertial mass. -/
def acceleration (κ : Coefficients) (m : Fin 3 → ℝ)
    (q : Fin 3 → Point) (i : Fin 3) : Point :=
  ∑ j, if j = i then 0 else (weight κ q i j / m i) • (q j - q i)

/-- The phase derivative is the velocity together with the physical acceleration of each body. -/
def vectorField (κ : Coefficients) (m : Fin 3 → ℝ) (z : Phase) : Phase :=
  (z.2, fun i => acceleration κ m z.1 i)

/-- Classical solutions of the central-force field on the collision-free phase set. -/
abbrev Solution (κ : Coefficients) (m : Fin 3 → ℝ)
    (z : ℝ → Phase) (I : Set ℝ) : Prop :=
  NBody.SolutionOn (NBody.regularPhaseSet (Fin 3) 2) (vectorField κ m) z I

/-- Signed double area after fixing the initial orientation. -/
def orientedArea (z : ℝ → Phase) (a t : ℝ) : ℝ :=
  if signedDoubleArea (z a).1 < 0 then -signedDoubleArea (z t).1
  else signedDoubleArea (z t).1

/-- The union of collision-free classical solution intervals through the initial phase at time zero. -/
def maximalDomain (κ : Coefficients) (m : Fin 3 → ℝ) (z₀ : Phase) : Set ℝ :=
  NBody.maximalUnionDomain (NBody.regularPhaseSet (Fin 3) 2) (vectorField κ m) z₀ 0

/-- The trajectory selected from the regular solutions through the initial phase at time zero. -/
def maximalTrajectory (κ : Coefficients) (m : Fin 3 → ℝ) (z₀ : Phase) : ℝ → Phase :=
  NBody.maximalUnionTrajectory (NBody.regularPhaseSet (Fin 3) 2) (vectorField κ m) z₀ 0

/-- The endpoint is the supremum of the initial noncollinear branch, not of
the full maximal solution domain. -/
def initialNoncollinearEndpoint (κ : Coefficients) (m : Fin 3 → ℝ) (z₀ : Phase) : ℝ :=
  sSup (BeforeFirstCollinearity (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0)

/-- Radial coefficient of the pair force for the potential with exponent α and coupling g. -/
def powerCoefficients (α : ℝ) (g : NBody.SymmetricCouplings (Fin 3)) : Coefficients where
  value i j r := α * g.coeff i j * Real.rpow r (-α - 2)
  symmetric i j r := by rw [g.symmetric i j]

/-- Each unordered pair has the same physical potential coefficient. -/
def commonCouplings (g : ℝ) : NBody.SymmetricCouplings (Fin 3) where
  coeff i j := if i = j then 0 else g
  symmetric i j := by
    by_cases h : i = j
    · subst j
      rfl
    · exact (ite_eq_right h).trans (ite_eq_right (Ne.symm h)).symm
  diagonal_zero i := by simp

/-- The classical equations for three equal masses and the pair potential
`-g r^(-α)` on each of the three unordered pairs. -/
abbrev EqualPowerSolution (α g m : ℝ) (z : ℝ → Phase) (I : Set ℝ) : Prop :=
  Solution (powerCoefficients α (commonCouplings g)) (fun _ => m) z I

/-- Fixed opposite-side labeling, with the shortest side joining bodies 0 and 1. -/
def orderedOppositeSides (q : Fin 3 → Point) : Prop :=
  0 < dist (q 0) (q 1) ∧ dist (q 0) (q 1) < dist (q 2) (q 0) ∧
    dist (q 2) (q 0) < dist (q 1) (q 2)

end DroppingThreeBodies.CentralForce

end
