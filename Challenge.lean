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

@[expose] public section Model

/-!
# Three bodies released from rest

These model declarations specify the eleven theorems below.
The interval-coverage lemma supplies the witness used to define the maximal trajectory.
Comparator checks the definitions used here against the model used in the proof development.
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
end Model

public section

open DroppingThreeBodies DroppingThreeBodies.CentralForce Set
open scoped Matrix.Norms.Elementwise

variable {κ : Coefficients} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
  {a t : ℝ}

/-- The scalar mass moment about the center of mass strictly decreases on the initial noncollinear branch. -/
theorem PrincipiaThreeBodies.centerOfMassMomentCurve_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (centerOfMassMomentCurve m (fun i u => (z u).1 i))
      (BeforeFirstCollinearity z I a) := by
  sorry

/-- Its time derivative is negative at every branch time strictly after release. -/
theorem PrincipiaThreeBodies.centerOfMassMomentCurve_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) t < 0 := by
  sorry

/-- The derivative of the centered spatial second-moment tensor is symmetric everywhere on the classical solution domain. -/
theorem PrincipiaThreeBodies.centeredSpatialMoment_deriv_symmetric (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (ht : t ∈ I) :
    (deriv (fun u => centeredSpatialMoment m (z u).1) t).transpose =
      deriv (fun u => centeredSpatialMoment m (z u).1) t := by
  sorry

/-- The tensor derivative is negative in every nonzero spatial direction on the initial branch strictly after release. -/
theorem PrincipiaThreeBodies.centeredSpatialMoment_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    matrixQuadratic (deriv (fun u => centeredSpatialMoment m (z u).1) t) w < 0 := by
  sorry

/-- The signed double area, multiplied by the sign of the initial area, strictly decreases on the initial branch. -/
theorem PrincipiaThreeBodies.orientedArea_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (orientedArea z a) (BeforeFirstCollinearity z I a) := by
  sorry

/-- The positively oriented double area has strictly negative time derivative
at every time strictly after release on the initial noncollinear branch. -/
theorem PrincipiaThreeBodies.orientedArea_deriv_neg
    (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i)
    (hκ : κ.Positive)
    (hconn : IsPreconnected I)
    (ha : a ∈ I)
    (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a)
    (hat : a < t) :
    deriv (fun u => orientedArea z a u) t < 0 := by
  sorry

/-- The square root of the absolute double area has negative second derivative at every noncollinear time in the connected solution domain, including release when noncollinear. -/
theorem PrincipiaThreeBodies.sqrtAbsArea_second_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    deriv (deriv (fun u => Real.sqrt |signedDoubleArea (z u).1|)) t < 0 := by
  sorry

/-- The square root of the absolute double area is strictly concave on the initial noncollinear branch. -/
theorem PrincipiaThreeBodies.sqrtAbsArea_strictConcaveOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictConcaveOn ℝ (BeforeFirstCollinearity z I a)
      (fun u => Real.sqrt |signedDoubleArea (z u).1|) := by
  sorry

/-- With C¹ radial coefficients on positive distances, the maximal solution has a nonempty, bounded initial branch with a strictly positive finite supremum. -/
theorem PrincipiaThreeBodies.maximal_initialBranch_endpoint_pos_finite
    {κ : Coefficients} {m : Fin 3 → ℝ} {z₀ : Phase}
    (hm : ∀ i, 0 < m i) (hκpos : κ.Positive) (hκreg : κ.C1)
    (harea : signedDoubleArea z₀.1 ≠ 0) (hrest : ∀ i, z₀.2 i = 0) :
    let S := BeforeFirstCollinearity (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0
    S.Nonempty ∧ BddAbove S ∧ IsLUB S (initialNoncollinearEndpoint κ m z₀) ∧
      0 < initialNoncollinearEndpoint κ m z₀ ∧
      (initialNoncollinearEndpoint κ m z₀ : EReal) < ⊤ := by
  sorry

/-- The scalar moment has negative derivative at a later endpoint when the classical collision-free solution domain contains the entire closed segment and the half-open segment is noncollinear. -/
theorem PrincipiaThreeBodies.centerOfMassMomentCurve_deriv_neg_at_regular_endpoint (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) {T : ℝ} (haT : a < T)
    (hI : Set.Icc a T ⊆ I)
    (harea : ∀ u ∈ Set.Ico a T, signedDoubleArea (z u).1 ≠ 0) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) T < 0 := by
  sorry

/-- For equal positive masses and a common positive inverse-power coupling with 0 < α < 2, the maximal trajectory from scalene noncollinear rest data has a finite first regular syzygy, is collision-free with strict opposite-side order through that time, and has body 0 strictly between bodies 2 and 1 there. -/
theorem PrincipiaThreeBodies.power_q2_subcritical
    (α g m : ℝ) (hα : 0 < α) (hα2 : α < 2) (hg : 0 < g) (hm : 0 < m)
    (q : Fin 3 → Point) (harea : signedDoubleArea q ≠ 0)
    (horder : orderedOppositeSides q) :
    let κ := powerCoefficients α (commonCouplings g)
    let masses : Fin 3 → ℝ := fun _ => m
    let z₀ : Phase := (q, fun _ => 0)
    let z := maximalTrajectory κ masses z₀
    let I := maximalDomain κ masses z₀
    let T := initialNoncollinearEndpoint κ masses z₀
    EqualPowerSolution α g m z I ∧ z 0 = z₀ ∧
      FirstRegularSyzygy z I 0 T ∧
      (∀ t ∈ Icc 0 T, CollisionFree (z t).1 ∧ orderedOppositeSides (z t).1) ∧
      Sbtw ℝ ((z T).1 2) ((z T).1 0) ((z T).1 1) := by
  sorry
