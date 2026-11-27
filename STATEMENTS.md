# Advertised statements

The Lean namespace `PrincipiaThreeBodies` advertises ten Q1 declarations and
one Q2 declaration. The nine original Q1 declarations came from
`DroppingThreeBodies.CentralForce` at
`0b5950ffbea5024171b3c5f26972b5b8e5f2ea13`. The new Q1 declaration
`orientedArea_deriv_neg` is derived in the submission copy of
`Dropping3Bodies/Inertia/CentralForceContraction.lean` using lemmas from
that checkpoint. The original Q2 declaration is
`DroppingThreeBodies.CentralForce.power_q2` at
`40164c309e448b6cae1a67542dc8be97bb17377f`, the combined snapshot used for
the proof library.

## Full Lean signatures

Implicit variables and namespace imports are included so the signature
block shows the same scope as Challenge and Solution.

```lean
namespace PrincipiaThreeBodies

open DroppingThreeBodies DroppingThreeBodies.CentralForce Set
open scoped Matrix.Norms.Elementwise

variable {κ : Coefficients} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
  {a t : ℝ}

theorem centerOfMassMomentCurve_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (centerOfMassMomentCurve m (fun i u => (z u).1 i))
      (BeforeFirstCollinearity z I a)

theorem centerOfMassMomentCurve_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) t < 0

theorem centeredSpatialMoment_deriv_symmetric (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (ht : t ∈ I) :
    (deriv (fun u => centeredSpatialMoment m (z u).1) t).transpose =
      deriv (fun u => centeredSpatialMoment m (z u).1) t

theorem centeredSpatialMoment_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    matrixQuadratic (deriv (fun u => centeredSpatialMoment m (z u).1) t) w < 0

theorem orientedArea_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (orientedArea z a) (BeforeFirstCollinearity z I a)

theorem orientedArea_deriv_neg
    (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i)
    (hκ : κ.Positive)
    (hconn : IsPreconnected I)
    (ha : a ∈ I)
    (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a)
    (hat : a < t) :
    deriv (fun u => orientedArea z a u) t < 0

theorem sqrtAbsArea_second_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    deriv (deriv (fun u => Real.sqrt |signedDoubleArea (z u).1|)) t < 0

theorem sqrtAbsArea_strictConcaveOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictConcaveOn ℝ (BeforeFirstCollinearity z I a)
      (fun u => Real.sqrt |signedDoubleArea (z u).1|)

theorem maximal_initialBranch_endpoint_pos_finite
    {κ : Coefficients} {m : Fin 3 → ℝ} {z₀ : Phase}
    (hm : ∀ i, 0 < m i) (hκpos : κ.Positive) (hκreg : κ.C1)
    (harea : signedDoubleArea z₀.1 ≠ 0) (hrest : ∀ i, z₀.2 i = 0) :
    let S := BeforeFirstCollinearity (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0
    S.Nonempty ∧ BddAbove S ∧ IsLUB S (initialNoncollinearEndpoint κ m z₀) ∧
      0 < initialNoncollinearEndpoint κ m z₀ ∧
      (initialNoncollinearEndpoint κ m z₀ : EReal) < ⊤

theorem centerOfMassMomentCurve_deriv_neg_at_regular_endpoint (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) {T : ℝ} (haT : a < T)
    (hI : Set.Icc a T ⊆ I)
    (harea : ∀ u ∈ Set.Ico a T, signedDoubleArea (z u).1 ≠ 0) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) T < 0

theorem power_q2_subcritical
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
      Sbtw ℝ ((z T).1 2) ((z T).1 0) ((z T).1 1)

end PrincipiaThreeBodies
```

## Q1 assumptions, interpretations, and dependencies

Throughout, `m` assigns a mass to each of three bodies in
`EuclideanSpace ℝ (Fin 2)`. The structure `Coefficients` requires that a pair
have the same radial coefficient in either direction. Its `Positive`
predicate is strict positivity for all positive distances and distinct
bodies. A `Solution` has an open time domain, collision-free positions there,
and a phase derivative given by velocity and acceleration. Acceleration is
the sum of the displacement toward each other body times its pair
coefficient divided by the target mass.

The branch `BeforeFirstCollinearity z I a` comprises times `t ≥ a` for
which the full closed segment `[a,t]` lies in `I` and has nonzero signed
double area throughout. The scalar moment is the mass moment about the
instantaneous center of mass. It equals the pair-sum moment divided by the
positive total mass under the hypotheses. `orientedArea z a` flips the sign
for the entire curve if the initial signed double area is negative.

| Declaration | Assumptions and interpretation | Statement dependencies beyond the force and phase model |
| --- | --- | --- |
| `centerOfMassMomentCurve_strictAntiOn_initialBranch` | Classical solution on a preconnected domain, positive masses, positive coefficients, and rest at `a ∈ I`. The centered scalar moment strictly decreases on the branch, including comparisons to release. | Centered scalar moment, noncollinear branch, `StrictAntiOn` |
| `centerOfMassMomentCurve_deriv_neg` | Same assumptions with branch membership and `a < t`. The scalar derivative is strictly negative at `t`. | Centered scalar moment, noncollinear branch, `deriv` |
| `centeredSpatialMoment_deriv_symmetric` | Classical solution, positive masses, and `t ∈ I`. The tensor derivative is symmetric. | Centered second-moment matrix, transpose, `deriv` |
| `centeredSpatialMoment_deriv_neg` | Same assumptions as the scalar derivative theorem, with any nonzero real two-vector `w`. The derivative's quadratic form is strictly negative on `w`. | Centered second-moment matrix, matrix quadratic form, noncollinear branch, `deriv` |
| `orientedArea_strictAntiOn_initialBranch` | Same assumptions as scalar strict decrease. The double area in the fixed initial orientation strictly decreases on the branch. | Oriented double area, noncollinear branch, `StrictAntiOn` |
| `orientedArea_deriv_neg` | Same assumptions as the scalar derivative theorem, including branch membership and `a < t`. The double area in the fixed initial orientation has strictly negative derivative at `t`. The release velocity gives zero derivative at `a`. | Oriented double area, noncollinear branch, `deriv` |
| `sqrtAbsArea_second_deriv_neg` | Classical solution, positive masses and coefficients, preconnected time domain, `a,t ∈ I`, rest at `a`, and nonzero double area at `t`. The second derivative is negative at `t`. This includes noncollinear release. | Double area, absolute value, `Real.sqrt`, nested `deriv` |
| `sqrtAbsArea_strictConcaveOn_initialBranch` | Same assumptions as scalar strict decrease. The square root of absolute double area is strictly concave on the branch. | Double area, noncollinear branch, `Real.sqrt`, `StrictConcaveOn` |
| `maximal_initialBranch_endpoint_pos_finite` | Positive masses and coefficients, `ContDiffAt ℝ 1` for each off-diagonal coefficient at positive distances, and noncollinear rest data at time zero. The branch is nonempty and bounded above with a strictly positive finite least upper bound. | Maximal domain and trajectory, branch and its supremum, `IsLUB`, `EReal` |
| `centerOfMassMomentCurve_deriv_neg_at_regular_endpoint` | Same solution, force, domain and rest assumptions as scalar strict decrease. Additionally `a < T`, `[a,T] ⊆ I`, and every time of `[a,T)` is noncollinear. The scalar derivative remains negative at `T`. | Centered scalar moment, double area, closed and half-open intervals, `deriv` |

Nine Q1 solution declarations apply the corresponding theorem in
`Dropping3Bodies/Inertia/CentralForceContraction.lean`. The endpoint supremum
declaration applies the theorem in
`Dropping3Bodies/Inertia/CentralForceMaximal.lean`. Their proof-only
dependencies include mass-normalized Jacobi coordinates, the weighted force
matrix, the matrix Riccati equation, derivative and matrix comparison lemmas,
the initial-branch tangent bound, and local ODE existence and uniqueness.
The oriented-area derivative proof uses `initialBranch_eq` to pass to the
abstract Jacobi branch, `System.riccati_trace_neg_of_rest` for the trace
sign, and `orientedDet_eq`, `System.orientedDet_eq_abs`, and
`areaScale_pos` for positivity of the oriented area. It applies the fixed
initial sign to `signedDoubleArea_hasDerivAt` to obtain the physical
derivative formula before taking the product of the two signs.

The Q1 finiteness result concerns the initial branch supremum and leaves its
regularity and collinearity open. The scalar endpoint theorem
provides a derivative sign when regularity through the endpoint is given.

## Q2 assumptions, interpretation, and dependencies

`power_q2_subcritical` uses the common mass `m > 0`, common pair coupling
`g > 0`, and exponent `0 < α < 2`. The pair potential is
`-g r^(-α)`, with radial force coefficient `α g r^(-α-2)`. The initial
phase is `(q, fun _ => 0)`. The initial double area is nonzero, and
`orderedOppositeSides` requires the positive strict chain
`dist(q 0,q 1) < dist(q 2,q 0) < dist(q 1,q 2)`.

The maximal domain is the union of all open classical collision-free intervals
through the initial phase at time zero. The trajectory evaluates a chosen
interval witness at each time in that union. Local uniqueness ensures the
representatives agree on overlaps. `T` is the real supremum of the initial
noncollinear branch. `FirstRegularSyzygy` requires `0 < T`, `[0,T] ⊆ I`,
zero area at `T`, nonzero area on `[0,T)`, and collision freedom at `T`.
The theorem includes the classical equations and initial condition, collision
freedom and the same strict distance order on `[0,T]`, and Mathlib's strict
betweenness predicate `Sbtw ℝ` with body 0 in the middle.

For a scalene triangle, the three distinct opposite-side lengths determine a
unique labeling by decreasing length of the sides opposite bodies 0, 1, and
2. Any permutation of the labels commutes with the equal-mass, common-coupling
field because it permutes the summands of each identical pair law. The
permutation also carries the rest phase and the regular domains to their
relabelings. The proof library records these geometry facts as
`dist_permuteConfiguration` and
`signedDoubleArea_permuteConfiguration_eq_zero_iff`. A relabeling preserves
distances and the condition of zero double area,
and takes the strict betweenness conclusion back to the original labels.
Thus body 0 represents the body opposite the longest initial side.

Statement dependencies are the shared central-force and maximal-trajectory
model, `powerCoefficients`, `commonCouplings`, `EqualPowerSolution`,
`FirstRegularSyzygy`, `orderedOppositeSides`, and Mathlib's `Sbtw`.
The solution uses `Dropping3Bodies/MainResults/Q2PowerLaw.lean` with
`hα2.le`. Its proof-only dependencies include the equal-mass torque and
side-gap equations, the cooperative sign argument, energy and uniform
separation estimates, regular ODE continuation, and the geometric
betweenness result. Critical-exponent lemmas are in the imported proof
closure of the original `α ≤ 2` theorem.

## Shared definitions

The problem-specific declarations in `PrincipiaThreeBodies/Definitions.lean`
retain their original names and meanings. The coverage lemma and its
`Classical.choose` construction are included to preserve the precise
maximal-union trajectory. Challenge declares the matching model locally
with Mathlib-only imports. See [the source map](SOURCE-MAP.md) for exact
definition provenance.
