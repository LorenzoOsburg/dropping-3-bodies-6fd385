module

public import Dropping3Bodies.Dynamics.ConservationCalculus
public import Dropping3Bodies.Dynamics.SolutionDerivatives

@[expose] public section

set_option maxHeartbeats 500000

namespace DroppingThreeBodies

/-- Total linear momentum is constant on a preconnected open interval of a
    classical unit-mass Newton solution. -/
theorem totalMomentumCoordinate_eq_on_classicalNewtonSolution
    {z : ℝ → Phase} {I : Set ℝ} {k : Fin 2}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    totalMomentumCoordinateCurve (fun i τ => (z τ).2 i) k s =
      totalMomentumCoordinateCurve (fun i τ => (z τ).2 i) k t := by
  apply totalMomentumCoordinate_eq_on_of_zero_derivative hsol.1 hconn
  · intro x hx
    exact (hasDerivAt_totalMomentumCoordinateCurve_newton_zero
      (q := fun i _ => (z x).1 i)
      (fun i j => (classicalNewton_body_coordinate_derivatives i hsol hx).2 j)).differentiableAt.differentiableWithinAt
  · intro x hx
    exact hasDerivAt_totalMomentumCoordinateCurve_newton_zero
      (q := fun i _ => (z x).1 i)
      (fun i j => (classicalNewton_body_coordinate_derivatives i hsol hx).2 j)
  · exact hs
  · exact ht

/-- If a classical Newton solution is initially at rest, each coordinate of
    the sum of the three positions is constant on its connected open interval.
    This is center-of-mass motion in the unit-mass case. -/
theorem totalPositionCoordinate_eq_on_classicalNewtonSolution_of_initial_rest
    {z : ℝ → Phase} {I : Set ℝ} {k : Fin 2}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hrest : ∀ i, (z t₀).2 i = 0)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    totalPositionCoordinateCurve (fun i τ => (z τ).1 i) k s =
      totalPositionCoordinateCurve (fun i τ => (z τ).1 i) k t := by
  have hmomentum₀ :
      totalMomentumCoordinateCurve (fun i τ => (z τ).2 i) k t₀ = 0 := by
    simp [totalMomentumCoordinateCurve, hrest]
  apply totalPositionCoordinate_eq_on_of_totalMomentum_zero hsol.1 hconn
  · intro x hx i j
    exact (classicalNewton_body_coordinate_derivatives i hsol hx).1 j
  · intro x hx
    calc
      (∑ i : Fin 3, (z x).2 i k) =
          totalMomentumCoordinateCurve (fun i τ => (z τ).2 i) k x := by
            simp [totalMomentumCoordinateCurve]
      _ = totalMomentumCoordinateCurve (fun i τ => (z τ).2 i) k t₀ :=
          (totalMomentumCoordinate_eq_on_classicalNewtonSolution hsol hconn ht₀ hx).symm
      _ = 0 := hmomentum₀
  · exact hs
  · exact ht

end DroppingThreeBodies