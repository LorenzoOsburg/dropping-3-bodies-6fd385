module

public import Dropping3Bodies.Dynamics.SolutionMomentum
public import Dropping3Bodies.Dynamics.SolutionDerivatives
public import Dropping3Bodies.EqualMass.FrameCalculus

@[expose] public section

set_option maxHeartbeats 500000

namespace DroppingThreeBodies

/-- Position curves of a packed Newton phase-space trajectory. -/
def solutionPositionCurve (z : ℝ → Phase) : Fin 3 → ℝ → Point :=
  fun i t => (z t).1 i

/-- Velocity curves of a packed Newton phase-space trajectory. -/
def solutionVelocityCurve (z : ℝ → Phase) : Fin 3 → ℝ → Point :=
  fun i t => (z t).2 i

/-- Centered initial positions and initial rest imply zero angular momentum
    in every cyclic side frame throughout the classical solution interval. -/
theorem classicalNewton_sideFrame_angularMomentum_eq_zero
    {z : ℝ → Phase} {I : Set ℝ}
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hrest : ∀ i, (z t₀).2 i = 0)
    (hcenter : (z t₀).1 0 + (z t₀).1 1 + (z t₀).1 2 = 0)
    {t : ℝ} (ht : t ∈ I) :
    ∀ i : Fin 3, frameAngularMomentum
      (sideVector (fun b => (z t).1 b) i)
      (sideOffset (fun b => (z t).1 b) i)
      (sideVector (fun b => (z t).2 b) i)
      (sideOffset (fun b => (z t).2 b) i) = 0 := by
  have hqcenter : (z t).1 0 + (z t).1 1 + (z t).1 2 = 0 := by
    ext k
    have hcenter₀ :
        totalPositionCoordinateCurve (solutionPositionCurve z) k t₀ = 0 := by
      simpa [totalPositionCoordinateCurve, solutionPositionCurve,
        Fin.sum_univ_succ, add_assoc] using congrArg (fun p : Point => p k) hcenter
    have hpositions :=
      totalPositionCoordinate_eq_on_classicalNewtonSolution_of_initial_rest
        hsol hconn ht₀ hrest (k := k) (s := t₀) (t := t) ht₀ ht
    calc
      (z t).1 0 k + (z t).1 1 k + (z t).1 2 k =
          totalPositionCoordinateCurve (solutionPositionCurve z) k t := by
            simp [totalPositionCoordinateCurve, solutionPositionCurve,
              Fin.sum_univ_succ, add_assoc]
      _ = totalPositionCoordinateCurve (solutionPositionCurve z) k t₀ := hpositions.symm
      _ = 0 := hcenter₀
  have hvcenter : (z t).2 0 + (z t).2 1 + (z t).2 2 = 0 := by
    ext k
    have hmomentum₀ :
        totalMomentumCoordinateCurve (solutionVelocityCurve z) k t₀ = 0 := by
      simp [totalMomentumCoordinateCurve, solutionVelocityCurve, hrest]
    have hmomentum :=
      totalMomentumCoordinate_eq_on_classicalNewtonSolution
        hsol hconn (k := k) (s := t₀) (t := t) ht₀ ht
    calc
      (z t).2 0 k + (z t).2 1 k + (z t).2 2 k =
          totalMomentumCoordinateCurve (solutionVelocityCurve z) k t := by
            simp [totalMomentumCoordinateCurve, solutionVelocityCurve,
              Fin.sum_univ_succ, add_assoc]
      _ = totalMomentumCoordinateCurve (solutionVelocityCurve z) k t₀ := hmomentum.symm
      _ = 0 := hmomentum₀
  have hL₀ : angularMomentumCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) t₀ = 0 := by
    simp [angularMomentumCurve, totalAngularMomentum, solutionPositionCurve,
      solutionVelocityCurve, hrest, cross]
  have hL := angularMomentum_eq_on_classicalNewtonSolution hsol hconn ht₀ ht
  have hLt : angularMomentumCurve (solutionPositionCurve z)
      (solutionVelocityCurve z) t = 0 := by
    calc
      angularMomentumCurve (solutionPositionCurve z) (solutionVelocityCurve z) t =
          angularMomentumCurve (solutionPositionCurve z) (solutionVelocityCurve z) t₀ := hL.symm
      _ = 0 := hL₀
  intro i
  rw [frameAngularMomentum_eq_total_of_centered
    (fun b => (z t).1 b) (fun b => (z t).2 b) i hqcenter hvcenter]
  simpa [angularMomentumCurve, totalAngularMomentum, solutionPositionCurve, solutionVelocityCurve] using hLt

/-- The actual Newton trajectory satisfies the equal-mass cyclic gap
    derivative identity at every time in the interval, under centered initial
    positions and initial rest. -/
theorem classicalNewton_bodyCurve_gap_derivative_identity
    {z : ℝ → Phase} {I : Set ℝ} (i : Fin 3)
    (hsol : ClassicalNewtonSolution z I) (hconn : IsPreconnected I)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I)
    (hrest : ∀ b, (z t₀).2 b = 0)
    (hcenter : (z t₀).1 0 + (z t₀).1 1 + (z t₀).1 2 = 0) :
    frameAreaCurve (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
        (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ) t *
      deriv (frameGapCurve (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
        (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ)) t -
      frameGapCurve (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
        (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ) t *
      deriv (frameAreaCurve (fun τ => sideVectorCurve (solutionPositionCurve z) i τ)
        (fun τ => sideOffsetCurve (solutionPositionCurve z) i τ)) t =
      -3 * frameMoment
        (sideVector (fun b => (z t).1 b) i)
        (sideOffset (fun b => (z t).1 b) i) *
        framePairRotation (sideVector (fun b => (z t).1 b) i)
          (sideVector (fun b => (z t).2 b) i) := by
  have hbody : HasBodyCoordDerivAt (solutionPositionCurve z)
      (fun b => (z t).2 b) t := by
    intro b k
    exact (classicalNewton_body_coordinate_derivatives b hsol ht).1 k
  have hframe := classicalNewton_sideFrame_angularMomentum_eq_zero
    hsol hconn ht₀ hrest hcenter ht i
  exact bodyCurve_gap_derivative_identity i hbody hframe

end DroppingThreeBodies