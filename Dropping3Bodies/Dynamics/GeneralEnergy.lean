module

public import Dropping3Bodies.Dynamics.GeneralNewton
public import Dropping3Bodies.Dynamics.Energy
public import Dropping3Bodies.Geometry.InertiaCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic

@[expose] public section

/-! Differential and algebraic energy identities for arbitrary masses. -/

namespace DroppingThreeBodies

noncomputable section

/-- Mass-weighted kinetic energy for a three-body velocity configuration. -/
def generalKineticEnergy (m : Fin 3 → ℝ) (v : Fin 3 → Point) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 3, m i * ‖v i‖ ^ 2

/-- Positive Newtonian potential magnitude, with each pair counted once. -/
def generalGravitationalPotential (G : ℝ) (m : Fin 3 → ℝ)
    (q : Fin 3 → Point) : ℝ :=
  G * m 0 * m 1 / dist (q 0) (q 1) +
    (G * m 0 * m 2 / dist (q 0) (q 2) +
      G * m 1 * m 2 / dist (q 1) (q 2))

/-- Pairwise work rate of the positive mass-weighted potential. -/
def generalPotentialRate (G : ℝ) (m : Fin 3 → ℝ)
    (q v : Fin 3 → Point) : ℝ :=
  -(G * m 0 * m 1) * inner ℝ (q 0 - q 1) (v 0 - v 1) *
      inverseCubeDistance q 0 1 +
    (-(G * m 0 * m 2) * inner ℝ (q 0 - q 2) (v 0 - v 2) *
        inverseCubeDistance q 0 2) +
    (-(G * m 1 * m 2) * inner ℝ (q 1 - q 2) (v 1 - v 2) *
        inverseCubeDistance q 1 2)

/-- Pairing the weighted Newton accelerations with the velocities groups by
    unordered pairs and equals the derivative formula for the potential. -/
theorem generalNewton_weighted_work_eq_potentialRate
    (G : ℝ) (m : Fin 3 → ℝ) (q v : Fin 3 → Point) :
    (∑ i : Fin 3, m i * inner ℝ (v i) (generalAcceleration G m q i)) =
      generalPotentialRate G m q v := by
  simp [generalPotentialRate, generalAcceleration, inverseCubeDistance,
    zpow_neg, Fin.sum_univ_succ, dist_comm, real_inner_comm,
    inner_add_right, inner_smul_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm (q 1) (v 0)]
  rw [real_inner_comm (q 0) (v 1)]
  rw [dist_comm (q 1) (q 0)]
  ring_nf

/-- The total mass-weighted internal force vanishes for arbitrary masses. -/
theorem generalNewton_weighted_acceleration_sum_eq_zero
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    ∑ i : Fin 3, m i • generalAcceleration G m q i = 0 := by
  have hkernel (i j : Fin 3) : inverseCubeDistance q i j =
      inverseCubeDistance q j i := by
    simp [inverseCubeDistance, dist_comm]
  ext k
  simp [generalAcceleration, Fin.sum_univ_succ, hkernel]
  ring_nf

/-- The total torque of the mass-weighted internal forces vanishes. -/
def generalTotalTorque (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) : ℝ :=
  ∑ i : Fin 3, m i * cross (q i) (generalAcceleration G m q i)

theorem generalNewton_weighted_totalTorque_eq_zero
    (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    generalTotalTorque G m q = 0 := by
  have hkernel (i j : Fin 3) : inverseCubeDistance q i j =
      inverseCubeDistance q j i := by
    simp [inverseCubeDistance, dist_comm]
  simp [generalTotalTorque, generalAcceleration, Fin.sum_univ_succ,
    cross, hkernel]
  ring_nf

/-- A classical collision-free solution for the general-mass Newton field. -/
def GeneralClassicalNewtonSolution (G : ℝ) (m : Fin 3 → ℝ)
    (z : ℝ → Phase) (I : Set ℝ) : Prop :=
  IsOpen I ∧ ∀ t ∈ I, CollisionFree (z t).1 ∧
    HasDerivAt z (generalNewtonField G m (z t)) t

/-- The packed first-order general Newton equation yields body derivatives. -/
theorem generalNewton_body_vector_derivatives
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (i : Fin 3) (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I) :
    HasDerivAt (fun s => (z s).1 i) ((z t).2 i) t ∧
      HasDerivAt (fun s => (z s).2 i) (generalAcceleration G m (z t).1 i) t := by
  have hphase := (hsol.2 t ht).2
  have hpos : HasDerivAt (fun s => (z s).1) ((generalNewtonField G m (z t)).1) t := by
    simpa using hphase.hasFDerivAt.fst.hasDerivAt
  have hvel : HasDerivAt (fun s => (z s).2) ((generalNewtonField G m (z t)).2) t := by
    simpa using hphase.hasFDerivAt.snd.hasDerivAt
  constructor
  · simpa [generalNewtonField] using (hasDerivAt_pi.1 hpos) i
  · simpa [generalNewtonField] using (hasDerivAt_pi.1 hvel) i

/-- On every compact subinterval of a general classical Newton solution,
    the squared-side rate is interval-integrable. -/
theorem generalNewton_sideSqRate_intervalIntegrable
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {a b : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I)
    (hsegment : Set.uIcc a b ⊆ I) (i : Fin 3) :
    IntervalIntegrable
      (fun τ => 2 * dot2 (sideVector (z τ).1 i) (sideVector (z τ).2 i))
      MeasureTheory.volume a b := by
  have hzcont : ContinuousOn z (Set.uIcc a b) := by
    intro τ hτ
    exact ((hsol.2 τ (hsegment hτ)).2).continuousAt.continuousWithinAt
  exact intervalIntegrable_sideSqRate_of_continuousOn i hzcont.fst hzcont.snd

/-- The integrated squared-side rate equals the endpoint change along a
    general classical Newton solution. -/
theorem generalNewton_sideSq_integral_eq_sub
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {a b : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I)
    (hsegment : Set.uIcc a b ⊆ I) (i : Fin 3) :
    ∫ τ in a..b,
      2 * dot2 (sideVector (z τ).1 i) (sideVector (z τ).2 i) =
      sideSq (z b).1 i - sideSq (z a).1 i := by
  have hderiv : ∀ τ ∈ Set.uIcc a b,
      HasBodyCoordDerivAt (fun j t => (z t).1 j)
        (fun j => (z τ).2 j) τ := by
    intro τ hτ j k
    have hpos := (generalNewton_body_vector_derivatives j hsol
      (hsegment hτ)).1
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := τ) (c := EuclideanSpace.proj k)).clm_apply hpos
  have hint := generalNewton_sideSqRate_intervalIntegrable hsol hsegment i
  exact intervalIntegral_sideSqRate_eq_sub i hderiv hint
/-- Total angular momentum for mass-weighted planar trajectories. -/
def generalAngularMomentumCurve (m : Fin 3 → ℝ)
    (q v : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, m i * cross (q i t) (v i t)

/-- Product-rule derivative of weighted angular momentum on arbitrary
    differentiable planar body curves. -/
theorem hasDerivAt_generalAngularMomentumCurve
    (m : Fin 3 → ℝ) {q v : Fin 3 → ℝ → Point}
    {dq dv : Fin 3 → Point} {t : ℝ}
    (hq : HasBodyCoordDerivAt q dq t) (hv : HasBodyCoordDerivAt v dv t) :
    HasDerivAt (generalAngularMomentumCurve m q v)
      (∑ i : Fin 3, m i * frameAreaRate (q i t) (v i t) (dq i) (dv i)) t := by
  have h0 := HasDerivAt.const_mul (m 0) (hasDerivAt_frameAreaCurve
    (fun k => hq 0 k) (fun k => hv 0 k))
  have h1 := HasDerivAt.const_mul (m 1) (hasDerivAt_frameAreaCurve
    (fun k => hq 1 k) (fun k => hv 1 k))
  have h2 := HasDerivAt.const_mul (m 2) (hasDerivAt_frameAreaCurve
    (fun k => hq 2 k) (fun k => hv 2 k))
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : generalAngularMomentumCurve m q v =ᶠ[nhds t]
      ((fun s => m 0 * frameAreaCurve (q 0) (v 0) s) +
        ((fun s => m 1 * frameAreaCurve (q 1) (v 1) s) +
          (fun s => m 2 * frameAreaCurve (q 2) (v 2) s))) := by
    filter_upwards [] with s
    simp [generalAngularMomentumCurve, frameAreaCurve, Fin.sum_univ_succ]
  simpa [Fin.sum_univ_succ] using hs.congr_of_eventuallyEq hfun

/-- The derivative of weighted angular momentum along Newton curves is the
    total torque of internal forces, hence zero. -/
theorem hasDerivAt_generalAngularMomentumCurve_newton_zero
    {G : ℝ} {m : Fin 3 → ℝ} {q v : Fin 3 → ℝ → Point} {t : ℝ}
    (hq : HasBodyCoordDerivAt q (fun i => v i t) t)
    (hv : HasBodyCoordDerivAt v
      (fun i => generalAcceleration G m (fun j => q j t) i) t) :
    HasDerivAt (generalAngularMomentumCurve m q v) 0 t := by
  have h := hasDerivAt_generalAngularMomentumCurve m hq hv
  have hrate :
      (∑ i : Fin 3, m i *
        frameAreaRate (q i t) (v i t) (v i t)
          (generalAcceleration G m (fun j => q j t) i)) =
        generalTotalTorque G m (fun i => q i t) := by
    simp [frameAreaRate, generalTotalTorque, cross_self]
  have hzero :
      (∑ i : Fin 3, m i *
        frameAreaRate (q i t) (v i t) (v i t)
          (generalAcceleration G m (fun j => q j t) i)) = 0 := by
    rw [hrate]
    exact generalNewton_weighted_totalTorque_eq_zero G m (fun i => q i t)
  exact h.congr_deriv hzero

/-- Packed general Newton solutions provide the coordinate derivatives
    required by the angular-momentum product rule. -/
theorem hasDerivAt_generalAngularMomentumCurve_solution_zero
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I) :
    HasDerivAt (generalAngularMomentumCurve m
      (fun i s => (z s).1 i) (fun i s => (z s).2 i)) 0 t := by
  have hq : HasBodyCoordDerivAt (fun i s => (z s).1 i)
      (fun i => (z t).2 i) t := by
    intro i k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (generalNewton_body_vector_derivatives i hsol ht).1
  have hv : HasBodyCoordDerivAt (fun i s => (z s).2 i)
      (fun i => generalAcceleration G m (z t).1 i) t := by
    intro i k
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj k)).clm_apply
        (generalNewton_body_vector_derivatives i hsol ht).2
  exact hasDerivAt_generalAngularMomentumCurve_newton_zero hq hv

/-- Every general-mass classical solution has constant total angular
    momentum on its preconnected open time domain. -/
theorem generalAngularMomentumCurve_eq_on
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    generalAngularMomentumCurve m (fun i τ => (z τ).1 i)
      (fun i τ => (z τ).2 i) s =
    generalAngularMomentumCurve m (fun i τ => (z τ).1 i)
      (fun i τ => (z τ).2 i) t := by
  apply hsol.1.is_const_of_deriv_eq_zero hconn
  · intro τ hτ
    exact (hasDerivAt_generalAngularMomentumCurve_solution_zero hsol hτ).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [(hasDerivAt_generalAngularMomentumCurve_solution_zero hsol hτ).deriv]
    simp
  · exact hs
  · exact ht

/-- A coordinate of total linear momentum for general masses. -/
def generalMomentumCoordinateCurve (m : Fin 3 → ℝ)
    (v : Fin 3 → ℝ → Point) (k : Fin 2) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, m i * v i t k

/-- A coordinate of the mass-weighted position vector along a curve. -/
def generalPositionCoordinateCurve (m : Fin 3 → ℝ)
    (q : Fin 3 → ℝ → Point) (k : Fin 2) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, m i * q i t k

/-- Product rule for a coordinate of mass-weighted linear momentum. -/
theorem hasDerivAt_generalMomentumCoordinateCurve
    (m : Fin 3 → ℝ) {v : Fin 3 → ℝ → Point} {a : Fin 3 → Point}
    {k : Fin 2} {t : ℝ} (hv : HasBodyCoordDerivAt v a t) :
    HasDerivAt (generalMomentumCoordinateCurve m v k)
      (∑ i : Fin 3, m i * a i k) t := by
  have h0 := HasDerivAt.const_mul (m 0) (hv 0 k)
  have h1 := HasDerivAt.const_mul (m 1) (hv 1 k)
  have h2 := HasDerivAt.const_mul (m 2) (hv 2 k)
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : generalMomentumCoordinateCurve m v k =ᶠ[nhds t]
      ((fun s => m 0 * v 0 s k) +
        ((fun s => m 1 * v 1 s k) + (fun s => m 2 * v 2 s k))) := by
    filter_upwards [] with s
    simp [generalMomentumCoordinateCurve, Fin.sum_univ_succ]
  simpa [Fin.sum_univ_succ] using hs.congr_of_eventuallyEq hfun

/-- At each point of a general-mass solution, the weighted momentum
    coordinate has zero derivative. -/
theorem generalMomentumCoordinateCurve_solution_zero
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I) (k : Fin 2) :
    HasDerivAt
      (generalMomentumCoordinateCurve m (fun i s => (z s).2 i) k) 0 t := by
  have hv : HasBodyCoordDerivAt (fun i s => (z s).2 i)
      (fun i => generalAcceleration G m (z t).1 i) t := by
    intro i j
    simpa [EuclideanSpace.coe_proj] using
      (hasDerivAt_const (x := t) (c := EuclideanSpace.proj j)).clm_apply
        (generalNewton_body_vector_derivatives i hsol ht).2
  have h := hasDerivAt_generalMomentumCoordinateCurve m (k := k) hv
  have hforce := generalNewton_weighted_acceleration_sum_eq_zero G m (z t).1
  have hcoord : (∑ i : Fin 3,
      m i * generalAcceleration G m (z t).1 i k) = 0 := by
    simpa [Fin.sum_univ_succ] using congrArg (fun p : Point => p k) hforce
  rw [hcoord] at h
  exact h

/-- Pair-force cancellation makes every coordinate of weighted momentum
    constant along a general-mass solution. -/
theorem generalMomentumCoordinate_eq_on
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {k : Fin 2}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    generalMomentumCoordinateCurve m (fun i τ => (z τ).2 i) k s =
      generalMomentumCoordinateCurve m (fun i τ => (z τ).2 i) k t := by
  apply hsol.1.is_const_of_deriv_eq_zero hconn
  · intro τ hτ
    exact (generalMomentumCoordinateCurve_solution_zero hsol hτ k).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [(generalMomentumCoordinateCurve_solution_zero hsol hτ k).deriv]
    simp
  · exact hs
  · exact ht

/-- Product rule for one coordinate of the mass-weighted position vector. -/
theorem hasDerivAt_generalPositionCoordinateCurve
    (m : Fin 3 → ℝ) {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point}
    {k : Fin 2} {t : ℝ} (hq : HasBodyCoordDerivAt q v t) :
    HasDerivAt (generalPositionCoordinateCurve m q k)
      (∑ i : Fin 3, m i * v i k) t := by
  have h0 := HasDerivAt.const_mul (m 0) (hq 0 k)
  have h1 := HasDerivAt.const_mul (m 1) (hq 1 k)
  have h2 := HasDerivAt.const_mul (m 2) (hq 2 k)
  have hs := HasDerivAt.add h0 (HasDerivAt.add h1 h2)
  have hfun : generalPositionCoordinateCurve m q k =ᶠ[nhds t]
      ((fun s => m 0 * q 0 s k) +
        ((fun s => m 1 * q 1 s k) + (fun s => m 2 * q 2 s k))) := by
    filter_upwards [] with s
    simp [generalPositionCoordinateCurve, Fin.sum_univ_succ]
  simpa [Fin.sum_univ_succ] using hs.congr_of_eventuallyEq hfun

/-- With initial rest, the weighted center of mass is constant on the
    connected solution domain. -/
theorem generalPositionCoordinate_eq_on_of_initial_rest
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {k : Fin 2}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hrest : ∀ i, (z t₀).2 i = 0)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    generalPositionCoordinateCurve m (fun i τ => (z τ).1 i) k s =
      generalPositionCoordinateCurve m (fun i τ => (z τ).1 i) k t := by
  have hmomentum₀ :
      generalMomentumCoordinateCurve m (fun i τ => (z τ).2 i) k t₀ = 0 := by
    simp [generalMomentumCoordinateCurve, hrest]
  apply hsol.1.is_const_of_deriv_eq_zero hconn
  · intro τ hτ
    have hq : HasBodyCoordDerivAt (fun i u => (z u).1 i)
        (fun i => (z τ).2 i) τ := by
      intro i j
      simpa [EuclideanSpace.coe_proj] using
        (hasDerivAt_const (x := τ) (c := EuclideanSpace.proj j)).clm_apply
          (generalNewton_body_vector_derivatives i hsol hτ).1
    exact (hasDerivAt_generalPositionCoordinateCurve m (k := k) hq).differentiableAt.differentiableWithinAt
  · intro τ hτ
    have hq : HasBodyCoordDerivAt (fun i u => (z u).1 i)
        (fun i => (z τ).2 i) τ := by
      intro i j
      simpa [EuclideanSpace.coe_proj] using
        (hasDerivAt_const (x := τ) (c := EuclideanSpace.proj j)).clm_apply
          (generalNewton_body_vector_derivatives i hsol hτ).1
    have hderiv := hasDerivAt_generalPositionCoordinateCurve m (k := k) hq
    have hP := generalMomentumCoordinate_eq_on (k := k) hsol hconn ht₀ hτ
    have hzero : (∑ i : Fin 3, m i * (z τ).2 i k) = 0 := by
      have hPτ := hP.symm
      simpa [generalMomentumCoordinateCurve] using hPτ.trans hmomentum₀
    rw [hderiv.deriv]
    simpa using hzero
  · exact hs
  · exact ht

/-- Mass-weighted kinetic energy along a velocity curve. -/
def generalKineticEnergyCurve (m : Fin 3 → ℝ)
    (v : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  generalKineticEnergy m (fun i => v i t)

/-- Positive mass-weighted potential along a position curve. -/
def generalPotentialCurve (G : ℝ) (m : Fin 3 → ℝ)
    (q : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  generalGravitationalPotential G m (fun i => q i t)

/-- Mechanical energy along a general-mass phase curve. -/
def generalNewtonianEnergyCurve (G : ℝ) (m : Fin 3 → ℝ)
    (z : ℝ → Phase) (t : ℝ) : ℝ :=
  generalKineticEnergyCurve m (fun i s => (z s).2 i) t -
    generalPotentialCurve G m (fun i s => (z s).1 i) t

/-- The derivative of the mass-weighted kinetic energy curve is total Newton
    work, for arbitrary real mass coefficients. -/
theorem hasDerivAt_generalKineticEnergyCurve
    (m : Fin 3 → ℝ) {v : Fin 3 → ℝ → Point} {a : Fin 3 → Point} {t : ℝ}
    (hv : ∀ i, HasDerivAt (fun s => v i s) (a i) t) :
    HasDerivAt (generalKineticEnergyCurve m v)
      (∑ i : Fin 3, m i * inner ℝ (v i t) (a i)) t := by
  have h := hasDerivAt_massMomentCurve (fun i => m i / 2) hv
  have hrate : massMomentRate (fun i => m i / 2) v a t =
      ∑ i : Fin 3, m i * inner ℝ (v i t) (a i) := by
    simp [massMomentRate, Fin.sum_univ_succ]
    ring
  have hfun : generalKineticEnergyCurve m v =ᶠ[nhds t]
      massMomentCurve (fun i => m i / 2) v := by
    filter_upwards [] with s
    simp [generalKineticEnergyCurve, generalKineticEnergy, massMomentCurve,
      massMoment, Fin.sum_univ_succ]
    ring
  rw [hrate] at h
  exact h.congr_of_eventuallyEq hfun

/-- Differentiate the positive potential with arbitrary pair masses. -/
theorem hasDerivAt_generalPotentialCurve
    (G : ℝ) (m : Fin 3 → ℝ)
    {q : Fin 3 → ℝ → Point} {v : Fin 3 → Point} {t : ℝ}
    (hq : ∀ i, HasDerivAt (fun s => q i s) (v i) t)
    (hsep : ∀ i j, i ≠ j → q i t ≠ q j t) :
    HasDerivAt (generalPotentialCurve G m q)
      (generalPotentialRate G m (fun i => q i t) v) t := by
  have h01 := hasDerivAt_inverseDistanceCurve (hq 0) (hq 1) (hsep 0 1 (by decide))
  have h02 := hasDerivAt_inverseDistanceCurve (hq 0) (hq 2) (hsep 0 2 (by decide))
  have h12 := hasDerivAt_inverseDistanceCurve (hq 1) (hq 2) (hsep 1 2 (by decide))
  have h01' := h01.const_mul (G * m 0 * m 1)
  have h02' := h02.const_mul (G * m 0 * m 2)
  have h12' := h12.const_mul (G * m 1 * m 2)
  have hsum := HasDerivAt.add h01' (HasDerivAt.add h02' h12')
  have hfun : generalPotentialCurve G m q =ᶠ[nhds t]
      (fun s => (G * m 0 * m 1) * (dist (q 0 s) (q 1 s))⁻¹) +
        ((fun s => (G * m 0 * m 2) * (dist (q 0 s) (q 2 s))⁻¹) +
          (fun s => (G * m 1 * m 2) * (dist (q 1 s) (q 2 s))⁻¹)) := by
    filter_upwards [] with s
    simp [generalPotentialCurve, generalGravitationalPotential,
      div_eq_mul_inv]
  have hderiv :
      (G * m 0 * m 1) *
          (-(inner ℝ (q 0 t - q 1 t) (v 0 - v 1)) /
            dist (q 0 t) (q 1 t) ^ 3) +
        ((G * m 0 * m 2) *
            (-(inner ℝ (q 0 t - q 2 t) (v 0 - v 2)) /
              dist (q 0 t) (q 2 t) ^ 3) +
          (G * m 1 * m 2) *
            (-(inner ℝ (q 1 t - q 2 t) (v 1 - v 2)) /
              dist (q 1 t) (q 2 t) ^ 3)) =
      generalPotentialRate G m (fun i => q i t) v := by
    simp [generalPotentialRate, inverseCubeDistance_eq_inv_distance_cube,
      div_eq_mul_inv]
    ring
  have hsum' := hsum.congr_of_eventuallyEq hfun.symm
  exact hsum'.congr_deriv hderiv

/-- Mechanical energy has zero derivative on every regular solution of the
    general-mass Newton field. -/
theorem hasDerivAt_generalNewtonianEnergyCurve_zero
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {t : ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (ht : t ∈ I) :
    HasDerivAt (generalNewtonianEnergyCurve G m z) 0 t := by
  let q : Fin 3 → ℝ → Point := fun i s => (z s).1 i
  let v : Fin 3 → ℝ → Point := fun i s => (z s).2 i
  let acc : Fin 3 → Point := fun i => generalAcceleration G m (z t).1 i
  have hq (i : Fin 3) : HasDerivAt (q i) ((z t).2 i) t := by
    simpa [q] using (generalNewton_body_vector_derivatives i hsol ht).1
  have hv (i : Fin 3) : HasDerivAt (v i) (acc i) t := by
    simpa [v, acc] using (generalNewton_body_vector_derivatives i hsol ht).2
  have hsep (i j : Fin 3) (hij : i ≠ j) : q i t ≠ q j t :=
    (hsol.2 t ht).1 i j hij
  have hkin := hasDerivAt_generalKineticEnergyCurve m hv
  have hpot := hasDerivAt_generalPotentialCurve G m hq hsep
  have hwork := generalNewton_weighted_work_eq_potentialRate G m
    (z t).1 (z t).2
  have haccEq :
      (∑ i : Fin 3, m i * inner ℝ ((z t).2 i) (acc i)) =
        generalPotentialRate G m (z t).1 (z t).2 := by
    simpa [acc] using hwork
  have hzero :
      (∑ i : Fin 3, m i * inner ℝ ((z t).2 i) (acc i)) -
        generalPotentialRate G m (z t).1 (z t).2 = 0 := by
    rw [haccEq]
    ring
  have henergy := (hkin.sub hpot).congr_deriv hzero
  change HasDerivAt
    (generalKineticEnergyCurve m (fun i s => (z s).2 i) -
      generalPotentialCurve G m (fun i s => (z s).1 i)) 0 t
  simpa [q, v] using henergy

/-- General-mass Newtonian energy is constant on a preconnected open
    collision-free solution domain. -/
theorem generalNewtonianEnergyCurve_eq_on
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    generalNewtonianEnergyCurve G m z s = generalNewtonianEnergyCurve G m z t := by
  apply hsol.1.is_const_of_deriv_eq_zero hconn
  · intro τ hτ
    exact (hasDerivAt_generalNewtonianEnergyCurve_zero hsol hτ).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [(hasDerivAt_generalNewtonianEnergyCurve_zero hsol hτ).deriv]
    simp
  · exact hs
  · exact ht

end

end DroppingThreeBodies
