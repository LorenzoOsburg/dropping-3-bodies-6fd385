module

public import Dropping3Bodies.Inertia.CentralForceContraction
public import Dropping3Bodies.Inertia.CentralForceMaximal
public import NBody.Potential.InversePowerGradient
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-! Attractive inverse-power force instances of the abstract contraction
theorem, and exact compatibility with the preserved Newtonian definitions.
The potential-gradient identity is not a premise of any result here. -/

namespace DroppingThreeBodies.CentralForce
noncomputable section

theorem powerCoefficients_positive {α : ℝ} (hα : 0 < α)
    {g : NBody.SymmetricCouplings (Fin 3)}
    (hg : ∀ i j, i ≠ j → 0 < g.coeff i j) : (powerCoefficients α g).Positive := by
  intro i j hij r hr
  exact mul_pos (mul_pos hα (hg i j hij)) (Real.rpow_pos_of_pos hr _)

theorem powerCoefficients_C1 (α : ℝ) (g : NBody.SymmetricCouplings (Fin 3)) :
    (powerCoefficients α g).C1 := by
  intro i j _ r hr
  change ContDiffAt ℝ 1 (fun s => α * g.coeff i j * Real.rpow s (-α - 2)) r
  exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hr.ne')

/-- The existing NBody expression is force, rather than acceleration. -/
theorem power_acceleration_eq_inversePowerForce (α : ℝ)
    (g : NBody.SymmetricCouplings (Fin 3)) (m : Fin 3 → ℝ)
    (q : Fin 3 → Point) (i : Fin 3) :
    acceleration (powerCoefficients α g) m q i =
      (m i)⁻¹ • NBody.inversePowerForce α g q i := by
  unfold acceleration NBody.inversePowerForce
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : j = i
  · simp [hij]
  · simp only [if_neg hij, if_neg (Ne.symm hij), smul_smul]
    congr 1
    simp [weight, powerCoefficients, div_eq_mul_inv, mul_comm]

/-- Acceleration is the negative particle gradient divided by the target mass.
The algebraic identity holds for all real exponents; attraction requires the
separate positive-parameter assumptions used in the contraction theorems. -/
theorem power_acceleration_eq_neg_gradient (α : ℝ)
    (g : NBody.SymmetricCouplings (Fin 3)) (m : Fin 3 → ℝ)
    {q : Fin 3 → Point} (hq : NBody.CollisionFree q) (i : Fin 3) :
    acceleration (powerCoefficients α g) m q i =
      (m i)⁻¹ • (-gradient
        (fun x => NBody.inversePowerPotential α g (Function.update q i x)) (q i)) := by
  rw [power_acceleration_eq_inversePowerForce,
    NBody.inversePowerForce_eq_neg_gradient α g hq i]

/-- Concrete contraction and area conclusions with only power-law parameters. -/
theorem power_contraction {α : ℝ} {g : NBody.SymmetricCouplings (Fin 3)}
    {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {a : ℝ}
    (hsol : Solution (powerCoefficients α g) m z I) (hα : 0 < α)
    (hg : ∀ i j, i ≠ j → 0 < g.coeff i j) (hm : ∀ i, 0 < m i)
    (hconn : IsPreconnected I) (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (centerOfMassMomentCurve m (fun i t => (z t).1 i))
        (BeforeFirstCollinearity z I a) ∧
      StrictAntiOn (orientedArea z a) (BeforeFirstCollinearity z I a) ∧
      StrictConcaveOn ℝ (BeforeFirstCollinearity z I a)
        (fun t => Real.sqrt |signedDoubleArea (z t).1|) :=
  ⟨centerOfMassMomentCurve_strictAntiOn_initialBranch hsol hm
      (powerCoefficients_positive hα hg) hconn ha hrest,
    orientedArea_strictAntiOn_initialBranch hsol hm
      (powerCoefficients_positive hα hg) hconn ha hrest,
    sqrtAbsArea_strictConcaveOn_initialBranch hsol hm
      (powerCoefficients_positive hα hg) hconn ha hrest⟩

theorem power_maximal_initialBranch_endpoint_pos_finite
    {α : ℝ} {g : NBody.SymmetricCouplings (Fin 3)} {m : Fin 3 → ℝ} {z₀ : Phase}
    (hα : 0 < α) (hg : ∀ i j, i ≠ j → 0 < g.coeff i j)
    (hm : ∀ i, 0 < m i) (harea : signedDoubleArea z₀.1 ≠ 0)
    (hrest : ∀ i, z₀.2 i = 0) :
    let κ := powerCoefficients α g
    let S := BeforeFirstCollinearity (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0
    S.Nonempty ∧ BddAbove S ∧ IsLUB S (initialNoncollinearEndpoint κ m z₀) ∧
      0 < initialNoncollinearEndpoint κ m z₀ ∧
      (initialNoncollinearEndpoint κ m z₀ : EReal) < ⊤ :=
  maximal_initialBranch_endpoint_pos_finite hm (powerCoefficients_positive hα hg)
    (powerCoefficients_C1 α g) harea hrest

/-- Strict square-root area curvature for every attractive real power law,
at every noncollinear time of the connected solution released from rest. -/
theorem power_sqrtAbsArea_second_deriv_neg
    {α : ℝ} {g : NBody.SymmetricCouplings (Fin 3)}
    {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ} {a t : ℝ}
    (hsol : Solution (powerCoefficients α g) m z I) (hα : 0 < α)
    (hg : ∀ i j, i ≠ j → 0 < g.coeff i j) (hm : ∀ i, 0 < m i)
    (hconn : IsPreconnected I) (ha : a ∈ I) (ht : t ∈ I)
    (hrest : ∀ i, (z a).2 i = 0) (harea : signedDoubleArea (z t).1 ≠ 0) :
    deriv (deriv (fun u => Real.sqrt |signedDoubleArea (z u).1|)) t < 0 :=
  sqrtAbsArea_second_deriv_neg hsol hm (powerCoefficients_positive hα hg)
    hconn ha ht hrest harea

def newtonCouplings (G : ℝ) (m : Fin 3 → ℝ) : NBody.SymmetricCouplings (Fin 3) where
  coeff i j := if i = j then 0 else G * m i * m j
  symmetric i j := by
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_neg hij, if_neg (Ne.symm hij)]
      ring
  diagonal_zero i := by simp

theorem newtonCouplings_positive {G : ℝ} {m : Fin 3 → ℝ}
    (hG : 0 < G) (hm : ∀ i, 0 < m i) (i j : Fin 3) (hij : i ≠ j) :
    0 < (newtonCouplings G m).coeff i j := by
  simp only [newtonCouplings, if_neg hij]
  exact mul_pos (mul_pos hG (hm i)) (hm j)

theorem power_newton_weight (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (i j : Fin 3) (hij : i ≠ j) :
    weight (powerCoefficients 1 (newtonCouplings G m)) q i j =
      G * m i * m j * inverseCubeDistance q i j := by
  change 1 * (if i = j then 0 else G * m i * m j) *
    Real.rpow (dist (q i) (q j)) (-1 - 2) = _
  have hr : Real.rpow (dist (q i) (q j)) ((-3 : ℤ) : ℝ) =
      dist (q i) (q j) ^ (-3 : ℤ) := Real.rpow_intCast _ _
  rw [if_neg hij, show (-1 - 2 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, hr]
  simp [inverseCubeDistance]

theorem power_newton_acceleration (G : ℝ) (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (q : Fin 3 → Point) (i : Fin 3) :
    acceleration (powerCoefficients 1 (newtonCouplings G m)) m q i =
      generalAcceleration G m q i := by
  unfold acceleration generalAcceleration
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : j = i
  · simp [hij]
  · simp only [if_neg hij]
    rw [power_newton_weight G m q i j (Ne.symm hij)]
    congr 1
    field_simp [(hm i).ne']

theorem power_newton_vectorField (G : ℝ) (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (z : Phase) :
    vectorField (powerCoefficients 1 (newtonCouplings G m)) m z = generalNewtonField G m z := by
  apply Prod.ext
  · rfl
  · funext i
    exact power_newton_acceleration G m hm z.1 i

theorem power_newton_forceMatrix (G : ℝ) (m : Fin 3 → ℝ) (q : Fin 3 → Point) :
    forceMatrix (powerCoefficients 1 (newtonCouplings G m)) m q = jacobiForceMatrix G m q := by
  ext a b
  simp only [forceMatrix, weightedForceMatrix, jacobiForceMatrix,
    power_newton_weight G m q 0 1 (by decide),
    power_newton_weight G m q 0 2 (by decide),
    power_newton_weight G m q 1 2 (by decide)]
  ring

theorem power_newton_maximalDomain (G : ℝ) (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (z₀ : Phase) : maximalDomain (powerCoefficients 1 (newtonCouplings G m)) m z₀ =
      generalMaximalNewtonDomain G m z₀ := by
  have hf : vectorField (powerCoefficients 1 (newtonCouplings G m)) m = NBody.vectorField G m :=
    funext fun z => power_newton_vectorField G m hm z
  unfold maximalDomain generalMaximalNewtonDomain
  rw [hf]

theorem power_newton_maximalTrajectory (G : ℝ) (m : Fin 3 → ℝ) (hm : ∀ i, 0 < m i)
    (z₀ : Phase) : maximalTrajectory (powerCoefficients 1 (newtonCouplings G m)) m z₀ =
      generalMaximalNewtonTrajectory G m z₀ := by
  have hf : vectorField (powerCoefficients 1 (newtonCouplings G m)) m = NBody.vectorField G m :=
    funext fun z => power_newton_vectorField G m hm z
  unfold maximalTrajectory generalMaximalNewtonTrajectory
  rw [hf]

theorem power_newton_initialNoncollinearEndpoint (G : ℝ) (m : Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (z₀ : Phase) :
    initialNoncollinearEndpoint (powerCoefficients 1 (newtonCouplings G m)) m z₀ =
      maximalInitialNoncollinearEndpoint G m z₀ := by
  unfold initialNoncollinearEndpoint maximalInitialNoncollinearEndpoint
  rw [power_newton_maximalDomain G m hm z₀, power_newton_maximalTrajectory G m hm z₀]

end
end DroppingThreeBodies.CentralForce
