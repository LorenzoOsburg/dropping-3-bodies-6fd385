module

public import PrincipiaThreeBodies.Definitions
import Dropping3Bodies.MainResults.Q2PowerLaw

public section

open DroppingThreeBodies DroppingThreeBodies.CentralForce Set
open scoped Matrix.Norms.Elementwise

variable {κ : Coefficients} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
  {a t : ℝ}

theorem PrincipiaThreeBodies.centerOfMassMomentCurve_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (centerOfMassMomentCurve m (fun i u => (z u).1 i))
      (BeforeFirstCollinearity z I a) := by
  exact DroppingThreeBodies.CentralForce.centerOfMassMomentCurve_strictAntiOn_initialBranch
    hsol hm hκ hconn ha hrest

theorem PrincipiaThreeBodies.centerOfMassMomentCurve_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) t < 0 := by
  exact DroppingThreeBodies.CentralForce.centerOfMassMomentCurve_deriv_neg
    hsol hm hκ hconn ha hrest ht hat

theorem PrincipiaThreeBodies.centeredSpatialMoment_deriv_symmetric (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (ht : t ∈ I) :
    (deriv (fun u => centeredSpatialMoment m (z u).1) t).transpose =
      deriv (fun u => centeredSpatialMoment m (z u).1) t := by
  exact DroppingThreeBodies.CentralForce.centeredSpatialMoment_deriv_symmetric
    hsol hm ht

theorem PrincipiaThreeBodies.centeredSpatialMoment_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (ht : t ∈ BeforeFirstCollinearity z I a) (hat : a < t)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) :
    matrixQuadratic (deriv (fun u => centeredSpatialMoment m (z u).1) t) w < 0 := by
  exact DroppingThreeBodies.CentralForce.centeredSpatialMoment_deriv_neg
    hsol hm hκ hconn ha hrest ht hat w hw

theorem PrincipiaThreeBodies.orientedArea_strictAntiOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (orientedArea z a) (BeforeFirstCollinearity z I a) := by
  exact DroppingThreeBodies.CentralForce.orientedArea_strictAntiOn_initialBranch
    hsol hm hκ hconn ha hrest

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
  exact DroppingThreeBodies.CentralForce.orientedArea_deriv_neg
    hsol hm hκ hconn ha hrest ht hat

theorem PrincipiaThreeBodies.sqrtAbsArea_second_deriv_neg (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (ht : t ∈ I) (hrest : ∀ i, (z a).2 i = 0)
    (harea : signedDoubleArea (z t).1 ≠ 0) :
    deriv (deriv (fun u => Real.sqrt |signedDoubleArea (z u).1|)) t < 0 := by
  exact DroppingThreeBodies.CentralForce.sqrtAbsArea_second_deriv_neg
    hsol hm hκ hconn ha ht hrest harea

theorem PrincipiaThreeBodies.sqrtAbsArea_strictConcaveOn_initialBranch (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) :
    StrictConcaveOn ℝ (BeforeFirstCollinearity z I a)
      (fun u => Real.sqrt |signedDoubleArea (z u).1|) := by
  exact DroppingThreeBodies.CentralForce.sqrtAbsArea_strictConcaveOn_initialBranch
    hsol hm hκ hconn ha hrest

theorem PrincipiaThreeBodies.maximal_initialBranch_endpoint_pos_finite
    {κ : Coefficients} {m : Fin 3 → ℝ} {z₀ : Phase}
    (hm : ∀ i, 0 < m i) (hκpos : κ.Positive) (hκreg : κ.C1)
    (harea : signedDoubleArea z₀.1 ≠ 0) (hrest : ∀ i, z₀.2 i = 0) :
    let S := BeforeFirstCollinearity (maximalTrajectory κ m z₀) (maximalDomain κ m z₀) 0
    S.Nonempty ∧ BddAbove S ∧ IsLUB S (initialNoncollinearEndpoint κ m z₀) ∧
      0 < initialNoncollinearEndpoint κ m z₀ ∧
      (initialNoncollinearEndpoint κ m z₀ : EReal) < ⊤ := by
  exact DroppingThreeBodies.CentralForce.maximal_initialBranch_endpoint_pos_finite
    hm hκpos hκreg harea hrest

theorem PrincipiaThreeBodies.centerOfMassMomentCurve_deriv_neg_at_regular_endpoint (hsol : Solution κ m z I)
    (hm : ∀ i, 0 < m i) (hκ : κ.Positive) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hrest : ∀ i, (z a).2 i = 0) {T : ℝ} (haT : a < T)
    (hI : Set.Icc a T ⊆ I)
    (harea : ∀ u ∈ Set.Ico a T, signedDoubleArea (z u).1 ≠ 0) :
    deriv (centerOfMassMomentCurve m (fun i u => (z u).1 i)) T < 0 := by
  exact DroppingThreeBodies.CentralForce.centerOfMassMomentCurve_deriv_neg_at_regular_endpoint
    hsol hm hκ hconn ha hrest haT hI harea

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
  exact DroppingThreeBodies.CentralForce.power_q2 α g m hα hα2.le hg hm q harea horder
