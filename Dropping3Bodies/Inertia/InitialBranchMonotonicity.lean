module

public import Dropping3Bodies.Inertia.CenterOfMassMoment
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-!
# Q1 monotonicity on the initial noncollinear branch

The pair-sum moment and physical center-of-mass moment conventions follow
`Inertia/CenterOfMassMoment.lean`. This module packages the compact-interval
result as a statement on the complete initial branch, for either orientation.
-/

namespace DroppingThreeBodies

noncomputable section

/-- The pair-sum moment is strictly antitone on the full regular
noncollinear branch issuing from an at-rest state. No first syzygy is assumed
to exist. Either orientation is allowed. -/
theorem generalNewton_pairMomentCurve_strictAntiOn_initialBranch
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (pairMomentCurve m (fun i s => (z s).1 i))
      (BeforeFirstCollinearity z I a) := by
  intro u hu v hv huv
  rcases hv with ⟨hav, hIcc, hnonzero⟩
  have hau : a ≤ u := hu.1
  have hauv : a < v := lt_of_le_of_lt hau huv
  have hdrop := generalNewton_pairMomentCurve_strictDecrease_before_firstCollinearity
    hsol hconn hauv hIcc hm0 hm1 hm2 hG
    (fun s hs => hnonzero s ⟨hs.1, le_of_lt hs.2⟩) hrest
  exact hdrop u ⟨hau, huv⟩

/-- The physical center-of-mass moment has the same strict decrease on the
initial branch, since the pair moment is total mass times this moment. -/
theorem generalNewton_centerOfMassMomentCurve_strictAntiOn_initialBranch
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a : ℝ} (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2)
    (hG : 0 < G) (hrest : ∀ i, (z a).2 i = 0) :
    StrictAntiOn (centerOfMassMomentCurve m (fun i s => (z s).1 i))
      (BeforeFirstCollinearity z I a) := by
  have hpair := generalNewton_pairMomentCurve_strictAntiOn_initialBranch
    hsol hconn hm0 hm1 hm2 hG hrest
  have hM : 0 < totalMass m := totalMass_pos_of_positive m hm0 hm1 hm2
  intro u hu v hv huv
  have hdrop := hpair hu hv huv
  rw [pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
      (fun i s => (z s).1 i) hm0 hm1 hm2 u,
    pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
      (fun i s => (z s).1 i) hm0 hm1 hm2 v] at hdrop
  nlinarith [hM]

end

end DroppingThreeBodies
