module

public import Dropping3Bodies.Inertia.JacobiRiccati
public import Dropping3Bodies.Dynamics.GeneralReflectionSymmetry
public import Dropping3Bodies.Geometry.Inertia
public import Dropping3Bodies.Inertia.Jacobi
public import Mathlib.Tactic
public import PrincipiaThreeBodies.Definitions

@[expose] public section

/-!
# Physical moment of inertia about the center of mass

The center-of-mass moment is translation-invariant and coincides with the
Jacobi moment. This module makes the physical Q1 quantity explicit without
requiring the center of mass to be at the origin.
-/

namespace DroppingThreeBodies

noncomputable section

/-- The pair-sum moment used in Richard Montgomery's MathOverflow Question 1
    (https://mathoverflow.net/questions/13933/dropping-three-bodies), evaluated
    along a position curve. -/
def pairMomentCurve (m : Fin 3 → ℝ)
    (q : Fin 3 → ℝ → Point) (t : ℝ) : ℝ :=
  pairMoment m (fun i => q i t)

theorem centerOfMassMoment_eq_jacobiMoment
    (m : Fin 3 → ℝ) (q : Fin 3 → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) :
    centerOfMassMoment m q = jacobiMoment m q := by
  have hMpos : 0 < totalMass m := totalMass_pos_of_positive m hm0 hm1 hm2
  have hM : totalMass m ≠ 0 := ne_of_gt hMpos
  have hpairJ := pairMoment_eq_totalMass_mul_jacobiMoment m q hm0 hm1 hm2
  have hpairM := pairMoment_eq_totalMass_mul_massMoment_sub_weightedPosition_sq m q
  unfold centerOfMassMoment
  field_simp [hM]
  linarith

theorem centerOfMassMomentCurve_eq_jacobiMomentCurve
    (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (t : ℝ) :
    centerOfMassMomentCurve m q t = jacobiMomentCurve m q t := by
  exact centerOfMassMoment_eq_jacobiMoment m (fun i => q i t) hm0 hm1 hm2

/-- The pair-sum inertia in MathOverflow Question 1 is total mass times the
    physical center-of-mass moment. -/
theorem pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve
    (m : Fin 3 → ℝ) (q : Fin 3 → ℝ → Point)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (t : ℝ) :
    pairMomentCurve m q t = totalMass m * centerOfMassMomentCurve m q t := by
  change pairMoment m (fun i => q i t) =
    totalMass m * centerOfMassMoment m (fun i => q i t)
  rw [pairMoment_eq_totalMass_mul_jacobiMoment m (fun i => q i t) hm0 hm1 hm2,
    ← centerOfMassMoment_eq_jacobiMoment m (fun i => q i t) hm0 hm1 hm2]

theorem generalNewton_centerOfMassMomentCurve_strictDecrease_to_endpoint
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea₀ : 0 < signedDoubleArea (z a).1)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    ∀ t ∈ Set.Ico a T,
      centerOfMassMomentCurve m (fun i s => (z s).1 i) T <
        centerOfMassMomentCurve m (fun i s => (z s).1 i) t := by
  have hJ := generalNewton_jacobiMomentCurve_strictDecrease_to_endpoint
    hsol hconn haT hIcc hm0 hm1 hm2 hG harea₀ hareaPre hrest
  intro t ht
  rw [centerOfMassMomentCurve_eq_jacobiMomentCurve m
      (fun i s => (z s).1 i) hm0 hm1 hm2 T,
    centerOfMassMomentCurve_eq_jacobiMomentCurve m
      (fun i s => (z s).1 i) hm0 hm1 hm2 t]
  exact hJ t ht

/-- Question 1's pair-sum inertia is strictly decreasing on every compact
    positive-area segment issuing from an at-rest initial state. The interval
    endpoint is interior to the solution domain; no regularity assumption at
    the first syzygy endpoint is needed. -/
theorem generalNewton_pairMomentCurve_strictDecrease_to_endpoint
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (harea₀ : 0 < signedDoubleArea (z a).1)
    (hareaPre : ∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1)
    (hrest : ∀ i, (z a).2 i = 0) :
    ∀ t ∈ Set.Ico a T,
      pairMomentCurve m (fun i s => (z s).1 i) T <
        pairMomentCurve m (fun i s => (z s).1 i) t := by
  have hcenter := generalNewton_centerOfMassMomentCurve_strictDecrease_to_endpoint
    hsol hconn haT hIcc hm0 hm1 hm2 hG harea₀ hareaPre hrest
  have hMpos : 0 < totalMass m := totalMass_pos_of_positive m hm0 hm1 hm2
  intro t ht
  rw [pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
      (fun i s => (z s).1 i) hm0 hm1 hm2 T,
    pairMomentCurve_eq_totalMass_mul_centerOfMassMomentCurve m
      (fun i s => (z s).1 i) hm0 hm1 hm2 t]
  exact mul_lt_mul_of_pos_left (hcenter t ht) hMpos

/-- On a compact regular Newton segment, nonvanishing signed area has one
    orientation throughout the pre-endpoint interval. The endpoint itself may
    be collinear, as at a first syzygy. -/
theorem generalNewton_signedArea_hasConstantSign_before_endpoint
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I)
    {a T : ℝ} (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hnonzero : ∀ t ∈ Set.Ico a T, signedDoubleArea (z t).1 ≠ 0) :
    (∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1) ∨
      (∀ t ∈ Set.Ico a T, signedDoubleArea (z t).1 < 0) := by
  let A : ℝ → ℝ := fun t => signedDoubleArea (z t).1
  have hzcont : ContinuousOn z (Set.Icc a T) := by
    intro t ht
    exact ((hsol.2 t (hIcc ht)).2).continuousAt.continuousWithinAt
  have hSignedArea : Continuous (fun q : Fin 3 → Point => signedDoubleArea q) := by
    change Continuous (fun q : Fin 3 → Point =>
      (q 1 0 - q 0 0) * (q 2 1 - q 0 1) -
        (q 1 1 - q 0 1) * (q 2 0 - q 0 0))
    fun_prop
  have hAcont : ContinuousOn A (Set.Icc a T) := by
    have hqcont : ContinuousOn (fun t => (z t).1) (Set.Icc a T) := hzcont.fst
    change ContinuousOn (fun t => signedDoubleArea ((fun s => (z s).1) t)) (Set.Icc a T)
    exact hSignedArea.comp_continuousOn hqcont
  have haIco : a ∈ Set.Ico a T := ⟨le_rfl, haT⟩
  rcases lt_or_gt_of_ne (hnonzero a haIco) with hA0neg | hA0pos
  · right
    intro t ht
    rcases lt_or_gt_of_ne (hnonzero t ht) with hAtneg | hAtpos
    · exact hAtneg
    · have hAcont' : ContinuousOn A (Set.Icc a t) := hAcont.mono fun s hs =>
        ⟨hs.1, le_trans hs.2 (le_of_lt ht.2)⟩
      have hzero : 0 ∈ Set.Icc (A a) (A t) :=
        ⟨le_of_lt hA0neg, le_of_lt hAtpos⟩
      obtain ⟨s, hs, hAs⟩ :=
        (intermediate_value_Icc ht.1 hAcont') hzero
      have hsIco : s ∈ Set.Ico a T :=
        ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      exact False.elim ((hnonzero s hsIco) hAs)
  · left
    intro t ht
    rcases lt_or_gt_of_ne (hnonzero t ht) with hAtneg | hAtpos
    · have hAcont' : ContinuousOn A (Set.Icc a t) := hAcont.mono fun s hs =>
        ⟨hs.1, le_trans hs.2 (le_of_lt ht.2)⟩
      have hzero : 0 ∈ Set.Icc (A t) (A a) :=
        ⟨le_of_lt hAtneg, le_of_lt hA0pos⟩
      obtain ⟨s, hs, hAs⟩ :=
        (intermediate_value_Icc' ht.1 hAcont') hzero
      have hsIco : s ∈ Set.Ico a T :=
        ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      exact False.elim ((hnonzero s hsIco) hAs)
    · exact hAtpos
/-- The pair-moment curve is unchanged by reflecting the whole solution. -/
theorem pairMomentCurve_reflectGeneralPhase
    (m : Fin 3 → ℝ) (z : ℝ → Phase) (t : ℝ) :
    pairMomentCurve m (fun i s => (reflectGeneralPhase (z s)).1 i) t =
      pairMomentCurve m (fun i s => (z s).1 i) t := by
  simp [pairMomentCurve, pairMoment, reflectGeneralPhase, reflectConfiguration]

/-- Question 1 applies with either orientation of the noncollinear branch.
    For a negative-area branch reflect the entire general-mass Newton solution;
    this preserves the pair-moment and turns the area positive. -/
theorem generalNewton_pairMomentCurve_strictDecrease_to_endpoint_eitherOrientation
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hareaSign : (∀ t ∈ Set.Ico a T, 0 < signedDoubleArea (z t).1) ∨
      (∀ t ∈ Set.Ico a T, signedDoubleArea (z t).1 < 0))
    (hrest : ∀ i, (z a).2 i = 0) :
    ∀ t ∈ Set.Ico a T,
      pairMomentCurve m (fun i s => (z s).1 i) T <
        pairMomentCurve m (fun i s => (z s).1 i) t := by
  rcases hareaSign with hpos | hneg
  · exact generalNewton_pairMomentCurve_strictDecrease_to_endpoint
      hsol hconn haT hIcc hm0 hm1 hm2 hG (hpos a ⟨le_rfl, haT⟩)
      (fun t ht => hpos t ht) hrest
  · have hsol' := generalClassicalNewtonSolution_reflect hsol
    have hrest' : ∀ i, (reflectGeneralPhase (z a)).2 i = 0 := by
      intro i
      simpa [reflectGeneralPhase, reflectConfiguration] using
        congrArg reflectPoint (hrest i)
    have harea₀ : 0 < signedDoubleArea (reflectGeneralPhase (z a)).1 := by
      rw [show (reflectGeneralPhase (z a)).1 = reflectConfiguration (z a).1 by rfl,
        signedDoubleArea_reflectConfiguration]
      exact neg_pos.mpr (hneg a ⟨le_rfl, haT⟩)
    have hareaPre : ∀ t ∈ Set.Ico a T,
        0 < signedDoubleArea (reflectGeneralPhase (z t)).1 := by
      intro t ht
      rw [show (reflectGeneralPhase (z t)).1 = reflectConfiguration (z t).1 by rfl,
        signedDoubleArea_reflectConfiguration]
      exact neg_pos.mpr (hneg t ht)
    have hdrop := generalNewton_pairMomentCurve_strictDecrease_to_endpoint
      hsol' hconn haT hIcc hm0 hm1 hm2 hG harea₀ hareaPre hrest'
    intro t ht
    calc
      pairMomentCurve m (fun i s => (z s).1 i) T =
          pairMomentCurve m (fun i s => (reflectGeneralPhase (z s)).1 i) T :=
        (pairMomentCurve_reflectGeneralPhase m z T).symm
      _ < pairMomentCurve m (fun i s => (reflectGeneralPhase (z s)).1 i) t :=
        hdrop t ht
      _ = pairMomentCurve m (fun i s => (z s).1 i) t :=
        pairMomentCurve_reflectGeneralPhase m z t


/-- Question 1's pair-sum inertia decreases before a first collinear time
    whenever the solution is regular through each compact endpoint and the
    triangle has not yet become collinear. No sign convention is required:
    continuity fixes the orientation, and reflection handles its negative. -/
theorem generalNewton_pairMomentCurve_strictDecrease_before_firstCollinearity
    {G : ℝ} {m : Fin 3 → ℝ} {z : ℝ → Phase} {I : Set ℝ}
    (hsol : GeneralClassicalNewtonSolution G m z I) (hconn : IsPreconnected I)
    {a T : ℝ} (haT : a < T) (hIcc : Set.Icc a T ⊆ I)
    (hm0 : 0 < m 0) (hm1 : 0 < m 1) (hm2 : 0 < m 2) (hG : 0 < G)
    (hnonzero : ∀ t ∈ Set.Ico a T, signedDoubleArea (z t).1 ≠ 0)
    (hrest : ∀ i, (z a).2 i = 0) :
    ∀ t ∈ Set.Ico a T,
      pairMomentCurve m (fun i s => (z s).1 i) T <
        pairMomentCurve m (fun i s => (z s).1 i) t := by
  have hsign := generalNewton_signedArea_hasConstantSign_before_endpoint
    hsol haT hIcc hnonzero
  exact generalNewton_pairMomentCurve_strictDecrease_to_endpoint_eitherOrientation
    hsol hconn haT hIcc hm0 hm1 hm2 hG hsign hrest

end

end DroppingThreeBodies
