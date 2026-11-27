module

public import Dropping3Bodies.Dynamics.CommonMassMaximalFlow
public import Dropping3Bodies.MainResults.CommonMassClassificationTransport
public import Dropping3Bodies.MainResults.EqualMassClassification
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The exhaustive side-order classification for equal masses and zero
velocities, transported to the actual maximal common-mass flow. -/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 1000000

/-- Full three-case classification for equal masses `μ>0` and gravity `G>0`.
The common-mass domain is exactly the union of all regular solution intervals;
first event times, homothetic collapse scales, and maximal right endpoints are
rescaled by `1 / sqrt (G*μ)`. Position and collinearity limits are preserved. -/
theorem commonMass_equalMass_maximal_sideOrder_classification
    (G μ : ℝ) (hG : 0 < G) (hμ : 0 < μ)
    (q : Fin 3 → Point) (hcf : CollisionFree q)
    (harea : signedDoubleArea q ≠ 0) :
    (commonMassNewtonUnionDomain G μ
      (q, fun _ : Fin 3 => (0 : Point)) = commonMassMaximalNewtonDomain G μ
        (q, fun _ : Fin 3 => (0 : Point))) ∧
    GeneralClassicalNewtonSolution G (fun _ : Fin 3 => μ)
      (commonMassMaximalNewtonTrajectory G μ
        (q, fun _ : Fin 3 => (0 : Point)))
      (commonMassMaximalNewtonDomain G μ
        (q, fun _ : Fin 3 => (0 : Point))) ∧
    ((∃ i T, T ∈ commonMassMaximalNewtonDomain G μ
        (q, fun _ : Fin 3 => (0 : Point)) ∧ 0 < T ∧
      FirstRegularSyzygy
        (commonMassMaximalNewtonTrajectory G μ
          (q, fun _ : Fin 3 => (0 : Point)))
        (commonMassMaximalNewtonDomain G μ
          (q, fun _ : Fin 3 => (0 : Point))) 0 T ∧
      Sbtw ℝ
        ((commonMassMaximalNewtonTrajectory G μ
          (q, fun _ : Fin 3 => (0 : Point)) T).1 (cyclicPrev i))
        ((commonMassMaximalNewtonTrajectory G μ
          (q, fun _ : Fin 3 => (0 : Point)) T).1 i)
        ((commonMassMaximalNewtonTrajectory G μ
          (q, fun _ : Fin 3 => (0 : Point)) T).1 (cyclicNext i))) ∨
    (∃ (K : ℝ), let T := homotheticCollapseTime K
      0 < T ∧
      (∀ t, 0 ≤ t → (t ∈ commonMassMaximalNewtonDomain G μ
        (q, fun _ : Fin 3 => (0 : Point)) ↔ t < T)) ∧
      (∀ t, 0 ≤ t → t < T → signedDoubleArea
        (commonMassMaximalNewtonTrajectory G μ
          (q, fun _ : Fin 3 => (0 : Point)) t).1 ≠ 0) ∧
      (∀ i j : Fin 3, Tendsto
        (fun t => dist ((commonMassMaximalNewtonTrajectory G μ
          (q, fun _ : Fin 3 => (0 : Point)) t).1 i)
          ((commonMassMaximalNewtonTrajectory G μ
            (q, fun _ : Fin 3 => (0 : Point)) t).1 j))
        (𝓝[<] T) (𝓝 0))) ∨
    (∃ i, sideSq q i < sideSq q (cyclicPrev i) ∧
      sideSq q i < sideSq q (cyclicNext i) ∧
      sideSq q (cyclicPrev i) = sideSq q (cyclicNext i) ∧
      (∀ t ∈ commonMassMaximalNewtonDomain G μ
        (q, fun _ : Fin 3 => (0 : Point)), 0 ≤ t →
        signedDoubleArea
          (commonMassMaximalNewtonTrajectory G μ
            (q, fun _ : Fin 3 => (0 : Point)) t).1 ≠ 0) ∧
      0 < sSup (commonMassMaximalNewtonDomain G μ
        (q, fun _ : Fin 3 => (0 : Point))) ∧
      sSup (commonMassMaximalNewtonDomain G μ
        (q, fun _ : Fin 3 => (0 : Point))) ≤
        Real.sqrt (8 * (dist (q (cyclicPrev i)) (q (cyclicNext i)) / 2) ^ 3) /
          Real.sqrt (G * μ) ∧
      Tendsto
        (fun t => dist ((commonMassMaximalNewtonTrajectory G μ
          (q, fun _ : Fin 3 => (0 : Point)) t).1 (cyclicPrev i))
          ((commonMassMaximalNewtonTrajectory G μ
            (q, fun _ : Fin 3 => (0 : Point)) t).1 (cyclicNext i)))
        (nhdsWithin (sSup (commonMassMaximalNewtonDomain G μ
          (q, fun _ : Fin 3 => (0 : Point))))
          (Set.Iio (sSup (commonMassMaximalNewtonDomain G μ
            (q, fun _ : Fin 3 => (0 : Point)))))) (𝓝 0))) := by
  let κ := Real.sqrt (G * μ)
  have hκ : 0 < κ := Real.sqrt_pos.2 (mul_pos hG hμ)
  let z₀ : Phase := (q, fun _ : Fin 3 => (0 : Point))
  let zU := maximalNewtonUnionTrajectory z₀
  let DU := maximalNewtonUnionDomain z₀
  let zG := commonMassMaximalNewtonTrajectory G μ z₀
  let DG := commonMassMaximalNewtonDomain G μ z₀
  have hclass := equalMass_maximal_sideOrder_classification q hcf harea
  have hunion : commonMassNewtonUnionDomain G μ z₀ = DG := by
    exact commonMassNewtonUnionDomain_eq_maximalDomain G μ hG hμ z₀
      (by intro i; rfl)
  have hsolution : GeneralClassicalNewtonSolution G
      (fun _ : Fin 3 => μ) zG DG := by
    exact commonMassMaximalNewtonTrajectory_solution G μ hG hμ z₀
  have hdom : ∀ t, t ∈ DG ↔ κ * t ∈ DU := by
    intro t
    rfl
  have htraj : ∀ t, zG t = timeScalePhase κ (zU (κ * t)) := by
    intro t
    rfl
  have hdist : ∀ i j,
      (fun t => dist ((zG t).1 i) ((zG t).1 j)) =
        (fun t => dist ((zU (κ * t)).1 i) ((zU (κ * t)).1 j)) := by
    intro i j
    funext t
    rw [htraj t]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hunion
  · exact hsolution
  · rcases hclass with hstrict | hequil | hisosceles
    · rcases hstrict with ⟨i, TU, hTUD, hTUpos, hfirstU, hbetweenU⟩
      let T := TU / κ
      have htime : κ * T = TU := commonMass_timeScale_eventTime hκ
      have hTD : T ∈ DG := by
        change κ * T ∈ DU
        rw [htime]
        exact hTUD
      have hfirstG : FirstRegularSyzygy zG DG 0 T := by
        have h := commonMass_firstRegularSyzygy_rescale hκ hfirstU
        simpa [T, zG, DG, zU, DU,
          commonMassMaximalNewtonTrajectory, commonMassMaximalNewtonDomain] using h
      have hbetweenG : Sbtw ℝ ((zG T).1 (cyclicPrev i)) ((zG T).1 i)
          ((zG T).1 (cyclicNext i)) := by
        simpa [T, htraj, timeScalePhase, htime] using hbetweenU
      exact Or.inl ⟨i, T, hTD, div_pos hTUpos hκ, hfirstG, hbetweenG⟩
    · rcases hequil with ⟨KU, hTUpos, hdomainU, hareaU, hcollapseU⟩
      let K := KU / κ
      let T := homotheticCollapseTime K
      have hTscale : T = homotheticCollapseTime KU / κ := by
        simp [T, K, homotheticCollapseTime]
        ring
      have hTpos : 0 < T := by
        rw [hTscale]
        exact div_pos hTUpos hκ
      have hdomainG : ∀ t, 0 ≤ t → (t ∈ DG ↔ t < T) := by
        intro t ht
        rw [hdom t, hdomainU (κ * t) (mul_nonneg (le_of_lt hκ) ht)]
        rw [hTscale]
        constructor
        · intro h
          apply (lt_div_iff₀ hκ).2
          simpa [mul_comm] using h
        · intro h
          have h' := (lt_div_iff₀ hκ).1 h
          simpa [mul_comm] using h'
      have hareaG : ∀ t, 0 ≤ t → t < T → signedDoubleArea (zG t).1 ≠ 0 := by
        intro t ht htT
        have hdomt : t ∈ DG := (hdomainG t ht).2 htT
        have hscaled := (hdom t).1 hdomt
        have hscaledArea := hareaU (κ * t)
          (mul_nonneg (le_of_lt hκ) ht)
          ((hdomainU (κ * t) (mul_nonneg (le_of_lt hκ) ht)).mp hscaled)
        simpa [htraj, timeScalePhase] using hscaledArea
      have hendpointMap :=
        commonMass_timeScale_leftEndpoint_tendsto hκ
          (T := homotheticCollapseTime KU)
      have hcollapseG : ∀ i j : Fin 3, Tendsto
          (fun t => dist ((zG t).1 i) ((zG t).1 j))
          (nhdsWithin T (Set.Iio T)) (𝓝 0) := by
        intro i j
        rw [hTscale]
        rw [hdist i j]
        have hfun : (fun t => dist ((zU (κ * t)).1 i) ((zU (κ * t)).1 j)) =
            (fun s => dist ((zU s).1 i) ((zU s).1 j)) ∘ (fun t => κ * t) := by
          funext t
          rfl
        rw [hfun]
        simpa [zU, z₀] using (hcollapseU i j).comp hendpointMap
      exact Or.inr (Or.inl ⟨K, hTpos, hdomainG, hareaG, hcollapseG⟩)
    · rcases hisosceles with
        ⟨i, hshortPrev, hshortNext, heq, hnoU, hsupUpos, hsupUbound, hlimitU⟩
      have hzeroDU : (0 : ℝ) ∈ DU := by
        obtain ⟨w⟩ := exists_newtonInitialIntervalWitness z₀ hcf
        exact maximalNewtonWitness_interval_subset z₀ w
          ⟨w.left_lt_zero, w.zero_lt_right⟩
      have hDUne : DU.Nonempty := ⟨0, hzeroDU⟩
      have hDUBdd : BddAbove DU := by
        by_contra hnot
        have hzero : sSup DU = sSup (∅ : Set ℝ) := csSup_of_not_bddAbove hnot
        simp at hzero
        linarith
      have hsupEq := commonMass_sSup_gravityRescaledDomain hκ hDUne hDUBdd
      have hsupEqDG : sSup DG = sSup DU / κ := by
        change sSup (gravityRescaledDomain κ DU) = sSup DU / κ
        exact hsupEq
      have hsupGpos : 0 < sSup DG := by
        rw [hsupEqDG]
        exact div_pos hsupUpos hκ
      have hsupGbound : sSup DG ≤
          Real.sqrt (8 * (dist (q (cyclicPrev i)) (q (cyclicNext i)) / 2) ^ 3) / κ := by
        rw [hsupEqDG]
        exact div_le_div_of_nonneg_right hsupUbound (le_of_lt hκ)
      have hnoG : ∀ t ∈ DG, 0 ≤ t → signedDoubleArea (zG t).1 ≠ 0 := by
        intro t ht ht0
        have hscaled := (hdom t).1 ht
        have ht0' : 0 ≤ κ * t := mul_nonneg (le_of_lt hκ) ht0
        have hno := hnoU (κ * t) hscaled ht0'
        simpa [htraj, timeScalePhase] using hno
      have hendpointMap := commonMass_timeScale_leftEndpoint_tendsto hκ
        (T := sSup DU)
      have hlimitG : Tendsto
          (fun t => dist ((zG t).1 (cyclicPrev i))
            ((zG t).1 (cyclicNext i)))
          (nhdsWithin (sSup DG) (Set.Iio (sSup DG))) (𝓝 0) := by
        rw [hsupEqDG]
        rw [hdist (cyclicPrev i) (cyclicNext i)]
        have hfun :
            (fun t => dist ((zU (κ * t)).1 (cyclicPrev i))
              ((zU (κ * t)).1 (cyclicNext i))) =
            (fun s => dist ((zU s).1 (cyclicPrev i))
              ((zU s).1 (cyclicNext i))) ∘ (fun t => κ * t) := by
          funext t
          rfl
        rw [hfun]
        simpa [zU, z₀] using hlimitU.comp hendpointMap
      exact Or.inr (Or.inr ⟨i, hshortPrev, hshortNext, heq, hnoG,
        hsupGpos, hsupGbound, hlimitG⟩)

end

end DroppingThreeBodies
