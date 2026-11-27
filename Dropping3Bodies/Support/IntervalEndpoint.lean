module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# Continuous extension to a right interval endpoint

A value that is constant on every point before a finite right endpoint must
have the same value at that endpoint when the function is continuous on the
closed interval.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

/-- A Lipschitz curve into a finite-dimensional real normed space has a
    genuine left limit at a finite right endpoint. We extend the curve to the
    whole time line using Mathlib's finite-dimensional Lipschitz extension
    theorem and transfer the extension's continuity back to the left filter. -/
theorem exists_left_limit_of_lipschitzOnWith_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ → E} {a T : ℝ} {K : NNReal}
    (haT : a < T) (hLip : LipschitzOnWith K f (Set.Ico a T)) :
    ∃ x : E, Tendsto f (nhdsWithin T (Set.Iio T)) (𝓝 x) := by
  obtain ⟨g, hg, hEq⟩ := hLip.extend_finite_dimension
  have hcont : ContinuousAt g T := hg.continuous.continuousAt
  have hgt : Tendsto g (nhdsWithin T (Set.Iio T)) (𝓝 (g T)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have haEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T), t ∈ Set.Ioi a := by
    exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio T))
      (Ioi_mem_nhds haT)
  have hEqEvent : f =ᶠ[nhdsWithin T (Set.Iio T)] g := by
    filter_upwards [haEvent, self_mem_nhdsWithin] with t hta ht
    exact hEq ⟨le_of_lt hta, ht⟩
  exact ⟨g T, hgt.congr' hEqEvent.symm⟩

/-- A finite-dimensional real-valued curve that is Lipschitz on a left-open
    interval has a genuine left limit at its finite right endpoint. The proof
    extends it coordinatewise using Mathlib's Lipschitz extension theorem,
    then uses continuity of that extension. -/
theorem exists_left_limit_of_lipschitzOnWith_pi
    {ι : Type*} [Fintype ι] {f : ℝ → ι → ℝ} {a T : ℝ} {K : NNReal}
    (haT : a < T) (hLip : LipschitzOnWith K f (Set.Ioc a T)) :
    ∃ x : ι → ℝ, Tendsto f (nhdsWithin T (Set.Iio T)) (𝓝 x) := by
  obtain ⟨g, hg, hEq⟩ := hLip.extend_pi
  have hcont : ContinuousAt g T := hg.continuous.continuousAt
  have hgt : Tendsto g (nhdsWithin T (Set.Iio T)) (𝓝 (g T)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have haEvent : ∀ᶠ t in nhdsWithin T (Set.Iio T), t ∈ Set.Ioi a := by
    exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Iio T))
      (Ioi_mem_nhds haT)
  have hEqEvent : f =ᶠ[nhdsWithin T (Set.Iio T)] g := by
    filter_upwards [haEvent, self_mem_nhdsWithin] with t hta ht
    exact hEq ⟨hta, le_of_lt ht⟩
  exact ⟨g T, hgt.congr' hEqEvent.symm⟩

theorem continuousOn_eq_zero_right_of_eq_zero_Ico
    {f : ℝ → ℝ} {a T : ℝ} (haT : a < T)
    (hcont : ContinuousOn f (Set.Icc a T))
    (hzero : ∀ t ∈ Set.Ico a T, f t = 0) :
    f T = 0 := by
  let u : ℕ → ℝ := fun n => T - (T - a) / ((n : ℝ) + 1)
  have hu_pos_fraction (n : ℕ) : 0 < (T - a) / ((n : ℝ) + 1) := by
    apply div_pos (sub_pos.mpr haT)
    positivity
  have hu_le_fraction (n : ℕ) :
      (T - a) / ((n : ℝ) + 1) ≤ T - a := by
    apply div_le_self (le_of_lt (sub_pos.mpr haT))
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hu_mem (n : ℕ) : u n ∈ Set.Icc a T := by
    dsimp [u]
    constructor <;> nlinarith [hu_pos_fraction n, hu_le_fraction n]
  have hu_tendsto : Tendsto u atTop (𝓝 T) := by
    have hinv := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hscaled : Tendsto (fun n : ℕ => (T - a) * (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hinv)
    have hsub : Tendsto u atTop (𝓝 T) := by
      simpa [u, div_eq_mul_inv, mul_comm] using
        (tendsto_const_nhds (x := T)).sub hscaled
    exact hsub
  have hu_within := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    u hu_tendsto (Filter.Eventually.of_forall hu_mem)
  have hlimit : Tendsto (fun n => f (u n)) atTop (𝓝 (f T)) :=
    (hcont T ⟨le_of_lt haT, le_rfl⟩).tendsto.comp hu_within
  have hzeroSeq : (fun n => f (u n)) = fun _ => 0 := by
    funext n
    apply hzero
    constructor
    · have := (hu_mem n).1
      exact this
    · dsimp [u]
      linarith [hu_pos_fraction n]
  rw [hzeroSeq] at hlimit
  exact (tendsto_nhds_unique tendsto_const_nhds hlimit).symm

/-- A continuous function nonnegative before the right endpoint remains
    nonnegative at that endpoint. -/
theorem continuousOn_nonneg_right_of_nonneg_Ico
    {f : ℝ → ℝ} {a T : ℝ} (haT : a < T)
    (hcont : ContinuousOn f (Set.Icc a T))
    (hnonneg : ∀ t ∈ Set.Ico a T, 0 ≤ f t) :
    0 ≤ f T := by
  let u : ℕ → ℝ := fun n => T - (T - a) / ((n : ℝ) + 1)
  have hu_pos_fraction (n : ℕ) : 0 < (T - a) / ((n : ℝ) + 1) := by
    apply div_pos (sub_pos.mpr haT)
    positivity
  have hu_le_fraction (n : ℕ) :
      (T - a) / ((n : ℝ) + 1) ≤ T - a := by
    apply div_le_self (le_of_lt (sub_pos.mpr haT))
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hu_mem (n : ℕ) : u n ∈ Set.Icc a T := by
    dsimp [u]
    constructor <;> nlinarith [hu_pos_fraction n, hu_le_fraction n]
  have hu_tendsto : Tendsto u atTop (𝓝 T) := by
    have hinv := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hscaled : Tendsto (fun n : ℕ => (T - a) * (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hinv)
    simpa [u, div_eq_mul_inv, mul_comm] using
      (tendsto_const_nhds (x := T)).sub hscaled
  have hu_within := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    u hu_tendsto (Filter.Eventually.of_forall hu_mem)
  have hlimit : Tendsto (fun n => f (u n)) atTop (𝓝 (f T)) :=
    (hcont T ⟨le_of_lt haT, le_rfl⟩).tendsto.comp hu_within
  have hnonnegSeq : ∀ n, 0 ≤ f (u n) := fun n => hnonneg (u n)
    ⟨(hu_mem n).1, by dsimp [u]; linarith [hu_pos_fraction n]⟩
  change f T ∈ Set.Ici 0
  exact (isClosed_Ici (a := (0 : ℝ))).mem_of_tendsto hlimit
    (Filter.Eventually.of_forall hnonnegSeq)

/-- A continuous function nonpositive before the right endpoint remains
    nonpositive at that endpoint. -/
theorem continuousOn_nonpos_right_of_nonpos_Ico
    {f : ℝ → ℝ} {a T : ℝ} (haT : a < T)
    (hcont : ContinuousOn f (Set.Icc a T))
    (hnonpos : ∀ t ∈ Set.Ico a T, f t ≤ 0) :
    f T ≤ 0 := by
  have h := continuousOn_nonneg_right_of_nonneg_Ico haT hcont.neg
    (fun t ht => by simpa using (hnonpos t ht))
  exact neg_nonneg.mp h

end DroppingThreeBodies
