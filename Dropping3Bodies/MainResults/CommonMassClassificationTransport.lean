module

public import Dropping3Bodies.Dynamics.CommonMassMaximalFlow
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Complete transport lemmas for first syzygies, one-sided endpoint limits,
and suprema under a positive time rescaling. -/

namespace DroppingThreeBodies

open Filter
open scoped Topology

noncomputable section

/-- The event time transforms by division by the positive time scale. -/
theorem commonMass_timeScale_eventTime {κ T : ℝ} (hκ : 0 < κ) :
    κ * (T / κ) = T := by
  field_simp [hκ.ne']

/-- A regular first-syzygy certificate is preserved by positive gravity
rescaling, with the event time divided by the scale. -/
theorem commonMass_firstRegularSyzygy_rescale
    {κ : ℝ} (hκ : 0 < κ) {z : ℝ → Phase} {D : Set ℝ} {T : ℝ}
    (hfirst : FirstRegularSyzygy z D 0 T) :
    FirstRegularSyzygy (gravityRescaledTrajectory κ z)
      (gravityRescaledDomain κ D) 0 (T / κ) := by
  rcases hfirst with ⟨hT, hsegment, hzero, hpre, hcf⟩
  have htime : κ * (T / κ) = T := commonMass_timeScale_eventTime hκ
  refine ⟨div_pos hT hκ, ?_, ?_, ?_, ?_⟩
  · intro t ht
    change κ * t ∈ D
    apply hsegment
    constructor
    · exact mul_nonneg (le_of_lt hκ) ht.1
    · calc
        κ * t ≤ κ * (T / κ) := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hκ)
        _ = T := htime
  · simpa [gravityRescaledTrajectory, timeScalePhase, htime] using hzero
  · intro t ht
    apply hpre (κ * t)
    constructor
    · exact mul_nonneg (le_of_lt hκ) ht.1
    · calc
        κ * t < κ * (T / κ) := mul_lt_mul_of_pos_left ht.2 hκ
        _ = T := htime
  · simpa [gravityRescaledTrajectory, timeScalePhase, htime] using hcf

/-- Positive time rescaling maps a left-sided neighborhood of the rescaled
endpoint into the corresponding left-sided neighborhood of the original. -/
theorem commonMass_timeScale_leftEndpoint_tendsto
    {κ T : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => κ * t)
      (nhdsWithin (T / κ) (Set.Iio (T / κ)))
      (nhdsWithin T (Set.Iio T)) := by
  have htime : κ * (T / κ) = T := commonMass_timeScale_eventTime hκ
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => κ * t) (T / κ) :=
      (continuous_const_mul κ).continuousAt
    simpa [htime] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    calc
      κ * t < κ * (T / κ) := mul_lt_mul_of_pos_left ht hκ
      _ = T := htime

/-- The supremum of a nonempty bounded domain scales by the inverse positive
time factor. -/
theorem commonMass_sSup_gravityRescaledDomain
    {κ : ℝ} (hκ : 0 < κ) {D : Set ℝ}
    (hne : D.Nonempty) (hbounded : BddAbove D) :
    sSup (gravityRescaledDomain κ D) = sSup D / κ := by
  have hSnonempty : (gravityRescaledDomain κ D).Nonempty := by
    rcases hne with ⟨x, hx⟩
    refine ⟨x / κ, ?_⟩
    change κ * (x / κ) ∈ D
    have hmul : κ * (x / κ) = x := by field_simp [hκ.ne']
    simpa [hmul] using hx
  have hSupper : ∀ x ∈ gravityRescaledDomain κ D, x ≤ sSup D / κ := by
    intro x hx
    change κ * x ∈ D at hx
    have hle : κ * x ≤ sSup D := le_csSup hbounded hx
    exact (le_div_iff₀ hκ).2 (by nlinarith [hle])
  have hSbounded : BddAbove (gravityRescaledDomain κ D) :=
    ⟨sSup D / κ, hSupper⟩
  have hsupUpper : ∀ x ∈ D, x ≤ κ * sSup (gravityRescaledDomain κ D) := by
    intro x hx
    have hxS : x / κ ∈ gravityRescaledDomain κ D := by
      change κ * (x / κ) ∈ D
      have hmul : κ * (x / κ) = x := by field_simp [hκ.ne']
      simpa [hmul] using hx
    have hle : x / κ ≤ sSup (gravityRescaledDomain κ D) :=
      le_csSup hSbounded hxS
    have hle' : x ≤ sSup (gravityRescaledDomain κ D) * κ :=
      (div_le_iff₀ hκ).mp hle
    nlinarith [hle']
  have hsupLe : sSup D ≤ κ * sSup (gravityRescaledDomain κ D) :=
    csSup_le hne hsupUpper
  have hsupSle : sSup (gravityRescaledDomain κ D) ≤ sSup D / κ :=
    csSup_le hSnonempty hSupper
  have hdivle : sSup D / κ ≤ sSup (gravityRescaledDomain κ D) :=
    (div_le_iff₀ hκ).2 (by simpa [mul_comm] using hsupLe)
  exact le_antisymm hsupSle hdivle

end

end DroppingThreeBodies
