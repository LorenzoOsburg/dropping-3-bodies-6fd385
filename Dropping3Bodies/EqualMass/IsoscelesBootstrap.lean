module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

namespace DroppingThreeBodies

/-- Abstract first-violation principle for a Wronskian bootstrap. If `W` starts
    at zero and has positive derivative whenever `ratio > c`, while
    `ratio' = W / x^2` and `x` stays positive, then the ratio cannot reach `c`
    from above on a compact forward interval. -/
theorem ratio_stays_above_of_wronskian_bootstrap
    {a b c : ℝ} {x W ratio Wdot : ℝ → ℝ}
    (hx : ∀ t ∈ Set.Icc a b, 0 < x t)
    (hW0 : W a = 0)
    (hratio0 : c < ratio a)
    (hWderiv : ∀ t ∈ Set.Icc a b, HasDerivAt W (Wdot t) t)
    (hratioderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt ratio (W t / (x t) ^ 2) t)
    (hWdot_pos : ∀ t ∈ Set.Icc a b, c < ratio t → 0 < Wdot t) :
    ∀ t ∈ Set.Icc a b, c < ratio t := by
  have hratio_cont : ContinuousOn ratio (Set.Icc a b) := by
    intro t ht
    exact (hratioderiv t ht).continuousAt.continuousWithinAt
  intro t ht
  by_contra hnot
  have hbad : ratio t ≤ c := not_lt.mp hnot
  let D := Set.Icc a t
  let S : Set D := {s | ratio s.val ≤ c}
  have htSub : Set.Icc a t ⊆ Set.Icc a b := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 ht.2⟩
  haveI : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_Icc
  have hSclosed : IsClosed S := by
    change IsClosed ((fun s : D => ratio s.val) ⁻¹' Set.Iic c)
    exact isClosed_Iic.preimage
      (continuousOn_iff_continuous_restrict.mp (hratio_cont.mono htSub))
  have hScompact : IsCompact S := hSclosed.isCompact
  have hSne : S.Nonempty := ⟨⟨t, ⟨ht.1, le_rfl⟩⟩, hbad⟩
  obtain ⟨τ, hτ⟩ := hScompact.exists_isLeast hSne
  have hτf : ratio (τ : ℝ) ≤ c := hτ.1
  have hτleT : (τ : ℝ) ≤ t := τ.property.2
  have haτ : a < (τ : ℝ) := by
    have hle := τ.property.1
    by_contra h
    have heq : (τ : ℝ) = a := by linarith
    have hbadInitial : ratio a ≤ c := by simpa [heq] using hτf
    exact (not_le_of_gt hratio0) hbadInitial
  have hfirst : ∀ s ∈ Set.Ioo a (τ : ℝ), c < ratio s := by
    intro s hs
    have hsD : s ∈ D := ⟨le_of_lt hs.1, le_trans (le_of_lt hs.2) hτleT⟩
    by_contra hnotAbove
    have hsBad : ratio s ≤ c := not_lt.mp hnotAbove
    have hsMem : (⟨s, hsD⟩ : D) ∈ S := hsBad
    have hτleS : (τ : ℝ) ≤ s := hτ.2 hsMem
    exact (not_le_of_gt hs.2) hτleS
  have hsegment : Set.Icc a (τ : ℝ) ⊆ Set.Icc a b := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 (le_trans hτleT ht.2)⟩
  have hWcont : ContinuousOn W (Set.Icc a (τ : ℝ)) := by
    intro s hs
    exact (hWderiv s (hsegment hs)).continuousAt.continuousWithinAt
  have hWmono : StrictMonoOn W (Set.Icc a (τ : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a (τ : ℝ)) hWcont
    intro s hsInterior
    have hsIOO : s ∈ Set.Ioo a (τ : ℝ) := by
      simpa [interior_Icc] using hsInterior
    rw [(hWderiv s (hsegment ⟨le_of_lt hsIOO.1, le_of_lt hsIOO.2⟩)).deriv]
    exact hWdot_pos s (hsegment ⟨le_of_lt hsIOO.1, le_of_lt hsIOO.2⟩)
      (hfirst s hsIOO)
  have hWinterior : ∀ s ∈ Set.Ioo a (τ : ℝ), 0 < W s := by
    intro s hs
    have hstrict := hWmono ⟨le_rfl, haτ.le⟩
      ⟨le_of_lt hs.1, le_of_lt hs.2⟩ hs.1
    rw [hW0] at hstrict
    exact hstrict
  have hratio_cont_segment : ContinuousOn ratio (Set.Icc a (τ : ℝ)) :=
    hratio_cont.mono hsegment
  have hratio_mono : StrictMonoOn ratio (Set.Icc a (τ : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a (τ : ℝ)) hratio_cont_segment
    intro s hsInterior
    have hsIOO : s ∈ Set.Ioo a (τ : ℝ) := by
      simpa [interior_Icc] using hsInterior
    rw [(hratioderiv s (hsegment ⟨le_of_lt hsIOO.1, le_of_lt hsIOO.2⟩)).deriv]
    exact div_pos (hWinterior s hsIOO)
      (sq_pos_of_pos (hx s (hsegment ⟨le_of_lt hsIOO.1, le_of_lt hsIOO.2⟩)))
  have hratioStrict := hratio_mono ⟨le_rfl, haτ.le⟩
    ⟨haτ.le, le_rfl⟩ haτ
  linarith

end DroppingThreeBodies
