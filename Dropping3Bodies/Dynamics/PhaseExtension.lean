module

public import Dropping3Bodies.Dynamics.PhaseLipschitz
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Local continuation across a regular phase endpoint

This module joins a left Newton trajectory to the local Picard solution from
its collision-free phase limit. The proof uses the autonomous character of
the Newton field and the one-sided derivative extension lemma in Mathlib.
-/

namespace DroppingThreeBodies

open Filter
open scoped Topology

/-- A classical Newton trajectory on a left interval extends through a finite
    endpoint if its phase has a collision-free left limit there. The extension
    retains the entire old trajectory on `(a,T)` and uses the local IVP
    trajectory immediately to the right of `T`. The source-level one-sided derivative adapter is
    `classicalNewton_left_extension_hasDerivWithinAt_of_phase_left_limit`;
    two-sided differentiability at the join follows from the continuous-field
    derivative gluing lemma in Mathlib. -/
theorem classicalNewton_local_extension_of_phase_left_limit
    {z : ℝ → Phase} {I : Set ℝ} {zT : Phase} {a T : ℝ}
    (haT : a < T)
    (hsol : ClassicalNewtonSolution z I)
    (hright : ∀ t ∈ Set.Ioo a T, t ∈ I)
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT))
    (hcf : CollisionFree zT.1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ w : ℝ → Phase,
      w T = zT ∧ ClassicalNewtonSolution w (Set.Ioo a (T + ρ)) ∧
      ∀ t ∈ Set.Ioo a T, w t = z t := by
  obtain ⟨ε, hε, y, hy0, hySol⟩ := exists_local_classicalNewtonSolution zT hcf
  let ρ := ε
  have hρ : 0 < ρ := hε
  have hρleε : ρ ≤ ε := le_of_eq rfl
  have hlocalZero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    constructor <;> linarith
  have hyDerivZero : HasDerivAt y (unitNewtonField zT) 0 := by
    have h := (hySol.2 0 hlocalZero).2
    simpa [hy0] using h
  let w : ℝ → Phase := fun t => if t < T then z t else y (t - T)
  have hwT : w T = zT := by simp [w, hy0]
  let zLeft : ℝ → Phase := fun t => if t < T then z t else zT
  let aMid := (a + T) / 2
  have haMid : a < aMid := by dsimp [aMid]; linarith
  have haMidT : aMid < T := by dsimp [aMid]; linarith
  have hrightMid : ∀ t ∈ Set.Ico aMid T, t ∈ I := by
    intro t ht
    exact hright t ⟨lt_of_lt_of_le haMid ht.1, ht.2⟩
  have hLeftExt : HasDerivWithinAt zLeft (unitNewtonField zT) (Set.Iic T) T :=
    classicalNewton_left_extension_hasDerivWithinAt_of_phase_left_limit
      haMidT hsol hrightMid hlim hcf
  have hEqLeft : ∀ t ∈ Set.Iic T, w t = zLeft t := by
    intro t ht
    by_cases htt : t < T
    · simp [w, zLeft, htt]
    · have hEq : t = T := le_antisymm ht (le_of_not_gt htt)
      subst t
      simp [w, zLeft, hy0]
  have hWLeft : HasDerivWithinAt w (unitNewtonField zT) (Set.Iic T) T :=
    hLeftExt.congr hEqLeft (hEqLeft T (by simp))
  have hShift : HasDerivAt (fun t => y (t - T)) (unitNewtonField zT) T := by
    have hD0 : HasDerivAt y (unitNewtonField zT) (T - T) := by
      simpa using hyDerivZero
    have h := HasDerivAt.comp_sub_const T T hD0
    simpa using h
  have hEqRight : ∀ t ∈ Set.Ici T, w t = y (t - T) := by
    intro t ht
    have ht' : ¬ t < T := not_lt_of_ge ht
    simp [w, ht']
  have hWRight : HasDerivWithinAt w (unitNewtonField zT) (Set.Ici T) T :=
    hShift.hasDerivWithinAt.congr hEqRight (hEqRight T (by simp))
  have hleftSlope : Tendsto (slope w T) (nhdsWithin T (Set.Iio T))
      (𝓝 (unitNewtonField zT)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hWLeft
    have hle : nhdsWithin T (Set.Iio T) ≤ nhdsWithin T (Set.Iic T \ {T}) :=
      nhdsWithin_mono T (by
        intro t ht
        change t < T at ht
        exact ⟨le_of_lt ht, by simp [ht.ne]⟩)
    exact h.mono_left hle
  have hrightSlope : Tendsto (slope w T) (nhdsWithin T (Set.Ioi T))
      (𝓝 (unitNewtonField zT)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hWRight
    have hle : nhdsWithin T (Set.Ioi T) ≤ nhdsWithin T (Set.Ici T \ {T}) :=
      nhdsWithin_mono T (by
        intro t ht
        change T < t at ht
        exact ⟨le_of_lt ht, by simp [ht.ne']⟩)
    exact h.mono_left hle
  have hDjoin : HasDerivAt w (unitNewtonField zT) T :=
    (hasDerivAt_iff_tendsto_slope_left_right).2 ⟨hleftSlope, hrightSlope⟩
  have hρpos : 0 < ρ := hρ
  refine ⟨ρ, hρpos, w, hwT, ?_, ?_⟩
  · refine ⟨isOpen_Ioo, ?_⟩
    intro t ht
    have hcollision : CollisionFree (w t).1 := by
      by_cases hleftT : t < T
      · have htI : t ∈ I := hright t ⟨ht.1, hleftT⟩
        simpa [w, hleftT] using (hsol.2 t htI).1
      · have hτlo : -ε < t - T := by
          have hTt : T ≤ t := le_of_not_gt hleftT
          linarith [hε]
        have hτhi : t - T < ε := by linarith [ht.2, hρleε]
        have hτ : t - T ∈ Set.Ioo (-ε) ε := ⟨hτlo, hτhi⟩
        have h := (hySol.2 (t - T) hτ).1
        simpa [w, hleftT] using h
    have hderiv : HasDerivAt w (unitNewtonField (w t)) t := by
      by_cases hleftT : t < T
      · have htI : t ∈ I := hright t ⟨ht.1, hleftT⟩
        have hD : HasDerivAt z (unitNewtonField (z t)) t := (hsol.2 t htI).2
        have hlocalEq : w =ᶠ[𝓝 t] z := by
          filter_upwards [Iio_mem_nhds hleftT] with s hs
          have hs' : s < T := hs
          simp [w, hs']
        have hDExt := hD.congr_of_eventuallyEq hlocalEq
        have hwt : w t = z t := by simp [w, hleftT]
        simpa [hwt] using hDExt
      · by_cases hne : t = T
        · subst t
          simpa [hwT] using hDjoin
        · have hTt : T < t := lt_of_le_of_ne (le_of_not_gt hleftT) (Ne.symm hne)
          have hτlo : -ε < t - T := by linarith [hε]
          have hτhi : t - T < ε := by linarith [ht.2, hρleε]
          have hτ : t - T ∈ Set.Ioo (-ε) ε := ⟨hτlo, hτhi⟩
          have hDlocal : HasDerivAt y (unitNewtonField (y (t - T))) (t - T) :=
            (hySol.2 (t - T) hτ).2
          have hDshift : HasDerivAt (fun s => y (s - T))
              (unitNewtonField (y (t - T))) t := by
            exact HasDerivAt.comp_sub_const t T hDlocal
          have hlocalEq : w =ᶠ[𝓝 t] (fun s => y (s - T)) := by
            filter_upwards [Ioi_mem_nhds hTt] with s hs
            have hs' : T < s := hs
            simp [w, not_lt_of_gt hs']
          have hDExt := hDshift.congr_of_eventuallyEq hlocalEq
          have hwt : w t = y (t - T) := by simp [w, not_lt_of_gt hTt]
          simpa [hwt] using hDExt
    exact ⟨hcollision, hderiv⟩
  · intro t ht
    have ht' : t < T := ht.2
    simp [w, ht']

/-- A solution on `(a,T)` is right-maximal when it has no classical
    continuation to any strictly larger interval `(a,T+ρ)` that agrees on
    the old interval. -/
def ClassicalNewtonRightMaximal (z : ℝ → Phase) (a T : ℝ) : Prop :=
  ∀ ρ > 0, ∀ w : ℝ → Phase,
    ClassicalNewtonSolution w (Set.Ioo a (T + ρ)) →
      (∀ t ∈ Set.Ioo a T, w t = z t) → False

/-- A right-maximal classical Newton trajectory cannot end at a finite
    collision-free phase limit: local existence and the gluing theorem extend
    the whole old interval to the right. -/
theorem classicalNewton_rightMaximal_endpoint_not_collisionFree
    {z : ℝ → Phase} {zT : Phase} {a T : ℝ}
    (haT : a < T)
    (hsol : ClassicalNewtonSolution z (Set.Ioo a T))
    (hlim : Tendsto z (nhdsWithin T (Set.Iio T)) (𝓝 zT))
    (hmax : ClassicalNewtonRightMaximal z a T) :
    ¬ CollisionFree zT.1 := by
  intro hcf
  obtain ⟨ρ, hρ, w, _, hnew, hagree⟩ :=
    classicalNewton_local_extension_of_phase_left_limit
      haT hsol (by
        intro t ht
        exact ht) hlim hcf
  exact hmax ρ hρ w hnew hagree

end DroppingThreeBodies
