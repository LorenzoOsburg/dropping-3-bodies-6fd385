module

public import NBody.Newton
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic

@[expose] public section

namespace NBody

/-- A classical Newtonian solution on an open time set: the configuration is
collision-free and its phase curve satisfies the first-order field equation. -/
def ClassicalSolution {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (G : ℝ) (m : ι → ℝ) (z : ℝ → Phase ι d) (I : Set ℝ) : Prop :=
  IsOpen I ∧ ∀ t ∈ I, CollisionFree (z t).1 ∧
    HasDerivAt z (vectorField G m (z t)) t

theorem classicalSolution_iff_integralCurveOn {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {G : ℝ} {m : ι → ℝ}
    {z : ℝ → Phase ι d} {I : Set ℝ} :
    ClassicalSolution G m z I ↔
      IsOpen I ∧ (∀ t ∈ I, CollisionFree (z t).1) ∧
        IsIntegralCurveOn z (fun _ w => vectorField G m w) I := by
  constructor
  · rintro ⟨hopen, hsol⟩
    refine ⟨hopen, (fun t ht => (hsol t ht).1), ?_⟩
    intro t ht
    exact (hsol t ht).2.hasDerivWithinAt
  · rintro ⟨hopen, hcf, hcurve⟩
    refine ⟨hopen, fun t ht => ⟨hcf t ht, ?_⟩⟩
    exact (hcurve t ht).hasDerivAt (hopen.mem_nhds ht)

theorem solution_body_derivatives {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} {G : ℝ} {m : ι → ℝ}
    {z : ℝ → Phase ι d} {I : Set ℝ} {t : ℝ}
    (hsol : ClassicalSolution G m z I) (ht : t ∈ I) (i : ι) :
    HasDerivAt (fun s => (z s).1 i) ((z t).2 i) t ∧
      HasDerivAt (fun s => (z s).2 i) (acceleration G m (z t).1 i) t := by
  have hphase := (hsol.2 t ht).2
  have hpos : HasDerivAt (fun s => (z s).1) ((vectorField G m (z t)).1) t := by
    simpa using hphase.hasFDerivAt.fst.hasDerivAt
  have hvel : HasDerivAt (fun s => (z s).2) ((vectorField G m (z t)).2) t := by
    simpa using hphase.hasFDerivAt.snd.hasDerivAt
  constructor
  · simpa [vectorField] using (hasDerivAt_pi.1 hpos) i
  · simpa [vectorField] using (hasDerivAt_pi.1 hvel) i

end NBody
