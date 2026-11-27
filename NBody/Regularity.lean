module

public import NBody.Newton
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Tactic

@[expose] public section

namespace NBody

open Filter
open scoped Topology

noncomputable section

theorem contDiffAt_phaseDistance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (z : Phase ι d) (i j : ι) (hcollision : z.1 i ≠ z.1 j) :
    ContDiffAt ℝ 1 (fun w : Phase ι d => dist (w.1 i) (w.1 j)) z := by
  have hdiff : ContDiffAt ℝ 1 (fun w : Phase ι d => w.1 i - w.1 j) z := by
    fun_prop
  have hnonzero : z.1 i - z.1 j ≠ (0 : EuclideanSpace ℝ (Fin d)) :=
    sub_ne_zero.mpr hcollision
  simpa only [dist_eq_norm] using ContDiffAt.norm ℝ hdiff hnonzero

theorem inverseCubeDistance_contDiffAt {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (z : Phase ι d) (i j : ι)
    (hcollision : z.1 i ≠ z.1 j) :
    ContDiffAt ℝ 1 (fun w : Phase ι d => inverseCubeDistance w.1 i j) z := by
  have hd := contDiffAt_phaseDistance z i j hcollision
  have hpos : 0 < dist (z.1 i) (z.1 j) := dist_pos.mpr hcollision
  have hpow : ContDiffAt ℝ 1
      (fun w : Phase ι d => dist (w.1 i) (w.1 j) ^ 3) z := hd.pow 3
  have hpow_ne : dist (z.1 i) (z.1 j) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt hpos)
  have hinv := hpow.inv hpow_ne
  have heq : (fun w : Phase ι d => inverseCubeDistance w.1 i j) =ᶠ[nhds z]
      (fun w => (dist (w.1 i) (w.1 j) ^ 3)⁻¹) := by
    filter_upwards [] with w
    simp [inverseCubeDistance, zpow_neg]
  exact hinv.congr_of_eventuallyEq heq

theorem forceTerm_contDiffAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (G : ℝ) (m : ι → ℝ) (z : Phase ι d) (i j : ι)
    (hcollision : z.1 i ≠ z.1 j) :
    ContDiffAt ℝ 1
      (fun w : Phase ι d =>
        (G * m j * inverseCubeDistance w.1 i j) • (w.1 j - w.1 i)) z := by
  have hinv := inverseCubeDistance_contDiffAt z i j hcollision
  have hconst : ContDiffAt ℝ 1 (fun _ : Phase ι d => G * m j) z := by
    fun_prop
  have hscalar : ContDiffAt ℝ 1
      (fun w : Phase ι d => G * m j * inverseCubeDistance w.1 i j) z :=
    hconst.mul hinv
  have hvector : ContDiffAt ℝ 1
      (fun w : Phase ι d => w.1 j - w.1 i) z := by fun_prop
  exact hscalar.smul hvector

theorem vectorField_contDiffAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (G : ℝ) (m : ι → ℝ) (z : Phase ι d)
    (hcf : CollisionFree z.1) :
    ContDiffAt ℝ 1 (fun w : Phase ι d => vectorField G m w) z := by
  classical
  change ContDiffAt ℝ 1
    (fun w : Phase ι d => (w.2, fun i => acceleration G m w.1 i)) z
  apply ContDiffAt.prodMk
  · fun_prop
  · rw [contDiffAt_pi]
    intro i
    have hterms (j : ι) : ContDiffAt ℝ 1
        (fun w : Phase ι d => if j = i then 0 else
          (G * m j * inverseCubeDistance w.1 i j) • (w.1 j - w.1 i)) z := by
      by_cases hij : j = i
      · simpa [hij] using
          (by fun_prop : ContDiffAt ℝ 1 (fun _ : Phase ι d =>
            (0 : EuclideanSpace ℝ (Fin d))) z)
      · simp only [if_neg hij]
        exact forceTerm_contDiffAt G m z i j (hcf i j (Ne.symm hij))
    simpa [acceleration] using
      (ContDiffAt.sum (s := Finset.univ) (fun j hj => hterms j))

end

end NBody
