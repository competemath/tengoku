/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Campanato
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.FarOscillation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Subordination

/-!
# Subordinated Base

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

lemma positive_shell_exists {z w : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hRρ : R ≤ parabolicRho₂ z w) :
    ∃ k : ℕ, w ∈ parabolicRieszShell R (k : ℤ) z := by
  exact _root_.CKN.Foundation.Parabolic.Morrey.exists_positive_shell hR hRρ

lemma shell_scale_sixtyfour {z w : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    w ∈ parabolicRieszShell (64 * r) (n : ℤ) z ↔
      w ∈ parabolicRieszShell r (n + 6 : ℤ) z := by
  constructor <;> intro hw
  · rcases hw with ⟨hlo, hhi⟩
    apply mem_parabolicRieszShell
    · convert hlo using 1;
        rw [Int.cast_add, show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num,
          ← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < 2)];
        norm_num
    · convert hhi using 1;
        rw [Int.cast_add, show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num,
          ← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < 2)];
        norm_num; ring_nf; simp [hr.ne']
  · rcases hw with ⟨hlo, hhi⟩
    apply mem_parabolicRieszShell
    · convert hlo using 1;
        rw [Int.cast_add, show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num,
          ← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < 2)];
        norm_num
    · convert hhi using 1;
        rw [Int.cast_add, show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num,
          ← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < 2)];
        norm_num; ring_nf; simp [hr.ne']

theorem heatPotential_near_far_cover {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (Set.univ : Set ParabolicPoint) = heatPotentialNearSet z r ∪
      ⋃ j : ℕ, heatPotentialFarShellSet z r j := by
  apply Subset.antisymm (fun w _ => ?_) (fun w _ => mem_univ w)
  by_cases hnear : parabolicRho₂ z w < 64 * r
  · exact Or.inl hnear
  · right
    have hR : 0 < 64 * r := by positivity
    have hρ : 0 < parabolicRho₂ z w :=
      lt_of_lt_of_le hR (le_of_not_gt hnear)
    obtain ⟨n, hn⟩ := positive_shell_exists hR (le_of_not_gt hnear)
    exact mem_iUnion.mpr ⟨n, (shell_scale_sixtyfour hr n).mp hn⟩

theorem heatPotential_near_far_disjoint {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (j : ℕ) : Disjoint (heatPotentialNearSet z r)
      (heatPotentialFarShellSet z r j) := by
  rw [Set.disjoint_left]
  intro w hwN hwS
  change parabolicRho₂ z w < 64 * r at hwN
  change w ∈ parabolicRieszShell r (j + 6 : ℤ) z at hwS
  have hwS' := hwS.1
  have hpow : (2 : ℝ) ^ (6 : ℝ) ≤ (2 : ℝ) ^ (((j + 6 : ℤ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num [Int.cast_add]
  have hrad : 64 * r ≤ (2 : ℝ) ^ (((j + 6 : ℤ) : ℝ)) * r := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_right hpow hr.le
  exact (not_lt_of_ge (hrad.trans hwS')) hwN

theorem heatPotential_far_shells_pairwise_disjoint {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) :
    Pairwise (Function.onFun Disjoint (heatPotentialFarShellSet z r)) := by
  intro j k hjk
  change Disjoint (heatPotentialFarShellSet z r j)
    (heatPotentialFarShellSet z r k)
  rw [Set.disjoint_left]
  intro w hwj hwk
  change w ∈ parabolicRieszShell r (j + 6 : ℤ) z at hwj
  change w ∈ parabolicRieszShell r (k + 6 : ℤ) z at hwk
  rcases lt_or_gt_of_ne hjk with hjk' | hkj'
  · have hexp : ((j : ℕ) + 6 : ℤ) + 1 ≤ (k + 6 : ℤ) := by
      omega
    have hexp' : (((j : ℕ) + 6 : ℤ) : ℝ) + 1 ≤ ((k + 6 : ℤ) : ℝ) := by
      exact_mod_cast hexp
    have hpow : (2 : ℝ) ^ ((((j : ℕ) + 6 : ℤ) : ℝ) + 1) ≤
        (2 : ℝ) ^ (((k + 6 : ℤ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp'
    have hrad := mul_le_mul_of_nonneg_right hpow hr.le
    exact (not_lt_of_ge (hrad.trans hwk.1)) hwj.2
  · have hexp : ((k : ℕ) + 6 : ℤ) + 1 ≤ (j + 6 : ℤ) := by
      omega
    have hexp' : (((k : ℕ) + 6 : ℤ) : ℝ) + 1 ≤ ((j + 6 : ℤ) : ℝ) := by
      exact_mod_cast hexp
    have hpow : (2 : ℝ) ^ ((((k : ℕ) + 6 : ℤ) : ℝ) + 1) ≤
        (2 : ℝ) ^ (((j + 6 : ℤ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp'
    have hrad := mul_le_mul_of_nonneg_right hpow hr.le
    exact (not_lt_of_ge (hrad.trans hwj.1)) hwk.2

lemma rhoTwo_eq_parabolicRho₂ {z w : ParabolicPoint}
    {ht : 0 < z.2 - w.2} :
    rhoTwo (z.1 - w.1) (z.2 - w.2) = parabolicRho₂ z w := by
  unfold rhoTwo parabolicRho₂
  rw [abs_of_pos ht]
  ring

lemma parabolicRho₂_pos_of_time {z w : ParabolicPoint}
    {ht : 0 < z.2 - w.2} : 0 < parabolicRho₂ z w := by
  unfold parabolicRho₂
  exact add_pos_of_pos_of_nonneg
    (Real.sqrt_pos.2 (abs_pos.mpr (ne_of_gt ht)))
    (vec3EuclideanNorm_nonneg _)

theorem heatPotentialKernel_abs_le_riesz₂ (z w : ParabolicPoint) :
    |heatPotentialKernel z w| ≤
      1000 * (parabolicRieszKernel 2 z w).toReal := by
  by_cases ht : 0 < z.2 - w.2
  · rw [heatPotentialKernel, pointSub]
    simp only [heatKernelPlus]
    rw [ite_eq_left ht]
    have hρ : 0 < parabolicRho₂ z w := parabolicRho₂_pos_of_time
      (z := z) (w := w) (ht := ht)
    have hright : (1000 / parabolicRho₂ z w ^ 3 : ℝ) =
        1000 * (parabolicRieszKernel 2 z w).toReal := by
      unfold parabolicRieszKernel
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (le_of_lt hρ)]
      rw [show -(5 - (2 : ℝ)) = -(3 : ℝ) by norm_num]
      rw [Real.rpow_neg (le_of_lt hρ)]
      simp [div_eq_mul_inv]
    calc
      |heatKernel (z.1 - w.1) (z.2 - w.2)| =
          heatKernel (z.1 - w.1) (z.2 - w.2) :=
        abs_of_nonneg (heatKernel_nonneg _ _)
      _ ≤ 1000 / rhoTwo (z.1 - w.1) (z.2 - w.2) ^ 3 :=
        heatKernel_le_rho_inv_cube ht
      _ = 1000 * (parabolicRieszKernel 2 z w).toReal := by
        rw [rhoTwo_eq_parabolicRho₂ (z := z) (w := w) (ht := ht), hright]
  · rw [heatPotentialKernel, pointSub]
    simp only [heatKernelPlus]
    rw [ite_eq_right ht, abs_zero]
    positivity

theorem heatPotentialSpatialKernel_abs_le_riesz₁ (i : Fin 3)
    (z w : ParabolicPoint) :
    |heatPotentialSpatialKernel i z w| ≤
      300000 * (parabolicRieszKernel 1 z w).toReal := by
  by_cases ht : 0 < z.2 - w.2
  · rw [heatPotentialSpatialKernel]
    have hρ : 0 < parabolicRho₂ z w := parabolicRho₂_pos_of_time
      (z := z) (w := w) (ht := ht)
    have hright : (300000 / parabolicRho₂ z w ^ 4 : ℝ) =
        300000 * (parabolicRieszKernel 1 z w).toReal := by
      unfold parabolicRieszKernel
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (le_of_lt hρ)]
      rw [show -(5 - (1 : ℝ)) = -(4 : ℝ) by norm_num]
      rw [Real.rpow_neg (le_of_lt hρ)]
      simp [div_eq_mul_inv]
    have hcomponent :
        |heatKernelSpaceDerivative (z.1 - w.1) (z.2 - w.2) i| ≤
          heatKernelGradientNorm (z.1 - w.1) (z.2 - w.2) := by
      unfold heatKernelGradientNorm
      exact Finset.single_le_sum
        (fun j _hj => abs_nonneg (heatKernelSpaceDerivative
          (z.1 - w.1) (z.2 - w.2) j)) (Finset.mem_univ i)
    have hgrad := heatKernelGradientNorm_le_rho_inv_four
      (x := z.1 - w.1) (t := z.2 - w.2) ht
    calc
      |heatKernelSpaceDerivative (z.1 - w.1) (z.2 - w.2) i| ≤
          heatKernelGradientNorm (z.1 - w.1) (z.2 - w.2) := hcomponent
      _ ≤ 300000 / rhoTwo (z.1 - w.1) (z.2 - w.2) ^ 4 := hgrad
      _ = 300000 * (parabolicRieszKernel 1 z w).toReal := by
        rw [rhoTwo_eq_parabolicRho₂ (z := z) (w := w) (ht := ht), hright]
  · rw [heatPotentialSpatialKernel, heatKernelSpaceDerivative]
    rw [ite_eq_right ht, abs_zero]
    positivity

lemma heatPotential_rho_zero_null (z : ParabolicPoint) :
    volume {w : ParabolicPoint | parabolicRho₂ z w = 0} = 0 := by
  apply measure_mono_null (parabolicRho₂_zero_subset_singleton z)
  rcases z with ⟨z, t₀⟩
  change (volume : Measure (Vec3 × ℝ)) ({(z, t₀)} : Set (Vec3 × ℝ)) = 0
  have hset : ({(z, t₀)} : Set (Vec3 × ℝ)) = {z} ×ˢ {t₀} := by
    ext w
    rcases w with ⟨x, t⟩
    simp only [mem_singleton_iff, mem_prod]
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨hx, ht⟩
      exact Prod.ext hx ht
  rw [hset]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
    ({z} ×ˢ {t₀}) = 0
  rw [Measure.prod_prod]
  simp

lemma heatPotential_near_riesz_le_shells
    {F : ParabolicPoint → ℝ} {z : ParabolicPoint} {R β : ℝ}
    (hR : 0 < R) :
    (∫⁻ w in {w | parabolicRho₂ z w < R},
      parabolicRieszKernel β z w * ENNReal.ofReal |F w|) ≤
      ∑' n : ℕ, ∫⁻ w in parabolicRieszShell R (Int.negSucc n) z,
        parabolicRieszKernel β z w * ENNReal.ofReal |F w| := by
  let s₀ : Set ParabolicPoint := {w | parabolicRho₂ z w = 0}
  let s : ℕ → Set ParabolicPoint :=
    fun n => parabolicRieszShell R (Int.negSucc n) z
  let g : ParabolicPoint → ℝ≥0∞ := fun w =>
    parabolicRieszKernel β z w * ENNReal.ofReal |F w|
  have hcover : {w | parabolicRho₂ z w < R} ⊆ s₀ ∪ ⋃ n, s n := by
    intro w hw
    by_cases hzero : parabolicRho₂ z w = 0
    · exact Or.inl hzero
    · have hpos : 0 < parabolicRho₂ z w :=
        lt_of_le_of_ne (parabolicRho₂_nonneg z w) (Ne.symm hzero)
      obtain ⟨k, hk, hmem⟩ := exists_shell_of_pos_lt hR hpos hw
      obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hk
      subst k
      exact Or.inr (mem_iUnion.mpr ⟨n, hmem⟩)
  have hzero : ∫⁻ w in s₀, g w = 0 := by
    rw [show (∫⁻ w in s₀, g w) =
      ∫⁻ w, g w ∂volume.restrict s₀ by rfl,
      Measure.restrict_eq_zero.mpr (by
        simpa [s₀] using heatPotential_rho_zero_null z),
      lintegral_zero_measure]
  calc
    (∫⁻ w in {w | parabolicRho₂ z w < R}, g w) ≤
        ∫⁻ w in s₀ ∪ ⋃ n, s n, g w := lintegral_mono_set hcover
    _ ≤ (∫⁻ w in s₀, g w) +
        ∫⁻ w in ⋃ n, s n, g w := lintegral_union_le _ _ _
    _ = ∫⁻ w in ⋃ n, s n, g w := by rw [hzero, zero_add]
    _ ≤ ∑' n : ℕ, ∫⁻ w in s n, g w := lintegral_iUnion_le s g
    _ = ∑' n : ℕ, ∫⁻ w in parabolicRieszShell R (Int.negSucc n) z,
        parabolicRieszKernel β z w * ENNReal.ofReal |F w| := by rfl

lemma heatPotential_near_riesz_scale {β θ R : ℝ} {n : ℕ}
    (hR : 0 < R) :
    (ENNReal.ofReal ((2 : ℝ) ^ ((Int.negSucc n : ℝ)) * R)) ^ (-(5 - β)) *
      (ENNReal.ofReal (2 * ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R))) ^
        (5 * (1 - 1 / θ)) =
      (ENNReal.ofReal 2) ^ (10 - β - 5 / θ) *
        ((ENNReal.ofReal 2) ^ (-(β - 5 / θ))) ^ n *
          (ENNReal.ofReal R) ^ (β - 5 / θ) := by
  have h2 : 0 < (2 : ℝ) := by norm_num
  have ha : 0 < (2 : ℝ) ^ (Int.negSucc n : ℝ) * R := by positivity
  have hb : 0 < 2 * ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R) := by positivity
  let a : ℝ := -(5 - β)
  let b : ℝ := 5 * (1 - 1 / θ)
  let d : ℝ := β - 5 / θ
  have hreal :
      ((2 : ℝ) ^ (Int.negSucc n : ℝ) * R) ^ a *
          (2 * ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R)) ^ b =
        2 ^ (10 - β - 5 / θ) * (2 ^ (-d)) ^ n * R ^ d := by
    let k : ℝ := Int.negSucc n
    have hk : k = -(n : ℝ) - 1 := by
      dsimp [k]
      rw [Int.cast_negSucc]
      push_cast
      ring
    dsimp [a, b, d]
    rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) ^ (Int.negSucc n : ℝ)) hR.le]
    rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ (2 : ℝ) ^
      ((Int.negSucc n : ℝ) + 1) * R)]
    rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1)) hR.le]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    have hk' : (Int.negSucc n : ℝ) = -(n : ℝ) - 1 := by exact hk
    rw [hk']
    have h2pow :
        (2 : ℝ) ^ ((-(n : ℝ) - 1) * (-(5 - β))) *
            (2 : ℝ) ^ (5 * (1 - 1 / θ) +
              (-(n : ℝ)) * (5 * (1 - 1 / θ))) =
          (2 : ℝ) ^ (10 - β - 5 / θ) *
            (2 : ℝ) ^ (-(β - 5 / θ) * (n : ℝ)) := by
      calc
        _ = (2 : ℝ) ^ (((-(n : ℝ) - 1) * (-(5 - β))) +
            (5 * (1 - 1 / θ) + (-(n : ℝ)) * (5 * (1 - 1 / θ)))) := by
          rw [← Real.rpow_add h2]
        _ = (2 : ℝ) ^ ((10 - β - 5 / θ) +
            (-(β - 5 / θ) * (n : ℝ))) := by
          congr 1
          ring
        _ = _ := by
          rw [Real.rpow_add h2]
    have hshift : -(n : ℝ) - 1 + 1 = -(n : ℝ) := by ring
    rw [hshift]
    calc
      _ = ((2 : ℝ) ^ ((-(n : ℝ) - 1) * (-(5 - β))) *
          (2 : ℝ) ^ (5 * (1 - 1 / θ)) *
          (2 : ℝ) ^ ((-(n : ℝ)) * (5 * (1 - 1 / θ)))) *
          (R ^ (-(5 - β)) * R ^ (5 * (1 - 1 / θ))) := by ring
      _ = (2 : ℝ) ^ (10 - β - 5 / θ) *
          (2 : ℝ) ^ (-(β - 5 / θ) * (n : ℝ)) *
          (R ^ (-(5 - β)) * R ^ (5 * (1 - 1 / θ))) := by
        calc
          _ = ((2 : ℝ) ^ ((-(n : ℝ) - 1) * (-(5 - β))) *
              (2 : ℝ) ^ (5 * (1 - 1 / θ) +
                (-(n : ℝ)) * (5 * (1 - 1 / θ)))) *
              (R ^ (-(5 - β)) * R ^ (5 * (1 - 1 / θ))) := by
            rw [Real.rpow_add h2]
            ring
          _ = _ := by rw [h2pow]
      _ = (2 : ℝ) ^ (10 - β - 5 / θ) *
          (2 ^ (-(β - 5 / θ))) ^ n * R ^ (β - 5 / θ) := by
        have hn : (2 : ℝ) ^ (-(β - 5 / θ) * (n : ℝ)) =
            (2 ^ (-(β - 5 / θ))) ^ n := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h2)]
        have hRpow : R ^ (-(5 - β)) * R ^ (5 * (1 - 1 / θ)) =
            R ^ (β - 5 / θ) := by
          rw [← Real.rpow_add hR]
          congr 1
          ring
        rw [hn, hRpow]
  rw [ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos hb]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤
    ((2 : ℝ) ^ (Int.negSucc n : ℝ) * R) ^ (-(5 - β)))]
  rw [hreal]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_rpow_of_pos h2]
  rw [ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_rpow_of_pos h2]
  rw [ENNReal.ofReal_rpow_of_pos hR]

lemma heatPotential_riesz_ne_top_of_pos {β : ℝ} {z w : ParabolicPoint}
    (hρ : 0 < parabolicRho₂ z w) : parabolicRieszKernel β z w ≠ ∞ := by
  unfold parabolicRieszKernel
  by_cases he : 0 ≤ -(5 - β)
  · exact ENNReal.rpow_ne_top_of_nonneg he ENNReal.ofReal_ne_top
  · rw [ENNReal.rpow_neg]
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hρ)
      ENNReal.ofReal_ne_top).ne'

theorem heatPotential_far_shell_source_factor_toReal
    {F : ParabolicPoint → ℝ} {r P θ : ℝ}
    (hr : 0 < r) (_ : AEMeasurable F volume) (_ : morreyNorm P θ F < ∞)
    (j : ℕ) :
    ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ F).toReal =
      (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r)) ^
          (5 * (1 - 1 / θ)) *
        (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ F).toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma heatPotential_far_scale_first
    {a r c : ℝ} {m j : ℕ} (hr : 0 < r) :
    2 * r * (c / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ m) *
        (2 * ((2 : ℝ) ^ ((j : ℝ) + 7) * r)) ^ a =
      (2 * c) * (2 : ℝ) ^ (8 * a - 4 * (m : ℝ)) *
        (2 : ℝ) ^ ((j : ℝ) * (a - m)) * r ^ (a + 1 - m) := by
  have hr0 : 0 ≤ r := hr.le
  have hden : ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ m =
      (2 : ℝ) ^ (((j : ℝ) + 4) * (m : ℝ)) * r ^ m := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) + 7) * r)]
  rw [hden]
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) + 7)) hr0]
  have hsource : (2 : ℝ) ^ a *
      (((2 : ℝ) ^ ((j : ℝ) + 7)) ^ a * r ^ a) =
      (2 : ℝ) ^ (a + ((j : ℝ) + 7) * a) * r ^ a := by
    rw [← Real.rpow_mul (by norm_num)]
    calc
      _ = ((2 : ℝ) ^ a *
          (2 : ℝ) ^ (((j : ℝ) + 7) * a)) * r ^ a := by ring
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [hsource]
  have hrpow : r ^ (a + 1) = r * r ^ a := by
    rw [Real.rpow_add hr]
    norm_num
    ring
  rw [Real.rpow_sub hr]
  have h2pow : (2 : ℝ) ^ (a * (1 + ((j : ℝ) + 7))) =
      (2 : ℝ) ^ (((j : ℝ) + 4) * (m : ℝ)) *
        (2 : ℝ) ^ (8 * a - 4 * (m : ℝ)) *
        (2 : ℝ) ^ ((j : ℝ) * (a - m)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  field_simp
  rw [h2pow, hrpow]
  norm_num
  ring_nf

lemma heatPotential_far_scale_second
    {a r c : ℝ} {m j : ℕ} (hr : 0 < r) :
    2 * r * (2 * r * (c / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ m)) *
        (2 * ((2 : ℝ) ^ ((j : ℝ) + 7) * r)) ^ a =
      (4 * c) * (2 : ℝ) ^ (8 * a - 4 * (m : ℝ)) *
        (2 : ℝ) ^ ((j : ℝ) * (a - m)) * r ^ (a + 2 - m) := by
  have hbase := heatPotential_far_scale_first
    (a := a) (r := r) (c := 2 * c) (m := m) (j := j) hr
  have hrpow : r ^ (a + 2 - m) = r ^ (a + 1 - m) * r := by
    calc
      r ^ (a + 2 - m) = r ^ ((a + 1 - m) + 1) := by
        congr 1
        ring
      _ = r ^ (a + 1 - m) * r ^ (1 : ℝ) := Real.rpow_add hr _ _
      _ = r ^ (a + 1 - m) * r := by norm_num
  calc
    _ = (2 * r * ((2 * c) / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ m) *
        (2 * ((2 : ℝ) ^ ((j : ℝ) + 7) * r)) ^ a) * r := by
      field_simp
    _ = ((2 * (2 * c)) * (2 : ℝ) ^ (8 * a - 4 * (m : ℝ)) *
        (2 : ℝ) ^ ((j : ℝ) * (a - m)) * r ^ (a + 1 - m)) * r := by
      rw [hbase]
    _ = _ := by rw [hrpow]; ring

end CKN.Core.HeatPotential
