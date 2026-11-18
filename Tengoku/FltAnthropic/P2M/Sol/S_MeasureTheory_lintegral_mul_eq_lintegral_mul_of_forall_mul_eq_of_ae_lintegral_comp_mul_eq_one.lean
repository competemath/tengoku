import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one

set_option autoImplicit false

open _root_.MeasureTheory
open scoped ENNReal

namespace MeasureTheory
export _root_.MeasureTheory (Measure lintegral_neg_eq_self SFinite lintegral_congr lintegral_mul_const lintegral_congr_ae lintegral_const_mul lintegral_lintegral_swap lintegral_mul_right_eq_self)
namespace SectionAveraging
open _root_.MeasureTheory

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace X] [MeasurableNeg X] in
/--
@isnad1 id=eq.1h3v.s6.777f02b8773a from=translated src=- shape=89416fb8 vocab=2f380a08
-/
theorem map_zero_of_forall_map_add (n : X → G) (hn : ∀ x y, n (x + y) = n x * n y) : n 0 = 1 := by
  have h := hn 0 0
  rw [add_zero] at h
  exact ((left_eq_mul.1 h).symm).symm

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace X] [MeasurableNeg X] in
/--
@isnad1 id=eq.1h4v.s6.0309ed429500 from=translated src=- shape=85439f9c vocab=d2365fb8
-/
theorem map_neg_mul (n : X → G) (hn : ∀ x y, n (x + y) = n x * n y) (x : X) : n (-x) * n x = 1 := by
  rw [← hn, neg_add_cancel, map_zero_of_forall_map_add n hn]

/--
@isnad1 id=eq.8h8v.s8.c18ad64719f7 from=translated src=- shape=4752c352 vocab=7cfe240a
-/
theorem main
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [μ.IsNegInvariant]
    (n : X → G) (hn : Measurable n) (hn_add : ∀ x y, n (x + y) = n x * n y)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦn : ∀ g x, Φ (g * n x) = Φ g)
    (w w₀ : G → ℝ≥0∞) (hw : Measurable w) (hw₀ : Measurable w₀)
    (h1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1) (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
    ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ := by
  have hF : Measurable fun p : G × X => w p.1 * Φ p.1 * w₀ (p.1 * n p.2) :=
    ((hw.comp measurable_fst).mul (hΦ.comp measurable_fst)).mul
      (hw₀.comp (measurable_fst.mul (hn.comp measurable_snd)))
  have hF' : Measurable fun p : G × X => w (p.1 * n (-p.2)) * Φ p.1 * w₀ p.1 :=
    ((hw.comp (measurable_fst.mul (hn.comp measurable_snd.neg))).mul (hΦ.comp measurable_fst)).mul
      (hw₀.comp measurable_fst)
  calc ∫⁻ g, w g * Φ g ∂τ
      = ∫⁻ g, w g * Φ g * ∫⁻ x, w₀ (g * n x) ∂μ ∂τ :=
        lintegral_congr_ae (h1₀.mono fun g hg => by simp only [hg, mul_one])
    _ = ∫⁻ g, ∫⁻ x, w g * Φ g * w₀ (g * n x) ∂μ ∂τ := by
        refine lintegral_congr fun g => ?_
        have hm : Measurable fun x => w₀ (g * n x) := hw₀.comp ((measurable_const_mul g).comp hn)
        rw [lintegral_const_mul _ hm]
    _ = ∫⁻ x, ∫⁻ g, w g * Φ g * w₀ (g * n x) ∂τ ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ x, ∫⁻ g, w (g * n (-x)) * Φ g * w₀ g ∂τ ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_mul_right_eq_self (fun g => w g * Φ g * w₀ (g * n x)) (n (-x))]
        refine lintegral_congr fun g => ?_
        simp only [mul_assoc, map_neg_mul n hn_add, mul_one, hΦn]
    _ = ∫⁻ g, ∫⁻ x, w (g * n (-x)) * Φ g * w₀ g ∂μ ∂τ := (lintegral_lintegral_swap hF'.aemeasurable).symm
    _ = ∫⁻ g, (∫⁻ x, w (g * n (-x)) ∂μ) * (Φ g * w₀ g) ∂τ := by
        refine lintegral_congr fun g => ?_
        have hm : Measurable fun x => w (g * n (-x)) :=
          hw.comp ((measurable_const_mul g).comp (hn.comp measurable_neg))
        rw [← lintegral_mul_const _ hm]
        refine lintegral_congr fun x => ?_
        rw [mul_assoc]
    _ = ∫⁻ g, (∫⁻ x, w (g * n x) ∂μ) * (Φ g * w₀ g) ∂τ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_neg_eq_self (μ := μ) (fun x => w (g * n x))]
    _ = ∫⁻ g, w₀ g * Φ g ∂τ :=
        lintegral_congr_ae (h1.mono fun g hg => by simp only [hg, one_mul]; exact mul_comm _ _)

end MeasureTheory.SectionAveraging

/--
@isnad1 id=eq.8h8v.s8.c18ad64719f7 from=translated src=- shape=4752c352 vocab=7cfe240a
-/
theorem solution
    {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [μ.IsNegInvariant]
    (n : X → G) (hn : Measurable n) (hn_add : ∀ x y, n (x + y) = n x * n y)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦn : ∀ g x, Φ (g * n x) = Φ g)
    (w w₀ : G → ℝ≥0∞) (hw : Measurable w) (hw₀ : Measurable w₀)
    (h1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1) (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
    ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ :=
  MeasureTheory.SectionAveraging.main τ μ n hn hn_add Φ hΦ hΦn w w₀ hw hw₀ h1 h1₀
