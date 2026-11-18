import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_order_sum_algebraMap_mul_coeffMap.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`, 3 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_order_sum_algebraMap_mul_coeffMap

set_option autoImplicit false

open _root_.AlgebraicCurve open _root_.ModularCurve

namespace HahnSeries export _root_.HahnSeries (coeff_sum coeff_single_zero_mul order ne_zero_of_coeff_ne_zero coeff order_le_of_coeff_ne_zero coeff_eq_zero_of_lt_order coeff_order_eq_zero) end HahnSeries
open scoped _root_.HahnSeries in

private theorem HahnSeries.ne_zero_and_order_eq_of_coeff {Γ R : Type*} [Zero Γ] [LinearOrder Γ]
    [Zero R] (x : HahnSeries Γ R) (m : Γ) (h1 : x.coeff m ≠ 0) (h2 : ∀ k < m, x.coeff k = 0) :
    x ≠ 0 ∧ x.order = m := by
  have hx : x ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine ⟨hx, le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_⟩
  exact not_lt.mp fun hlt => (HahnSeries.coeff_order_eq_zero.not.2 hx) (h2 _ hlt)

namespace ModularCurve export _root_.ModularCurve (coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single) end ModularCurve
open scoped _root_.ModularCurve in

private theorem ModularCurve.coeff_sum_algebraMap_mul_coeffMap
    {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') {ι : Type*} (s : Finset ι)
    (c : ι → K') (f : ι → LaurentSeries K) (k : ℤ) :
    (∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (f i)).coeff k
      = ∑ i ∈ s, σ ((f i).coeff k) * c i := by
  rw [HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, coeffMap_coeff,
    mul_comm]

open scoped _root_.ModularCurve in
private theorem ModularCurve.order_sum_algebraMap_mul_coeffMap
    {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (c : ι → K') (hc : ∀ a : ι → K, ∑ i ∈ s, σ (a i) * c i = 0 → ∀ i ∈ s, a i = 0)
    (f : ι → LaurentSeries K) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (f i)) ≠ 0 ∧
      (∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (f i)).order
        = s.inf' hs (fun i => (f i).order) := by

  obtain ⟨i₀, hi₀, hmi₀⟩ := Finset.exists_mem_eq_inf' hs (fun i => (f i).order)
  refine HahnSeries.ne_zero_and_order_eq_of_coeff _ _ ?_ ?_
  ·
    intro h0
    rw [ModularCurve.coeff_sum_algebraMap_mul_coeffMap] at h0
    have hzero := hc (fun i => (f i).coeff (s.inf' hs (fun i => (f i).order))) h0 i₀ hi₀
    apply (HahnSeries.coeff_order_eq_zero.not.2 (hf i₀ hi₀))
    rw [← hmi₀]
    exact hzero
  ·
    intro k hk
    rw [ModularCurve.coeff_sum_algebraMap_mul_coeffMap]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk (Finset.inf'_le _ hi)),
      map_zero, zero_mul]

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_order_sum_algebraMap_mul_coeffMap.ModularCurve in

theorem solution {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (c : ι → K') (hc : ∀ a : ι → K, ∑ i ∈ s, σ (a i) * c i = 0 → ∀ i ∈ s, a i = 0)
    (f : ι → LaurentSeries K) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (f i)) ≠ 0 ∧
      (∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (f i)).order
        = s.inf' hs (fun i => (f i).order) :=
  ModularCurve.order_sum_algebraMap_mul_coeffMap σ s hs c hc f hf

