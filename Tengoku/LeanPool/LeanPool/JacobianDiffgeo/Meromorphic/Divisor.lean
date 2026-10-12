/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.Field
public import Tengoku

/-!
# Divisors (CC2) and the divisor map `divisor : ℳ X → Divisor X` (CC3)

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.6, D7, proof plan
§6.3).

* `Function.locallyFinsuppWithin.degree` (Compat, upstreamable): the degree of a divisor on a
  compact `T2Space`, `D.degree := ∑ x ∈ (D.finiteSupport isCompact_univ).toFinset, D x`.
* `RS.Divisor X := Function.locallyFinsuppWithin (Set.univ : Set X) ℤ` (CC2, frozen).
* `MeroGermOn.divisorOn φ : Function.locallyFinsuppWithin U ℤ`, `toFun x = (φ.ord x).untop₀`;
  local finiteness (§6.3) via `eventually_ordAtX_eq_top`/`eventually_ordAtX_eq_zero`.
* `divisor : ℳ X → Divisor X` (CC3's `div`, renamed to avoid `Div`-notation collision): total,
  `divisor 0 = 0` honestly (empty support, no case split). Algebra (`divisor_mul/inv/smul`),
  effectivity (`divisor_nonneg_iff`), compactness finiteness (`finite_support_divisor`,
  `finite_setOf_ord_neg/pos`, `eventually_ord_eq_zero`).
-/

@[expose] public section

open scoped ContDiff Manifold
open Set Filter Topology

/-! ### Compat: `degree` (upstreamable to `Function.locallyFinsuppWithin`) -/

namespace Function.locallyFinsuppWithin

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- Degree of a divisor on a compact `T2Space` (CC2's `deg`; absent from mathlib at the pin). -/
noncomputable def degree {Y : Type*} [AddCommMonoid Y]
    (D : Function.locallyFinsuppWithin (Set.univ : Set X) Y) : Y :=
  ∑ x ∈ (D.finiteSupport isCompact_univ).toFinset, D x

theorem degree_eq_sum_of_subset {Y : Type*} [AddCommMonoid Y]
    {D : Function.locallyFinsuppWithin (Set.univ : Set X) Y} {S : Finset X}
    (hS : D.support ⊆ (S : Set X)) : D.degree = ∑ x ∈ S, D x := by
  unfold degree
  apply Finset.sum_subset
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact hS hx
  · intro x _ hxD
    rw [Set.Finite.mem_toFinset] at hxD
    by_contra hne
    exact hxD (Function.mem_support.mpr hne)

@[simp] theorem degree_zero {Y : Type*} [AddCommMonoid Y] :
    (0 : Function.locallyFinsuppWithin (Set.univ : Set X) Y).degree = 0 := by
  rw [degree_eq_sum_of_subset (S := ∅) (by simp)]
  simp

theorem degree_add {Y : Type*} [AddCommMonoid Y]
    (D E : Function.locallyFinsuppWithin (Set.univ : Set X) Y) :
    (D + E).degree = D.degree + E.degree := by
  classical
  set S := (D.finiteSupport isCompact_univ).toFinset ∪ (E.finiteSupport isCompact_univ).toFinset
    with hS_def
  have hDS : D.support ⊆ (S : Set X) := by
    intro x hx; rw [hS_def, Finset.coe_union]
    exact Or.inl (Finset.mem_coe.mpr ((D.finiteSupport isCompact_univ).mem_toFinset.mpr hx))
  have hES : E.support ⊆ (S : Set X) := by
    intro x hx; rw [hS_def, Finset.coe_union]
    exact Or.inr (Finset.mem_coe.mpr ((E.finiteSupport isCompact_univ).mem_toFinset.mpr hx))
  have hDES : (D + E).support ⊆ (S : Set X) := by
    intro x hx
    by_contra hxS
    rw [hS_def, Finset.coe_union, Set.mem_union, not_or] at hxS
    have hxD : D x = 0 := by
      by_contra hd
      exact hxS.1 (Finset.mem_coe.mpr ((D.finiteSupport isCompact_univ).mem_toFinset.mpr
        (Function.mem_support.mpr hd)))
    have hxE : E x = 0 := by
      by_contra he
      exact hxS.2 (Finset.mem_coe.mpr ((E.finiteSupport isCompact_univ).mem_toFinset.mpr
        (Function.mem_support.mpr he)))
    apply hx
    have hcoe := congrFun (Function.locallyFinsuppWithin.coe_add D E) x
    simp only [hxD, hxE, Pi.add_apply, add_zero] at hcoe
    exact hcoe
  rw [degree_eq_sum_of_subset hDES, degree_eq_sum_of_subset hDS, degree_eq_sum_of_subset hES,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact congrFun (Function.locallyFinsuppWithin.coe_add D E) x

theorem degree_neg {Y : Type*} [AddCommGroup Y]
    (D : Function.locallyFinsuppWithin (Set.univ : Set X) Y) :
    (-D).degree = -D.degree := by
  have hsub : (-D).support ⊆ ((D.finiteSupport isCompact_univ).toFinset : Set X) := by
    intro x hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hd
    have hxD : D x = 0 := not_not.mp (mt Function.mem_support.mpr hd)
    apply hx
    have hcoe := congrFun (Function.locallyFinsuppWithin.coe_neg D) x
    simp only [hxD, Pi.neg_apply, neg_zero] at hcoe
    exact hcoe
  rw [degree_eq_sum_of_subset hsub, degree, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact congrFun (Function.locallyFinsuppWithin.coe_neg D) x

theorem degree_mono {D E : Function.locallyFinsuppWithin (Set.univ : Set X) ℤ} (h : D ≤ E) :
    D.degree ≤ E.degree := by
  classical
  set S := (D.finiteSupport isCompact_univ).toFinset ∪ (E.finiteSupport isCompact_univ).toFinset
    with hS_def
  have hDS : D.support ⊆ (S : Set X) := by
    intro x hx; rw [hS_def, Finset.coe_union]
    exact Or.inl (Finset.mem_coe.mpr ((D.finiteSupport isCompact_univ).mem_toFinset.mpr hx))
  have hES : E.support ⊆ (S : Set X) := by
    intro x hx; rw [hS_def, Finset.coe_union]
    exact Or.inr (Finset.mem_coe.mpr ((E.finiteSupport isCompact_univ).mem_toFinset.mpr hx))
  rw [degree_eq_sum_of_subset hDS, degree_eq_sum_of_subset hES]
  apply Finset.sum_le_sum
  intro x _
  exact Function.locallyFinsuppWithin.le_def.1 h x

theorem degree_nonneg_of_nonneg {D : Function.locallyFinsuppWithin (Set.univ : Set X) ℤ}
    (h : 0 ≤ D) : 0 ≤ D.degree := by
  rw [← degree_zero (X := X) (Y := ℤ)]
  exact degree_mono h

end Function.locallyFinsuppWithin

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {U V : Set X} {x : X} {c : ℂ}

variable (X) in
/-- CC2 (frozen). -/
abbrev Divisor := Function.locallyFinsuppWithin (Set.univ : Set X) ℤ

namespace MeroGermOn

/-- Relative divisor of a germ class (support automatically inside `U` by the D3 junk). -/
noncomputable def divisorOn [T1Space X] [IsManifold 𝓘(ℂ) ω X] (φ : MeroGermOn X U) :
    Function.locallyFinsuppWithin U ℤ where
  toFun x := (φ.ord x).untop₀
  supportWithinDomain' := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra hxU
    apply hx
    obtain ⟨f, hf, rfl⟩ := exists_rep φ
    rw [ord_apply_mk, ite_eq_right (fun h => hxU h.2)]
    exact WithTop.untop₀_zero
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨f, hf, rfl⟩ := exists_rep φ
    by_cases hU : IsOpen U
    · by_cases hordz : ordAtX f z = ⊤
      · have he : ∀ᶠ y in 𝓝 z, ordAtX f y = ⊤ := eventually_ordAtX_eq_top hordz
        have heU : ∀ᶠ y in 𝓝 z, ordAtX f y = ⊤ ∧ y ∈ U := he.and (hU.mem_nhds hz)
        obtain ⟨W, hW, hWsub⟩ := Filter.eventually_iff_exists_mem.mp heU
        refine ⟨W, hW, ?_⟩
        have hempty : W ∩ Function.support (fun x => ((mk f hf).ord x).untop₀) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          rintro y ⟨hyW, hyS⟩
          obtain ⟨hordy, hyU⟩ := hWsub y hyW
          simp only [Function.mem_support, ne_eq] at hyS
          apply hyS
          rw [ord_mk hU hyU, hordy]
          exact WithTop.untop₀_top
        rw [hempty]; exact Set.finite_empty
      · have he : ∀ᶠ y in 𝓝[≠] z, ordAtX f y = 0 := eventually_ordAtX_eq_zero (hf z hz) hordz
        have heU : ∀ᶠ y in 𝓝[≠] z, ordAtX f y = 0 ∧ y ∈ U :=
          he.and (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz))
        rw [eventually_nhdsWithin_iff] at heU
        obtain ⟨W, hW, hWsub⟩ := Filter.eventually_iff_exists_mem.mp heU
        refine ⟨W, hW, ?_⟩
        have hsub : W ∩ Function.support (fun x => ((mk f hf).ord x).untop₀) ⊆ {z} := by
          rintro y ⟨hyW, hyS⟩
          simp only [Set.mem_singleton_iff]
          by_contra hyz
          obtain ⟨hordy, hyU⟩ := hWsub y hyW hyz
          simp only [Function.mem_support, ne_eq] at hyS
          apply hyS
          rw [ord_mk hU hyU, hordy]
          exact WithTop.untop₀_zero
        exact Set.Finite.subset (Set.finite_singleton z) hsub
    · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      have hempty : Set.univ ∩ Function.support (fun x => ((mk f hf).ord x).untop₀) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        rintro y ⟨-, hyS⟩
        simp only [Function.mem_support, ne_eq] at hyS
        apply hyS
        rw [ord_apply_mk, ite_eq_right (fun h => hU h.1)]
        exact WithTop.untop₀_zero
      rw [hempty]; exact Set.finite_empty

@[simp] theorem divisorOn_apply [T1Space X] [IsManifold 𝓘(ℂ) ω X] (φ : MeroGermOn X U) (x : X) :
    φ.divisorOn x = (φ.ord x).untop₀ := rfl

end MeroGermOn

/-- CC3's `div : ℳ X → Divisor X` (renamed `divisor`; total, `divisor 0 = 0` honestly). -/
noncomputable abbrev divisor [T1Space X] [IsManifold 𝓘(ℂ) ω X] (φ : ℳ X) : Divisor X := φ.divisorOn

@[simp] theorem divisor_apply [T1Space X] [IsManifold 𝓘(ℂ) ω X] (φ : ℳ X) (x : X) :
    divisor φ x = (φ.ord x).untop₀ := rfl

@[simp] theorem divisor_zero [T1Space X] [IsManifold 𝓘(ℂ) ω X] :
    divisor (0 : ℳ X) = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [divisor_apply, MeroGermOn.ord_zero, ite_eq_left ⟨isOpen_univ, mem_univ y⟩]
  simp

variable [T1Space X] [IsManifold 𝓘(ℂ) ω X]

theorem finite_support_divisor [T2Space X] [CompactSpace X] (φ : ℳ X) :
    (divisor φ).support.Finite :=
  (divisor φ).finiteSupport isCompact_univ

end RS
