import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod

set_option autoImplicit false

open Filter Topology

namespace R5

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}

/--
@isnad1 id=ex.2h5v.s7.dc39fe4f1c15 from=translated src=- shape=4ff02136 vocab=549079c1
-/
theorem exists_neg_of_prod_neg
    {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hprod : meromorphicOrderAt (∏ i ∈ s, f i) x < 0) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  by_contra h
  push Not at h
  have hsum : (0 : WithTop ℤ) ≤ ∑ i ∈ s, meromorphicOrderAt (f i) x :=
    Finset.sum_nonneg h
  rw [meromorphicOrderAt_prod hf] at hprod
  exact absurd (lt_of_le_of_lt hsum hprod) (lt_irrefl _)

/--
@isnad1 id=ex.3h6v.s7.5c387bf4ad9b from=translated src=- shape=efec1110 vocab=200da796
-/
theorem exists_neg_of_prod_eventuallyEq
    {s : Finset ι} {f : ι → 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hfg : ∀ᶠ z in 𝓝[≠] x, (∏ i ∈ s, f i z) = g z)
    (hg : meromorphicOrderAt g x < 0) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  refine exists_neg_of_prod_neg hf ?_
  have : (∏ i ∈ s, f i) =ᶠ[𝓝[≠] x] g := by
    filter_upwards [hfg] with z hz
    simpa [Finset.prod_apply] using hz
  rwa [meromorphicOrderAt_congr this]

end R5

open Filter Topology in

/--
@isnad1 id=ex.6h7v.s8.2ee7a8d29be4 from=translated src=- shape=3ffeac16 vocab=39d2408a
-/
theorem R5.single
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}
    {s : Finset ι} {f : ι → 𝕜 → 𝕜} {p h : 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hp : MeromorphicAt p x) (hpole : meromorphicOrderAt p x < 0)
    (hh : AnalyticAt 𝕜 h x) (hh0 : h x ≠ 0)
    (hfg : ∀ᶠ z in nhdsWithin x {x}ᶜ, (∏ i ∈ s, f i z) = p z * h z) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  refine R5.exists_neg_of_prod_eventuallyEq hf hfg ?_
  have hh' : meromorphicOrderAt h x = 0 := by
    rw [hh.meromorphicOrderAt_eq, hh.analyticOrderAt_eq_zero.mpr hh0]
    rfl
  have hmul : meromorphicOrderAt (p * h) x = meromorphicOrderAt p x + meromorphicOrderAt h x :=
    meromorphicOrderAt_mul hp hh.meromorphicAt
  show meromorphicOrderAt (fun z => p z * h z) x < 0
  have : (fun z => p z * h z) = p * h := rfl
  rw [this, hmul, hh', add_zero]
  exact hpole

open Filter Topology in
/--
@isnad1 id=ex.6h9v.s8.6fcc69ba3590 from=translated src=- shape=1e7ed733 vocab=39d2408a
-/
theorem solution
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι κ : Type*}
    {s : Finset ι} {t : Finset κ} {f : ι → 𝕜 → 𝕜} {p : 𝕜 → 𝕜} {h : κ → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hp : MeromorphicAt p x) (hpole : meromorphicOrderAt p x < 0)
    (hh : ∀ j ∈ t, AnalyticAt 𝕜 (h j) x) (hh0 : ∀ j ∈ t, h j x ≠ 0)
    (hfg : ∀ᶠ z in nhdsWithin x {x}ᶜ, (∏ i ∈ s, f i z) = p z * ∏ j ∈ t, h j z) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by
  refine R5.single (h := fun z => ∏ j ∈ t, h j z) hf hp hpole
    (Finset.analyticAt_fun_prod t hh) ?_ hfg
  exact Finset.prod_ne_zero_iff.mpr hh0
