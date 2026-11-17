/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.RepresentationTheory.Crystal.Path.RootOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The path crystals `B(π)` and `B(λ)`

For a Littelmann path `π`, let `B(π)` be the connected component of `π` in the crystal of all
paths, i.e. the smallest set of paths containing `π` and stable under all root operators `eᵢ`,
`fᵢ` ([Lit95] §2). For a dominant weight `λ` and the straight line path `π_λ(t) = tλ`,
Littelmann's theorem ([Lit95] Thm. 9.1, [Lit94]) states that the character of
`B(λ) := B(π_λ)` is the character of the irreducible integrable highest-weight module `L(λ)`.

## Main definitions

* `LittelmannPath.straightLine S λ`: the path `π_λ(t) = tλ`.
* `LittelmannPath.stringPath S λ i k`: the path `t ↦ tλ - min(nt, k) αᵢ` (`n = ⟨λ, αᵢ^∨⟩`).
* `LittelmannPath.component π`: the connected component `B(π)` of `π`.
* `LittelmannPath.componentCrystal π`: the crystal structure on `B(π)`.
* `LittelmannPath.fWord`, `LittelmannPath.fOrbit π`: the paths `f_{i₁} ⋯ f_{iₖ} π`.

## Main results

* `LittelmannPath.e_straightLine`, `LittelmannPath.φ_straightLine`: for dominant `λ`, `π_λ` is a
  highest weight element: `eᵢ π_λ = 0` and `φᵢ(π_λ) = ⟨λ, αᵢ^∨⟩`.
* `LittelmannPath.fIter_straightLine`: `fᵢ^k π_λ` is `LittelmannPath.stringPath S λ i k` for
  `0 ≤ k ≤ ⟨λ, αᵢ^∨⟩`; in particular `fᵢ^n π_λ = π_{rᵢ λ}` for `n = ⟨λ, αᵢ^∨⟩ ≥ 0`.
* `LittelmannPath.straightLine_reflection_mem_component`: `π_{rᵢ λ}` lies in the connected
  component of `π_λ`.
* `LittelmannPath.isSeminormal_componentCrystal`: `B(π)` is seminormal.
* `LittelmannPath.card_wt_reflection_component`: the number of paths of weight `rᵢ μ` in `B(π)`
  equals the number of paths of weight `μ` (Kashiwara's `Sᵢ`).
* `LittelmannPath.component_eq_fOrbit`, `LittelmannPath.exists_wt_eq_of_mem_component`,
  `LittelmannPath.finite_wt_component`: *if* the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under the
  `eⱼ`, then `B(π)` is this set, its weights lie in `wt π - Q₊`, and (for linearly independent
  simple roots and finitely many indices) each weight occurs finitely often.

## What remains

Littelmann's theorem that for `π` with image in the dominant chamber (e.g. `π = π_λ`) the set
`{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ` ([Lit95] §7, Cor. 1 c); in [Lit94] via
Lakshmibai–Seshadri paths) is not proved here; it is the hypothesis of
`LittelmannPath.component_eq_fOrbit`. Nor is the character formula `ch B(λ) = ch L(λ)`.

## References

* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
-/
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean
open Set

namespace Tengoku.LieLean.LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-! ### Straight line paths -/

variable (S) in
/-- The straight line path `π_λ(t) = tλ` ([Lit95] §1).-/
def straightLine (μ : X) : LittelmannPath S where
  toFun t := max 0 (min 1 t) • S.embed μ
  wt := μ
  toFun_of_nonpos' t ht := by
    rw [min_eq_right (ht.trans zero_le_one), max_eq_left ht, zero_smul]
  toFun_of_one_le' t ht := by rw [min_eq_left ht, max_eq_right zero_le_one, one_smul]
  continuous_coroot' i := by
    simp only [map_smul, smul_eq_mul]
    exact (continuous_const.max (continuous_const.min continuous_id)).mul continuous_const

variable {i : ι} {μ : X}

/--
@isnad1 id=eq.0h7v.s7.7ca89ca6848c from=translated src=- shape=2d342777 vocab=81bc8ea4
-/
@[simp] lemma wt_straightLine : (straightLine S μ).wt = μ := rfl

/--
@isnad1 id=eq.0h8v.s8.a6e4ecb3e135 from=translated src=- shape=446278f9 vocab=ca10d6b3
-/
lemma straightLine_apply (t : 𝕜) : straightLine S μ t = max 0 (min 1 t) • S.embed μ := rfl

/-! ### The `αᵢ`-string through a straight line path -/

variable (S) in
/-- For `0 ≤ k ≤ n = ⟨λ, αᵢ^∨⟩`, the path `t ↦ tλ - min(nt, k) αᵢ`; it is `fᵢ^k π_λ`
(`LittelmannPath.fIter_straightLine`).-/
def stringPath (μ : X) (i : ι) (k : ℕ) (hk : (k : ℤ) ≤ D.coroot i μ) : LittelmannPath S where
  toFun t := max 0 (min 1 t) • S.embed μ -
    min ((D.coroot i μ : 𝕜) * max 0 (min 1 t)) k • S.root i
  wt := μ - k • D.root i
  toFun_of_nonpos' t ht := by
    rw [min_eq_right (ht.trans zero_le_one), max_eq_left ht, zero_smul, mul_zero,
      min_eq_left (Nat.cast_nonneg k), zero_smul, sub_zero]
  toFun_of_one_le' t ht := by
    rw [min_eq_left ht, max_eq_right zero_le_one, one_smul, mul_one,
      min_eq_right (by exact_mod_cast hk), map_sub, map_nsmul, CartanDatum.PathSpace.root,
      Nat.cast_smul_eq_nsmul]
  continuous_coroot' j := by
    have hc : Continuous fun t : 𝕜 ↦ max 0 (min 1 t) :=
      continuous_const.max (continuous_const.min continuous_id)
    simp only [map_sub, map_smul, smul_eq_mul]
    exact (hc.mul continuous_const).sub
      (((continuous_const.mul hc).min continuous_const).mul continuous_const)

/--
@isnad1 id=eq.2h10v.s9.41285d3aa41a from=translated src=- shape=989a29f6 vocab=87cab833
-/
lemma stringPath_apply {k : ℕ} (hk : (k : ℤ) ≤ D.coroot i μ) {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    stringPath S μ i k hk t = t • S.embed μ - min ((D.coroot i μ : 𝕜) * t) k • S.root i := by
  change max 0 (min 1 t) • S.embed μ - min ((D.coroot i μ : 𝕜) * max 0 (min 1 t)) k • S.root i = _
  rw [min_eq_right ht.2, max_eq_right ht.1]

/--
@isnad1 id=eq.1h8v.s7.a57a9b31d272 from=translated src=- shape=13b0e441 vocab=816ee3ab
-/
lemma stringPath_zero (hk : ((0 : ℕ) : ℤ) ≤ D.coroot i μ) :
    stringPath S μ i 0 hk = straightLine S μ := by
  refine ext_of_eqOn fun t ht ↦ ?_
  rw [stringPath_apply hk ht, straightLine_apply, min_eq_right ht.2, max_eq_right ht.1,
    Nat.cast_zero, min_eq_right (mul_nonneg (by exact_mod_cast hk) ht.1), zero_smul, sub_zero]

/--
@isnad1 id=eq.2h10v.s8.019ed629a0df from=translated src=- shape=3a7cfad4 vocab=5e8310cb
-/
lemma pairing_stringPath {k : ℕ} (hk : (k : ℤ) ≤ D.coroot i μ) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) :
    (stringPath S μ i k hk).pairing i t =
      D.coroot i μ * t - 2 * min ((D.coroot i μ : 𝕜) * t) k := by
  rw [pairing, stringPath_apply hk ht, map_sub, map_smul, map_smul, S.coroot_embed,
    S.coroot_root_self, smul_eq_mul, smul_eq_mul]
  ring

/--
@isnad1 id=eq.2h10v.s8.f108908fbe14 from=translated src=- shape=180cf3c1 vocab=33d15097
-/
lemma runningMin_stringPath {k : ℕ} (hk : ((k + 1 : ℕ) : ℤ) ≤ D.coroot i μ) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) :
    (stringPath S μ i (k + 1) hk).runningMin i t = -min ((D.coroot i μ : 𝕜) * t) (k + 1) := by
  have hn : (0 : 𝕜) < D.coroot i μ := by
    have : (0 : ℤ) < D.coroot i μ := lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos k) hk
    exact_mod_cast this
  set n : 𝕜 := ((D.coroot i μ : ℤ) : 𝕜)
  apply le_antisymm
  · rcases le_total (n * t) (k + 1) with h | h
    · refine ((stringPath S μ i (k + 1) hk).runningMin_le (i := i) ⟨ht.1, le_rfl⟩).trans_eq ?_
      rw [pairing_stringPath hk ht, min_eq_left (by push_cast; exact h), min_eq_left h]
      ring
    · have hs : (k + 1) / n ∈ Icc (0 : 𝕜) t :=
        ⟨by positivity, by rwa [div_le_iff₀ hn, mul_comm]⟩
      refine ((stringPath S μ i (k + 1) hk).runningMin_le (i := i) hs).trans_eq ?_
      rw [pairing_stringPath hk ⟨hs.1, hs.2.trans ht.2⟩, mul_div_cancel₀ _ hn.ne', min_eq_right h]
      push_cast
      rw [min_self]
      ring
  · refine (stringPath S μ i (k + 1) hk).le_runningMin ht.1 fun u hu ↦ ?_
    rw [pairing_stringPath hk ⟨hu.1, hu.2.trans ht.2⟩]
    push_cast
    have hnu : n * u ≤ n * t := mul_le_mul_of_nonneg_left hu.2 hn.le
    rcases le_total (n * u) (k + 1) with h | h
    · rw [min_eq_left h]
      have := min_le_min_right ((k : 𝕜) + 1) hnu
      rw [min_eq_left h] at this
      linarith
    · rw [min_eq_right h, min_eq_right (h.trans hnu)]
      linarith

/-- `eᵢ` moves one step up the `αᵢ`-string through `π_λ`.
@isnad1 id=eq.1h9v.s8.d0294fee1dbd from=translated src=- shape=041873a5 vocab=603ca4ae
-/
theorem e_stringPath {k : ℕ} (hk : ((k + 1 : ℕ) : ℤ) ≤ D.coroot i μ) :
    e i (stringPath S μ i (k + 1) hk) =
      some (stringPath S μ i k ((Int.ofNat_le.mpr k.le_succ).trans hk)) := by
  have hQ : (stringPath S μ i (k + 1) hk).minPairing i = -(k + 1) := by
    rw [minPairing, runningMin_stringPath hk ⟨zero_le_one, le_rfl⟩, mul_one,
      min_eq_right (by exact_mod_cast hk)]
  rw [e_of_le (by rw [hQ]; linarith [(Nat.cast_nonneg k : (0 : 𝕜) ≤ k)])]
  congr 1
  refine ext_of_eqOn fun t ht ↦ ?_
  rw [eRaw_apply, stringPath_apply _ ht, stringPath_apply _ ht, eCoeff, hQ,
    runningMin_stringPath hk ht]
  set x : 𝕜 := (D.coroot i μ : 𝕜) * t
  have key : min x ((k + 1 : ℕ) : 𝕜) +
      (min (-min x ((k : 𝕜) + 1)) (-((k : 𝕜) + 1) + 1) - (-((k : 𝕜) + 1) + 1)) = min x k := by
    push_cast
    rcases le_total x k with h₁ | h₁
    · rw [min_eq_left (by linarith), min_eq_left h₁, min_eq_right (by linarith)]
      ring
    rcases le_total x (k + 1) with h₂ | h₂
    · rw [min_eq_left h₂, min_eq_right h₁, min_eq_left (by linarith)]
      ring
    · rw [min_eq_right h₂, min_eq_right h₁, min_eq_left (by linarith)]
      ring
  rw [← key]
  module

/-- `fᵢ^k π_λ = t ↦ tλ - min(nt, k) αᵢ` for `k ≤ n = ⟨λ, αᵢ^∨⟩`.
@isnad1 id=eq.1h9v.s8.eb36c5cc4d89 from=translated src=- shape=d7a7867f vocab=07d2ef2f
-/
theorem f_stringPath {k : ℕ} (hk : ((k + 1 : ℕ) : ℤ) ≤ D.coroot i μ) :
    f i (stringPath S μ i k ((Int.ofNat_le.mpr k.le_succ).trans hk)) =
      some (stringPath S μ i (k + 1) hk) :=
  f_eq_some_iff.mpr (e_stringPath hk)

variable [FloorRing 𝕜]

/-! ### Connected components -/

/-- The connected component `B(π)` of a path `π` in the path crystal: the smallest set of paths
containing `π` and stable under all root operators ([Lit95] §2).-/
def component (π : LittelmannPath S) : Set (LittelmannPath S) := (crystal S).closure {π}

variable (π : LittelmannPath S)

/--
@isnad1 id=mem.0h7v.s7.e783a34421fc from=translated src=- shape=c01cf610 vocab=8353bc21
-/
lemma mem_component_self : π ∈ π.component := (crystal S).subset_closure {π} rfl

/--
@isnad1 id=isstable.0h7v.s7.45270e542f8d from=translated src=- shape=4a6095be vocab=89afd938
-/
lemma isStable_component : (crystal S).IsStable π.component := Crystal.isStable_closure _

/-- The crystal structure on the connected component `B(π)`. For the straight line path `π_λ` of
a dominant weight this is Littelmann's crystal `B(λ)`.-/
noncomputable def componentCrystal : Crystal D π.component :=
  Crystal.restrict π.isStable_component

/-- The crystal `B(π)` is seminormal.
@isnad1 id=issemino.0h7v.s7.243aa68b8969 from=translated src=- shape=eded5b54 vocab=1d546159
-/
theorem isSeminormal_componentCrystal : π.componentCrystal.IsSeminormal :=
  (isSeminormal_crystal S).restrict π.isStable_component

/-! ### Connected components of crystals -/

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜] in
/-- In a crystal, `a` lies in the connected component of `b` iff `b` lies in that of `a`.
@isnad1 id=mem.1h7v.s6.c6508b0928a9 from=translated src=- shape=16e94280 vocab=be53a603
-/
lemma _root_.Tengoku.LieLean.Crystal.mem_closure_singleton_comm {B : Type*} {C : Crystal D B} {a b : B}
    (h : a ∈ C.closure {b}) : b ∈ C.closure {a} := by
  have hT : C.IsStable {x | b ∈ C.closure {x}} := by
    refine ⟨fun j x x' hx he ↦ ?_, fun j x x' hx hf ↦ ?_⟩
    · have hx' : x ∈ C.closure {x'} := (Crystal.isStable_closure {x'}).f_mem j x' x
        (Crystal.subset_closure {x'} rfl) ((C.f_eq_some_iff j x' x).mpr he)
      exact Crystal.closure_subset (Crystal.isStable_closure _) (singleton_subset_iff.mpr hx') hx
    · have hx' : x ∈ C.closure {x'} := (Crystal.isStable_closure {x'}).e_mem j x' x
        (Crystal.subset_closure {x'} rfl) ((C.f_eq_some_iff j x x').mp hf)
      exact Crystal.closure_subset (Crystal.isStable_closure _) (singleton_subset_iff.mpr hx') hx
  exact Crystal.closure_subset hT (singleton_subset_iff.mpr (Crystal.subset_closure {b} rfl)) h

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜] in
/--
@isnad1 id=le.1h7v.s6.280a18eb2fc3 from=translated src=- shape=ff3ba236 vocab=02321664
-/
lemma _root_.Tengoku.LieLean.Crystal.closure_singleton_subset {B : Type*} {C : Crystal D B} {a b : B}
    (h : a ∈ C.closure {b}) : C.closure {a} ⊆ C.closure {b} :=
  Crystal.closure_subset (Crystal.isStable_closure _) (singleton_subset_iff.mpr h)

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜] in
/--
@isnad1 id=mem.1h9v.s6.65846f7847d0 from=translated src=- shape=d349a8af vocab=62592400
-/
lemma _root_.Tengoku.LieLean.Crystal.mem_closure_of_fIter_eq_some {B : Type*} {C : Crystal D B} {b b' : B}
    {i : ι} {k : ℕ} (h : C.fIter i k b = some b') : b' ∈ C.closure {b} := by
  induction k generalizing b' with
  | zero =>
    cases h
    exact Crystal.subset_closure {b} rfl
  | succ k ih =>
    rw [C.fIter_succ'] at h
    obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp h
    exact (Crystal.isStable_closure {b}).f_mem i c b' (ih hc) hf

/--
@isnad1 id=eq.1h9v.s8.72731a499e3f from=translated src=- shape=14c625f5 vocab=c4b8d0fc
-/
theorem fIter_straightLine {k : ℕ} (hk : (k : ℤ) ≤ D.coroot i μ) :
    (crystal S).fIter i k (straightLine S μ) = some (stringPath S μ i k hk) := by
  induction k with
  | zero => rw [Crystal.fIter_zero, stringPath_zero]
  | succ k ih =>
    rw [Crystal.fIter_succ', ih ((Int.ofNat_le.mpr k.le_succ).trans hk), Option.bind_some]
    exact f_stringPath hk

/-! ### The paths `f_{i₁} ⋯ f_{iₖ} π` -/

/-- `fWord [i₁, …, iₖ] π = f_{i₁} ⋯ f_{iₖ} π` (`none` if some step gives `0`).-/
noncomputable def fWord : List ι → LittelmannPath S → Option (LittelmannPath S)
  | [], π => some π
  | i :: l, π => (fWord l π).bind (f i)

/-- The set of paths `f_{i₁} ⋯ f_{iₖ} π`.-/
def fOrbit : Set (LittelmannPath S) := {π' | ∃ l, fWord l π = some π'}

variable {π}

/--
@isnad1 id=eq.1h9v.s8.31e00c2dc38d from=translated src=- shape=ab8dc398 vocab=4ee123f1
-/
lemma wt_of_fWord {l : List ι} {π' : LittelmannPath S} (h : fWord l π = some π') :
    π'.wt = π.wt - (l.map D.root).sum := by
  induction l generalizing π' with
  | nil =>
    cases h
    simp
  | cons i l ih =>
    obtain ⟨ρ, hρ, hf⟩ := Option.bind_eq_some_iff.mp h
    have := (crystal S).wt_f hf
    simp only [crystal_wt] at this
    rw [this, ih hρ, List.map_cons, List.sum_cons]
    abel

/--
@isnad1 id=le.0h7v.s7.26c0c4ddb4bc from=translated src=- shape=49177e27 vocab=5358bbf1
-/
lemma fOrbit_subset_component : π.fOrbit ⊆ π.component := by
  rintro π' ⟨l, hl⟩
  induction l generalizing π' with
  | nil =>
    cases hl
    exact π.mem_component_self
  | cons i l ih =>
    obtain ⟨ρ, hρ, hf⟩ := Option.bind_eq_some_iff.mp hl
    exact π.isStable_component.f_mem i ρ π' (ih hρ) hf

/-- If the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ`, then it is the connected component
`B(π)`. (Littelmann proves the hypothesis for paths `π` in the dominant chamber, [Lit95] §7,
Cor. 1 c); this is not formalized here.)
@isnad1 id=eq.1h7v.s8.40ed31adc27a from=translated src=- shape=c6813d51 vocab=9d52fb21
-/
theorem component_eq_fOrbit
    (h : ∀ π' ∈ π.fOrbit, ∀ j π'', e j π' = some π'' → π'' ∈ π.fOrbit) :
    π.component = π.fOrbit := by
  refine subset_antisymm (Crystal.closure_subset ⟨fun j π' π'' hπ' he ↦ h π' hπ' j π'' he,
    fun j π' π'' ⟨l, hl⟩ hf ↦ ⟨j :: l, by rw [fWord, hl, Option.bind_some]; exact hf⟩⟩
    (singleton_subset_iff.mpr ⟨[], rfl⟩)) fOrbit_subset_component

/-- If the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ`, then the weights of `B(π)` lie in
`wt π - Q₊`.
@isnad1 id=ex.2h8v.s9.a4b67edaee47 from=translated src=- shape=8f056c05 vocab=35d0ee93
-/
theorem exists_wt_eq_of_mem_component
    (h : ∀ π' ∈ π.fOrbit, ∀ j π'', e j π' = some π'' → π'' ∈ π.fOrbit)
    {π' : LittelmannPath S} (hπ' : π' ∈ π.component) :
    ∃ s : Multiset ι, π'.wt = π.wt - (s.map D.root).sum := by
  rw [component_eq_fOrbit h] at hπ'
  obtain ⟨l, hl⟩ := hπ'
  exact ⟨l, by rw [wt_of_fWord hl, Multiset.map_coe, Multiset.sum_coe]⟩

/-- If the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ` and the simple roots are linearly
independent (in the sense that `s ↦ ∑_{i ∈ s} αᵢ` is injective on multisets), then every weight
occurs only finitely often in `B(π)`.
@isnad1 id=finite.2h8v.s9.e58ae9f1a092 from=translated src=- shape=789056e0 vocab=7b24894e
-/
theorem finite_wt_component
    (hroot : Function.Injective fun s : Multiset ι ↦ (s.map D.root).sum)
    (h : ∀ π' ∈ π.fOrbit, ∀ j π'', e j π' = some π'' → π'' ∈ π.fOrbit) (μ : X) :
    {π' ∈ π.component | π'.wt = μ}.Finite := by
  rw [component_eq_fOrbit h]
  rcases eq_empty_or_nonempty {π' ∈ π.fOrbit | π'.wt = μ} with h0 | ⟨π₀, ⟨l₀, hl₀⟩, hπ₀⟩
  · rw [h0]
    exact finite_empty
  refine ((List.finite_toSet l₀.permutations).image fun l ↦ (fWord l π).getD π).subset ?_
  rintro π' ⟨⟨l, hl⟩, hπ'⟩
  refine ⟨l, List.mem_permutations.mpr (Multiset.coe_eq_coe.mp (hroot ?_)), by simp [hl]⟩
  have h₁ := wt_of_fWord hl
  have h₂ := wt_of_fWord hl₀
  simp only [Multiset.map_coe, Multiset.sum_coe]
  rw [hπ', hπ₀] at *
  rw [h₁] at h₂
  exact sub_right_inj.mp h₂

end Tengoku.LieLean.LittelmannPath
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
