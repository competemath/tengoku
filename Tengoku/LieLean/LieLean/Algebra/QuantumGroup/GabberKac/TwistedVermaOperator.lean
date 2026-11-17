/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.GabberKac.VermaOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Twisted Verma-type operators on free algebras

Let `R` be a commutative ring, `i ∈ X`, `s : X → R` and `c : ℕ[X] → R`. The *twisted Verma-type
operator* `E = LusztigF.twistVermaOp i s c` on `FreeAlgebra R X` is the `R`-linear map determined
by `E(1) = 0` and
`E(xⱼ y) = sⱼ xⱼ E(y) + δᵢⱼ c(μ) y` for `y` of weight `μ` (`LusztigF.twistVermaOp_ι_mul`).

For `s = 1` this is `LusztigF.vermaOp` (`LusztigF.twistVermaOp_one`). The signs `sⱼ` are those of
a raising operator acting on a Verma module through a super commutator relation
`eᵢ fⱼ = σ(i, j) fⱼ eᵢ + δᵢⱼ hᵢ` (contragredient Lie superalgebras, [Kac78] §1.2), or through a
twisted relation `Eᵢ Fⱼ = π^{p(i)p(j)} Fⱼ Eᵢ + ⋯` (covering quantum groups). As for
`LusztigF.vermaOp`, `E_w = E_{iₙ} ∘ ⋯ ∘ E_{i₁}` for a word `w = [i₁, …, iₙ]`
(`LusztigF.twistVermaWordOp`) and `S(w, y) = ε(E_w y)` (`LusztigF.twistVermaForm`).

The operators are natural in the coefficient ring (`LusztigF.map_twistVermaForm`), lower weights
(`LusztigF.twistVermaForm_eq_zero_of_ne`), and rescaling the coefficients `cᵢ` by constants `κᵢ`
rescales `S(w, -)` by `∏ κ_{w_a}` (`LusztigF.twistVermaForm_mul_coeff`).

## Main definitions

* `LusztigF.twistVermaOp i s c`, `LusztigF.twistVermaWordOp s c w`, `LusztigF.twistVermaForm s c w`.

## Main results

* `LusztigF.twistVermaOp_ι_mul`: the defining recursion.
* `LusztigF.map_twistVermaForm`: naturality under `FreeAlgebra.mapCoeffs`.
* `LusztigF.twistVermaForm_eq_zero_of_ne`: `S(w, y) = 0` unless `y` has the weight of `w`.
* `LusztigF.eq_algebraMap_of_mem_wordSpan_zero`: the weight-zero part of `FreeAlgebra R X` is `R`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2.
-/

noncomputable section
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean 
open FreeAlgebra

namespace Tengoku.LieLean.LusztigF

variable {R X : Type*} [CommRing R] [DecidableEq X]

/-- The values of the twisted Verma-type operator on words.-/
def twistVermaOpWord (i : X) (s : X → R) (c : (X →₀ ℕ) → R) : List X → FreeAlgebra R X
  | [] => 0
  | j :: w => s j • (ι R j * twistVermaOpWord i s c w) +
      if i = j then c (wordWeight w) • wordBasis R X w else 0

/-- The twisted Verma-type operator `E` on `FreeAlgebra R X`: `E(1) = 0` and
`E(xⱼ y) = sⱼ xⱼ E(y) + δᵢⱼ c(μ) y` for `y` of weight `μ`.-/
def twistVermaOp (i : X) (s : X → R) (c : (X →₀ ℕ) → R) :
    FreeAlgebra R X →ₗ[R] FreeAlgebra R X :=
  (wordBasis R X).constr R (twistVermaOpWord i s c)

/--
@isnad1 id=eq.0h6v.s8.2bce2319eab8 from=translated src=- shape=21e2c285 vocab=b59280ef
-/
@[simp] lemma twistVermaOp_wordBasis (i : X) (s : X → R) (c : (X →₀ ℕ) → R) (w : List X) :
    twistVermaOp i s c (wordBasis R X w) = twistVermaOpWord i s c w :=
  (wordBasis R X).constr_basis R _ w

/--
@isnad1 id=eq.0h5v.s8.af9ed262aa46 from=translated src=- shape=14005501 vocab=57a2d971
-/
@[simp] lemma twistVermaOp_one (i : X) (s : X → R) (c : (X →₀ ℕ) → R) :
    twistVermaOp i s c 1 = 0 := by
  rw [← wordBasis_nil, twistVermaOp_wordBasis, twistVermaOpWord]

/-- The defining recursion `E(xⱼ y) = sⱼ xⱼ E(y) + δᵢⱼ c(|y|) y`.
@isnad1 id=eq.0h7v.s9.6f1c2fac2b52 from=translated src=- shape=59ff9e4d vocab=9cc8dc50
-/
theorem twistVermaOp_ι_mul (i : X) (s : X → R) (c : (X →₀ ℕ) → R) (j : X)
    (y : FreeAlgebra R X) :
    twistVermaOp i s c (ι R j * y) =
      s j • (ι R j * twistVermaOp i s c y) + if i = j then weightScale c y else 0 := by
  induction y using induction_wordBasis with
  | zero => simp
  | add y z hy hz =>
    rw [mul_add, map_add, hy, hz, map_add, mul_add, smul_add]
    split_ifs
    · rw [map_add]; abel
    · simp only [add_zero]
  | smul a y hy =>
    rw [mul_smul_comm, map_smul, hy, map_smul, smul_add, mul_smul_comm, smul_comm a (s j)]
    split_ifs <;> simp
  | word w =>
    rw [ι_mul_wordBasis, twistVermaOp_wordBasis, twistVermaOp_wordBasis, twistVermaOpWord,
      weightScale_wordBasis]

/-- With trivial signs, the twisted operator is `LusztigF.vermaOp`.
@isnad1 id=eq.0h4v.s7.5e4f985559cd from=translated src=- shape=090f571b vocab=23ea2847
-/
theorem twistVermaOp_one_sign (i : X) (c : (X →₀ ℕ) → R) :
    twistVermaOp i (fun _ ↦ 1) c = vermaOp i c := by
  refine (wordBasis R X).ext fun w ↦ ?_
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [← ι_mul_wordBasis, twistVermaOp_ι_mul, ih, vermaOp_ι_mul, one_smul]

/-- Rescaling the coefficients by a constant rescales the operator.
@isnad1 id=eq.0h6v.s9.922ea3cc221a from=translated src=- shape=1ff9c8a9 vocab=e4605d06
-/
theorem twistVermaOp_mul_coeff (i : X) (s : X → R) (c : (X →₀ ℕ) → R) (κ : R) :
    twistVermaOp i s (fun μ ↦ κ * c μ) = κ • twistVermaOp i s c := by
  refine (wordBasis R X).ext fun w ↦ ?_
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [← ι_mul_wordBasis, twistVermaOp_ι_mul, ih, LinearMap.smul_apply, LinearMap.smul_apply,
      twistVermaOp_ι_mul, weightScale_wordBasis, weightScale_wordBasis, smul_add, mul_smul_comm,
      smul_comm κ (s j)]
    split_ifs <;> simp [mul_smul]

/-- The operator `E_w = E_{iₙ} ∘ ⋯ ∘ E_{i₁}` of a word `w = [i₁, …, iₙ]`.-/
def twistVermaWordOp (s : X → X → R) (c : X → (X →₀ ℕ) → R) :
    List X → Module.End R (FreeAlgebra R X)
  | [] => 1
  | i :: w => twistVermaWordOp s c w * twistVermaOp i (s i) (c i)

/--
@isnad1 id=eq.0h4v.s7.2a692c73cd28 from=translated src=- shape=c0b2daf6 vocab=b744413d
-/
@[simp] lemma twistVermaWordOp_nil (s : X → X → R) (c : X → (X →₀ ℕ) → R) :
    twistVermaWordOp s c [] = 1 := rfl

/--
@isnad1 id=eq.0h7v.s9.4868ce8a1766 from=translated src=- shape=5e318b91 vocab=8db9d6a8
-/
lemma twistVermaWordOp_cons (s : X → X → R) (c : X → (X →₀ ℕ) → R) (i : X) (w : List X)
    (y : FreeAlgebra R X) :
    twistVermaWordOp s c (i :: w) y = twistVermaWordOp s c w (twistVermaOp i (s i) (c i) y) :=
  rfl

/-- The pairing `S(w, y) = ε(E_w y)` between a word `w` and `y`.-/
def twistVermaForm (s : X → X → R) (c : X → (X →₀ ℕ) → R) (w : List X) :
    FreeAlgebra R X →ₗ[R] R :=
  (algebraMapInv : FreeAlgebra R X →ₐ[R] R).toLinearMap ∘ₗ twistVermaWordOp s c w

/--
@isnad1 id=eq.0h6v.s9.a24e0aee55e8 from=translated src=- shape=c51cb1f2 vocab=ed8fe35d
-/
lemma twistVermaForm_apply (s : X → X → R) (c : X → (X →₀ ℕ) → R) (w : List X)
    (y : FreeAlgebra R X) :
    twistVermaForm s c w y = algebraMapInv (twistVermaWordOp s c w y) := rfl

/--
@isnad1 id=eq.0h7v.s9.b171d9ec4aba from=translated src=- shape=161ed548 vocab=04efcd8c
-/
lemma twistVermaForm_cons (s : X → X → R) (c : X → (X →₀ ℕ) → R) (i : X) (w : List X)
    (y : FreeAlgebra R X) :
    twistVermaForm s c (i :: w) y = twistVermaForm s c w (twistVermaOp i (s i) (c i) y) := rfl

/-- Rescaling the coefficients `cᵢ` by constants `κᵢ` rescales `S(w, -)` by `∏ₐ κ_{w_a}`.
@isnad1 id=eq.0h7v.s8.8b5460984cf1 from=translated src=- shape=36d7419a vocab=86e7a7cf
-/
theorem twistVermaForm_mul_coeff (s : X → X → R) (c : X → (X →₀ ℕ) → R) (κ : X → R)
    (w : List X) (y : FreeAlgebra R X) :
    twistVermaForm s (fun i μ ↦ κ i * c i μ) w y = (w.map κ).prod * twistVermaForm s c w y := by
  induction w generalizing y with
  | nil => simp [twistVermaForm_apply]
  | cons i w ih =>
    rw [twistVermaForm_cons, twistVermaOp_mul_coeff, LinearMap.smul_apply, map_smul, ih,
      twistVermaForm_cons, List.map_cons, List.prod_cons, smul_eq_mul]
    ring

/-! ### Naturality -/

variable {S : Type*} [CommRing S] (φ : R →+* S)

/--
@isnad1 id=eq.0h8v.s8.f615fe9eb518 from=translated src=- shape=25123cb1 vocab=749fb7b2
-/
lemma mapCoeffs_twistVermaOpWord (i : X) (s : X → R) (c : (X →₀ ℕ) → R) (w : List X) :
    mapCoeffs φ (twistVermaOpWord i s c w) = twistVermaOpWord i (φ ∘ s) (φ ∘ c) w := by
  induction w with
  | nil => simp [twistVermaOpWord]
  | cons j w ih =>
    simp only [twistVermaOpWord, map_add, mapCoeffs_smul, map_mul, mapCoeffs_ι, ih,
      Function.comp_apply]
    split_ifs <;> simp [mapCoeffs_smul, map_list_prod, Function.comp_def]

/-- The twisted Verma-type operators commute with change of coefficients.
@isnad1 id=eq.0h8v.s9.b4a4aeec6afd from=translated src=- shape=4e273147 vocab=9e81540d
-/
theorem mapCoeffs_twistVermaOp (i : X) (s : X → R) (c : (X →₀ ℕ) → R) (y : FreeAlgebra R X) :
    mapCoeffs φ (twistVermaOp i s c y) = twistVermaOp i (φ ∘ s) (φ ∘ c) (mapCoeffs φ y) := by
  induction y using induction_wordBasis with
  | zero => simp
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  | smul a y hy => rw [map_smul, mapCoeffs_smul, hy, mapCoeffs_smul, map_smul]
  | word w =>
    rw [twistVermaOp_wordBasis, mapCoeffs_twistVermaOpWord, mapCoeffs_wordBasis,
      twistVermaOp_wordBasis]

/--
@isnad1 id=eq.0h8v.s9.fbb1b39c8727 from=translated src=- shape=32f2faf0 vocab=48e8dd37
-/
theorem mapCoeffs_twistVermaWordOp (s : X → X → R) (c : X → (X →₀ ℕ) → R) (w : List X)
    (y : FreeAlgebra R X) :
    mapCoeffs φ (twistVermaWordOp s c w y) =
      twistVermaWordOp (fun i ↦ φ ∘ s i) (fun i ↦ φ ∘ c i) w (mapCoeffs φ y) := by
  induction w generalizing y with
  | nil => rfl
  | cons i w ih =>
    rw [twistVermaWordOp_cons, ih, mapCoeffs_twistVermaOp, twistVermaWordOp_cons]

/-- The pairing is natural in the coefficient ring.
@isnad1 id=eq.0h8v.s9.2e458a7038c5 from=translated src=- shape=98ab2e4f vocab=fbc8688d
-/
theorem map_twistVermaForm (s : X → X → R) (c : X → (X →₀ ℕ) → R) (w : List X)
    (y : FreeAlgebra R X) :
    φ (twistVermaForm s c w y) =
      twistVermaForm (fun i ↦ φ ∘ s i) (fun i ↦ φ ∘ c i) w (mapCoeffs φ y) := by
  rw [twistVermaForm_apply, twistVermaForm_apply, ← mapCoeffs_twistVermaWordOp,
    algebraMapInv_mapCoeffs]

/-! ### Weights -/

/--
@isnad1 id=eq.1h6v.s6.39929876affc from=translated src=- shape=378ee859 vocab=84fd8086
-/
lemma twistVermaOpWord_eq_zero (i : X) (s : X → R) (c : (X →₀ ℕ) → R) (w : List X)
    (hw : wordWeight w i = 0) : twistVermaOpWord i s c w = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    have hij : i ≠ j := by rintro rfl; simp at hw
    have hw' : wordWeight w i = 0 := by
      simp only [wordWeight_cons, Finsupp.add_apply] at hw; omega
    simp [twistVermaOpWord, ih hw', hij]

/--
@isnad1 id=mem.0h6v.s8.07d070dce9b7 from=translated src=- shape=f04876ff vocab=c8fd49f3
-/
lemma twistVermaOpWord_mem (i : X) (s : X → R) (c : (X →₀ ℕ) → R) (w : List X) :
    twistVermaOpWord i s c w ∈ wordSpan R (wordWeight w - Finsupp.single i 1) := by
  induction w with
  | nil => simp [twistVermaOpWord]
  | cons j w ih =>
    rw [twistVermaOpWord]
    refine add_mem (Submodule.smul_mem _ _ ?_) ?_
    · by_cases hwi : wordWeight w i = 0
      · rw [twistVermaOpWord_eq_zero i s c w hwi, mul_zero]; exact zero_mem _
      · have h := ι_mul_mem_wordSpan (R := R) j ih
        convert h using 2
        rw [wordWeight_cons]
        ext l
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs <;> subst_vars <;> omega
    · split_ifs with hij
      · subst hij
        refine Submodule.smul_mem _ _ (wordBasis_mem_wordSpan_of_eq ?_)
        rw [wordWeight_cons, add_comm, add_tsub_cancel_right]
      · exact zero_mem _

/--
@isnad1 id=mem.1h7v.s9.05267a98042b from=translated src=- shape=571571d1 vocab=ca4c9a18
-/
lemma twistVermaOp_mem_wordSpan (i : X) (s : X → R) (c : (X →₀ ℕ) → R) {μ : X →₀ ℕ}
    {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) :
    twistVermaOp i s c y ∈ wordSpan R (μ - Finsupp.single i 1) := by
  induction hy using wordSpan_induction with
  | word w hw => rw [twistVermaOp_wordBasis, ← hw]; exact twistVermaOpWord_mem i s c w
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

/--
@isnad1 id=eq.2h7v.s9.f0fa353215ff from=translated src=- shape=ed337edc vocab=0728610d
-/
lemma twistVermaOp_eq_zero_of_mem (i : X) (s : X → R) (c : (X →₀ ℕ) → R) {μ : X →₀ ℕ}
    (hμ : μ i = 0) {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) : twistVermaOp i s c y = 0 := by
  induction hy using wordSpan_induction with
  | word w hw => rw [twistVermaOp_wordBasis, twistVermaOpWord_eq_zero i s c w (hw ▸ hμ)]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul a y _ hy => rw [map_smul, hy, smul_zero]

/--
@isnad1 id=and.1h7v.s9.d8f1b33a6c69 from=translated src=- shape=e1e8c08a vocab=df078025
-/
lemma twistVermaWordOp_mem (s : X → X → R) (c : X → (X →₀ ℕ) → R) (w : List X) {μ : X →₀ ℕ}
    {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) :
    twistVermaWordOp s c w y ∈ wordSpan R (μ - wordWeight w) ∧
      (¬ wordWeight w ≤ μ → twistVermaWordOp s c w y = 0) := by
  induction w generalizing μ y with
  | nil => simpa using hy
  | cons i w ih =>
    rw [twistVermaWordOp_cons]
    by_cases hμi : μ i = 0
    · rw [twistVermaOp_eq_zero_of_mem i (s i) (c i) hμi hy, map_zero]
      exact ⟨zero_mem _, fun _ ↦ rfl⟩
    · obtain ⟨h1, h2⟩ := ih (twistVermaOp_mem_wordSpan i (s i) (c i) hy)
      have e : μ - Finsupp.single i 1 - wordWeight w = μ - wordWeight (i :: w) := by
        rw [wordWeight_cons, tsub_tsub]
      refine ⟨e ▸ h1, fun h ↦ h2 fun hle ↦ h ?_⟩
      rw [wordWeight_cons, ← single_add_tsub_single hμi, add_comm (Finsupp.single i 1)]
      exact add_le_add_left hle _

/-- `S(w, y) = 0` unless `y` has the weight of the word `w`.
@isnad1 id=eq.2h7v.s8.3706af09dbfd from=translated src=- shape=3319263d vocab=fbefd76e
-/
theorem twistVermaForm_eq_zero_of_ne (s : X → X → R) (c : X → (X →₀ ℕ) → R) (w : List X)
    {μ : X →₀ ℕ} (hμ : wordWeight w ≠ μ) {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) :
    twistVermaForm s c w y = 0 := by
  obtain ⟨h1, h2⟩ := twistVermaWordOp_mem s c w hy
  rw [twistVermaForm_apply]
  by_cases hle : wordWeight w ≤ μ
  · refine algebraMapInv_eq_zero_of_mem_wordSpan (fun h0 ↦ hμ ?_) h1
    exact le_antisymm hle (tsub_eq_zero_iff_le.1 h0)
  · rw [h2 hle, map_zero]

omit [DecidableEq X] in
/-- The weight-zero part of `FreeAlgebra R X` consists of the scalars.-/
lemma eq_algebraMap_of_mem_wordSpan_zero {y : FreeAlgebra R X} (hy : y ∈ wordSpan R 0) :
    y = algebraMap R _ (algebraMapInv y) := by
  induction hy using wordSpan_induction with
  | word w hw =>
    cases w with
    | nil => simp
    | cons j w => simp [wordWeight_cons] at hw
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, ← hy, ← hz]
  | smul a y _ hy =>
    rw [map_smul, smul_eq_mul, map_mul, ← hy, Algebra.smul_def]

/-- If `y` has the weight of `w`, then `E_w y = S(w, y)`.
@isnad1 id=eq.1h6v.s9.c63fbb14bbb4 from=translated src=- shape=e85865ea vocab=5a479d2d
-/
theorem twistVermaWordOp_eq_algebraMap (s : X → X → R) (c : X → (X →₀ ℕ) → R) (w : List X)
    {y : FreeAlgebra R X} (hy : y ∈ wordSpan R (wordWeight w)) :
    twistVermaWordOp s c w y = algebraMap R _ (twistVermaForm s c w y) := by
  have h := (twistVermaWordOp_mem s c w hy).1
  rw [tsub_self] at h
  exact eq_algebraMap_of_mem_wordSpan_zero h

end Tengoku.LieLean.LusztigF
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
