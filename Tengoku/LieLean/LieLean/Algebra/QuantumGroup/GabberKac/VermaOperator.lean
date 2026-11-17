/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.GabberKac.MapCoeffs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Verma-type operators on free algebras

Let `R` be a commutative ring, `i ∈ X` and `c : ℕ[X] → R`. The *Verma-type operator*
`E = LusztigF.vermaOp i c` on the free algebra `FreeAlgebra R X` is the `R`-linear map determined
by `E(1) = 0` and
`E(xⱼ y) = xⱼ E(y) + δᵢⱼ c(μ) y` for `y` of weight `μ` (`LusztigF.vermaOp_ι_mul`).

This is the shape of the action of a raising operator on a Verma module, pulled back to the free
algebra on the lowering operators: classically `eᵢ fⱼ y v_Λ = fⱼ eᵢ y v_Λ + δᵢⱼ hᵢ y v_Λ` with
`hᵢ y v_Λ = ⟨Λ - μ, αᵢ^∨⟩ y v_Λ`, and for quantum groups the same holds with the quantum integer
`[⟨Λ - μ, αᵢ^∨⟩]_{vᵢ}` ([Lus] 3.4.2, 3.4.5, [Jan] 4.3 (R4), 5.12(8)). For a family `c = (cᵢ)ᵢ`
and a word `w = [i₁, …, iₙ]` we put `E_w = E_{iₙ} ∘ ⋯ ∘ E_{i₁}` (`LusztigF.vermaWordOp`) and
`S(w, y) = ε(E_w y)` (`LusztigF.vermaForm`), where `ε` is the augmentation: this is the
(contravariant) Shapovalov pairing between the word `w` and `y`.

The operators are natural in the coefficient ring (`LusztigF.mapCoeffs_vermaOp`,
`LusztigF.map_vermaForm`), which is how the quantum and classical Shapovalov pairings are
compared in the quantum Gabber–Kac theorem, and they lower weights
(`LusztigF.vermaForm_eq_zero_of_ne`).

## Main definitions

* `LusztigF.vermaOp i c`, `LusztigF.vermaWordOp c w`, `LusztigF.vermaForm c w y`.

## Main results

* `LusztigF.vermaOp_ι_mul`: the defining recursion.
* `LusztigF.map_vermaForm`: naturality under `FreeAlgebra.mapCoeffs`.
* `LusztigF.vermaForm_eq_zero_of_ne`: `S(w, y) = 0` unless `y` has the weight of `w`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.4.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 4.3, 5.5, 5.12.
-/

noncomputable section
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean 
open FreeAlgebra

namespace Tengoku.LieLean.LusztigF

variable {R X : Type*} [CommRing R] [DecidableEq X]

/-- The values of the Verma-type operator on words.-/
def vermaOpWord (i : X) (c : (X →₀ ℕ) → R) : List X → FreeAlgebra R X
  | [] => 0
  | j :: w => ι R j * vermaOpWord i c w +
      if i = j then c (wordWeight w) • wordBasis R X w else 0

/-- The Verma-type operator `E` on `FreeAlgebra R X`: `E(1) = 0` and
`E(xⱼ y) = xⱼ E(y) + δᵢⱼ c(μ) y` for `y` of weight `μ`.-/
def vermaOp (i : X) (c : (X →₀ ℕ) → R) : FreeAlgebra R X →ₗ[R] FreeAlgebra R X :=
  (wordBasis R X).constr R (vermaOpWord i c)

omit [DecidableEq X] in
/-- The operator `y ↦ c(μ) y` on words `y` of weight `μ`.-/
def weightScale (c : (X →₀ ℕ) → R) : FreeAlgebra R X →ₗ[R] FreeAlgebra R X :=
  (wordBasis R X).constr R fun w ↦ c (wordWeight w) • wordBasis R X w

/--
@isnad1 id=eq.0h5v.s8.eb3fd4ce68c7 from=translated src=- shape=48073ce3 vocab=4f734926
-/
@[simp] lemma vermaOp_wordBasis (i : X) (c : (X →₀ ℕ) → R) (w : List X) :
    vermaOp i c (wordBasis R X w) = vermaOpWord i c w :=
  (wordBasis R X).constr_basis R _ w

omit [DecidableEq X] in
/--
@isnad1 id=eq.0h4v.s9.7d1cc9038507 from=translated src=- shape=40ed0aea vocab=26e30ef6
-/
@[simp] lemma weightScale_wordBasis (c : (X →₀ ℕ) → R) (w : List X) :
    weightScale c (wordBasis R X w) = c (wordWeight w) • wordBasis R X w :=
  (wordBasis R X).constr_basis R _ w

omit [DecidableEq X] in
/--
@isnad1 id=eq.1h5v.s8.700841664f4a from=translated src=- shape=effb361d vocab=10102502
-/
lemma weightScale_of_mem (c : (X →₀ ℕ) → R) {μ : X →₀ ℕ} {y : FreeAlgebra R X}
    (hy : y ∈ wordSpan R μ) : weightScale c y = c μ • y := by
  induction hy using wordSpan_induction with
  | word w hw => rw [weightScale_wordBasis, hw]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul a y _ hy => rw [map_smul, hy, smul_comm]

/--
@isnad1 id=eq.0h4v.s8.0a7b3a2b8cb9 from=translated src=- shape=b450ffa8 vocab=9110b5a4
-/
@[simp] lemma vermaOp_one (i : X) (c : (X →₀ ℕ) → R) : vermaOp i c 1 = 0 := by
  rw [← wordBasis_nil, vermaOp_wordBasis, vermaOpWord]

/-- The defining recursion `E(xⱼ y) = xⱼ E(y) + δᵢⱼ c(|y|) y`.
@isnad1 id=eq.0h6v.s9.b7e3652fde62 from=translated src=- shape=1c7b8c45 vocab=2f68300d
-/
theorem vermaOp_ι_mul (i : X) (c : (X →₀ ℕ) → R) (j : X) (y : FreeAlgebra R X) :
    vermaOp i c (ι R j * y) = ι R j * vermaOp i c y + if i = j then weightScale c y else 0 := by
  induction y using induction_wordBasis with
  | zero => simp
  | add y z hy hz =>
    rw [mul_add, map_add, hy, hz, map_add, mul_add]
    split_ifs
    · rw [map_add]; abel
    · simp only [add_zero]
  | smul a y hy =>
    rw [mul_smul_comm, map_smul, hy, map_smul, smul_add, mul_smul_comm]
    split_ifs <;> simp
  | word w =>
    rw [ι_mul_wordBasis, vermaOp_wordBasis, vermaOp_wordBasis, vermaOpWord, weightScale_wordBasis]

/-- The operator `E_w = E_{iₙ} ∘ ⋯ ∘ E_{i₁}` of a word `w = [i₁, …, iₙ]`.-/
def vermaWordOp (c : X → (X →₀ ℕ) → R) : List X → Module.End R (FreeAlgebra R X)
  | [] => 1
  | i :: w => vermaWordOp c w * vermaOp i (c i)

/--
@isnad1 id=eq.0h3v.s7.fc575224ada9 from=translated src=- shape=e2dde09b vocab=316f8a20
-/
@[simp] lemma vermaWordOp_nil (c : X → (X →₀ ℕ) → R) : vermaWordOp c [] = 1 := rfl

/--
@isnad1 id=eq.0h6v.s9.0c7a557a21b8 from=translated src=- shape=e673697a vocab=d400b63d
-/
lemma vermaWordOp_cons (c : X → (X →₀ ℕ) → R) (i : X) (w : List X) (y : FreeAlgebra R X) :
    vermaWordOp c (i :: w) y = vermaWordOp c w (vermaOp i (c i) y) := rfl

/-- The Shapovalov-type pairing `S(w, y) = ε(E_w y)` between a word `w` and `y`.-/
def vermaForm (c : X → (X →₀ ℕ) → R) (w : List X) : FreeAlgebra R X →ₗ[R] R :=
  (algebraMapInv : FreeAlgebra R X →ₐ[R] R).toLinearMap ∘ₗ vermaWordOp c w

/--
@isnad1 id=eq.0h5v.s9.71e4c7ecef6f from=translated src=- shape=cb6ec4e1 vocab=d0efc8ce
-/
lemma vermaForm_apply (c : X → (X →₀ ℕ) → R) (w : List X) (y : FreeAlgebra R X) :
    vermaForm c w y = algebraMapInv (vermaWordOp c w y) := rfl

/--
@isnad1 id=eq.0h4v.s8.36d24abbdfe8 from=translated src=- shape=c7fc5642 vocab=b7641bfb
-/
@[simp] lemma vermaForm_nil (c : X → (X →₀ ℕ) → R) (y : FreeAlgebra R X) :
    vermaForm c [] y = algebraMapInv y := rfl

/--
@isnad1 id=eq.0h6v.s9.d1543e5a79a4 from=translated src=- shape=3d7ced3d vocab=8c3f2325
-/
lemma vermaForm_cons (c : X → (X →₀ ℕ) → R) (i : X) (w : List X) (y : FreeAlgebra R X) :
    vermaForm c (i :: w) y = vermaForm c w (vermaOp i (c i) y) := rfl

/-! ### Naturality -/

variable {S : Type*} [CommRing S] (φ : R →+* S)

/--
@isnad1 id=eq.0h7v.s7.23e28de74121 from=translated src=- shape=42b8b891 vocab=cb4f2947
-/
lemma mapCoeffs_vermaOpWord (i : X) (c : (X →₀ ℕ) → R) (w : List X) :
    mapCoeffs φ (vermaOpWord i c w) = vermaOpWord i (φ ∘ c) w := by
  induction w with
  | nil => simp [vermaOpWord]
  | cons j w ih =>
    simp only [vermaOpWord, map_add, map_mul, mapCoeffs_ι, ih]
    split_ifs <;> simp [mapCoeffs_smul, map_list_prod, Function.comp_def]

/-- The Verma-type operators commute with change of coefficients.
@isnad1 id=eq.0h7v.s9.c42a59d0048b from=translated src=- shape=2a771cf1 vocab=198ae1a0
-/
theorem mapCoeffs_vermaOp (i : X) (c : (X →₀ ℕ) → R) (y : FreeAlgebra R X) :
    mapCoeffs φ (vermaOp i c y) = vermaOp i (φ ∘ c) (mapCoeffs φ y) := by
  induction y using induction_wordBasis with
  | zero => simp
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  | smul a y hy => rw [map_smul, mapCoeffs_smul, hy, mapCoeffs_smul, map_smul]
  | word w => rw [vermaOp_wordBasis, mapCoeffs_vermaOpWord, mapCoeffs_wordBasis, vermaOp_wordBasis]

/--
@isnad1 id=eq.0h7v.s9.e5028773aae3 from=translated src=- shape=f17c6642 vocab=8e36c2e2
-/
theorem mapCoeffs_vermaWordOp (c : X → (X →₀ ℕ) → R) (w : List X) (y : FreeAlgebra R X) :
    mapCoeffs φ (vermaWordOp c w y) = vermaWordOp (fun i ↦ φ ∘ c i) w (mapCoeffs φ y) := by
  induction w generalizing y with
  | nil => rfl
  | cons i w ih => rw [vermaWordOp_cons, ih, mapCoeffs_vermaOp, vermaWordOp_cons]

/-- The Shapovalov-type pairing is natural in the coefficient ring.
@isnad1 id=eq.0h7v.s9.3d40e4008a05 from=translated src=- shape=a9db2270 vocab=d996e197
-/
theorem map_vermaForm (c : X → (X →₀ ℕ) → R) (w : List X) (y : FreeAlgebra R X) :
    φ (vermaForm c w y) = vermaForm (fun i ↦ φ ∘ c i) w (mapCoeffs φ y) := by
  rw [vermaForm_apply, vermaForm_apply, ← mapCoeffs_vermaWordOp, algebraMapInv_mapCoeffs]

/-! ### Weights -/

omit [DecidableEq X] in
/--
@isnad1 id=eq.1h3v.s7.78d89e969208 from=translated src=- shape=ea9d01ca vocab=e77af7f8
-/
lemma single_add_tsub_single {μ : X →₀ ℕ} {i : X} (h : μ i ≠ 0) :
    μ - Finsupp.single i 1 + Finsupp.single i 1 = μ := by
  classical
  ext j
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs with hij
  · subst hij; omega
  · omega

/--
@isnad1 id=eq.1h5v.s6.048b37fb7696 from=translated src=- shape=a34aac4e vocab=bc3a0357
-/
lemma vermaOpWord_eq_zero (i : X) (c : (X →₀ ℕ) → R) (w : List X) (hw : wordWeight w i = 0) :
    vermaOpWord i c w = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    have hij : i ≠ j := by rintro rfl; simp at hw
    have hw' : wordWeight w i = 0 := by
      simp only [wordWeight_cons, Finsupp.add_apply] at hw; omega
    simp [vermaOpWord, ih hw', hij]

/--
@isnad1 id=mem.0h5v.s7.4ce00ff5a9ed from=translated src=- shape=3dbe69f4 vocab=71103bcd
-/
lemma vermaOpWord_mem (i : X) (c : (X →₀ ℕ) → R) (w : List X) :
    vermaOpWord i c w ∈ wordSpan R (wordWeight w - Finsupp.single i 1) := by
  induction w with
  | nil => simp [vermaOpWord]
  | cons j w ih =>
    rw [vermaOpWord]
    refine add_mem ?_ ?_
    · by_cases hwi : wordWeight w i = 0
      · rw [vermaOpWord_eq_zero i c w hwi, mul_zero]; exact zero_mem _
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
@isnad1 id=mem.1h6v.s9.1390708fba63 from=translated src=- shape=c8405f2b vocab=12fe1daf
-/
lemma vermaOp_mem_wordSpan (i : X) (c : (X →₀ ℕ) → R) {μ : X →₀ ℕ} {y : FreeAlgebra R X}
    (hy : y ∈ wordSpan R μ) : vermaOp i c y ∈ wordSpan R (μ - Finsupp.single i 1) := by
  induction hy using wordSpan_induction with
  | word w hw => rw [vermaOp_wordBasis, ← hw]; exact vermaOpWord_mem i c w
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

/--
@isnad1 id=eq.2h6v.s9.af216de8ab59 from=translated src=- shape=c7da2d2d vocab=01ccf436
-/
lemma vermaOp_eq_zero_of_mem (i : X) (c : (X →₀ ℕ) → R) {μ : X →₀ ℕ} (hμ : μ i = 0)
    {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) : vermaOp i c y = 0 := by
  induction hy using wordSpan_induction with
  | word w hw => rw [vermaOp_wordBasis, vermaOpWord_eq_zero i c w (hw ▸ hμ)]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul a y _ hy => rw [map_smul, hy, smul_zero]

/--
@isnad1 id=and.1h6v.s9.8c0306c3ebd9 from=translated src=- shape=d1b79597 vocab=d1e2098e
-/
lemma vermaWordOp_mem (c : X → (X →₀ ℕ) → R) (w : List X) {μ : X →₀ ℕ} {y : FreeAlgebra R X}
    (hy : y ∈ wordSpan R μ) :
    vermaWordOp c w y ∈ wordSpan R (μ - wordWeight w) ∧
      (¬ wordWeight w ≤ μ → vermaWordOp c w y = 0) := by
  induction w generalizing μ y with
  | nil => simpa using hy
  | cons i w ih =>
    rw [vermaWordOp_cons]
    by_cases hμi : μ i = 0
    · rw [vermaOp_eq_zero_of_mem i (c i) hμi hy, map_zero]
      exact ⟨zero_mem _, fun _ ↦ rfl⟩
    · obtain ⟨h1, h2⟩ := ih (vermaOp_mem_wordSpan i (c i) hy)
      have e : μ - Finsupp.single i 1 - wordWeight w = μ - wordWeight (i :: w) := by
        rw [wordWeight_cons, tsub_tsub]
      refine ⟨e ▸ h1, fun h ↦ h2 fun hle ↦ h ?_⟩
      rw [wordWeight_cons, ← single_add_tsub_single hμi, add_comm (Finsupp.single i 1)]
      exact add_le_add_left hle _

/-- `S(w, y) = 0` unless `y` has the weight of the word `w`.
@isnad1 id=eq.2h6v.s8.49396f661832 from=translated src=- shape=cfe06c8d vocab=7f0ec89c
-/
theorem vermaForm_eq_zero_of_ne (c : X → (X →₀ ℕ) → R) (w : List X) {μ : X →₀ ℕ}
    (hμ : wordWeight w ≠ μ) {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) :
    vermaForm c w y = 0 := by
  obtain ⟨h1, h2⟩ := vermaWordOp_mem c w hy
  rw [vermaForm_apply]
  by_cases hle : wordWeight w ≤ μ
  · refine algebraMapInv_eq_zero_of_mem_wordSpan (fun h0 ↦ hμ ?_) h1
    exact le_antisymm hle (tsub_eq_zero_iff_le.1 h0)
  · rw [h2 hle, map_zero]

end Tengoku.LieLean.LusztigF
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
