/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.Seed.LinearAlgebra.FreeAlgebra
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.LusztigF.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Words in free algebras and change of coefficients

For a commutative ring `R`, the free algebra `FreeAlgebra R X` has the basis of words
`FreeAlgebra.wordBasis R X`, `[x₁, …, xₙ] ↦ x₁ ⋯ xₙ` (a reindexing of Mathlib's
`FreeAlgebra.basisFreeMonoid` by lists). A ring homomorphism `φ : R → S` induces the ring
homomorphism `FreeAlgebra.mapCoeffs φ : FreeAlgebra R X → FreeAlgebra S X`, `xᵢ ↦ xᵢ`, which acts
on coordinates in the word basis by `φ`.

We also record the subspaces `FreeAlgebra.wordSpan R μ` spanned by the words of weight `μ ∈ ℕ[X]`
(for a field these are the weight spaces `LusztigF.weightSpace` of Lusztig's algebra `'f`).

## Main definitions

* `FreeAlgebra.wordBasis R X`: the basis of words.
* `FreeAlgebra.mapCoeffs φ`: change of coefficients along `φ : R →+* S`.
* `FreeAlgebra.wordSpan R μ`: the span of the words of weight `μ`.

## Main results

* `FreeAlgebra.wordBasis_apply`, `FreeAlgebra.ι_mul_wordBasis`.
* `FreeAlgebra.mapCoeffs_wordBasis`, `FreeAlgebra.wordBasis_repr_mapCoeffs`,
  `FreeAlgebra.algebraMapInv_mapCoeffs`.

## References

Elementary; this is API for Mathlib's `FreeAlgebra` used in the proof of the quantum Gabber–Kac
theorem.
-/

noncomputable section
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean 
namespace FreeAlgebra

variable (R X : Type*) [CommRing R]

/-- The basis of `FreeAlgebra R X` given by the words `[x₁, …, xₙ] ↦ x₁ ⋯ xₙ`.-/
def wordBasis : Module.Basis (List X) R (FreeAlgebra R X) :=
  (basisFreeMonoid R X).reindex FreeMonoid.ofList.symm

variable {R X}

/--
@isnad1 id=eq.0h3v.s7.9bc7133c798e from=translated src=- shape=e5fb50c9 vocab=1bb741fa
-/
@[simp] lemma wordBasis_apply (w : List X) : wordBasis R X w = (w.map (ι R)).prod := by
  simp [wordBasis, basisFreeMonoid, equivMonoidAlgebraFreeMonoid, FreeMonoid.lift_apply]

/--
@isnad1 id=eq.0h2v.s7.b5d2824abea0 from=translated src=- shape=9c0afd07 vocab=14aace87
-/
@[simp] lemma wordBasis_nil : wordBasis R X [] = 1 := by simp

/--
@isnad1 id=eq.0h4v.s8.da32e611a8f1 from=translated src=- shape=db71e07e vocab=49d6b500
-/
lemma ι_mul_wordBasis (x : X) (w : List X) :
    ι R x * wordBasis R X w = wordBasis R X (x :: w) := by
  simp

/--
@isnad1 id=eq.0h4v.s8.35e2c036092b from=translated src=- shape=0f7ba3b9 vocab=b5d5f1a6
-/
lemma wordBasis_append (w w' : List X) :
    wordBasis R X (w ++ w') = wordBasis R X w * wordBasis R X w' := by
  simp

/--
@isnad1 id=eq.0h2v.s8.627fbc1e748e from=translated src=- shape=a93d31e6 vocab=3f984aa6
-/
lemma span_wordBasis : Submodule.span R (Set.range (wordBasis R X)) = ⊤ :=
  (wordBasis R X).span_eq

/-- Induction over the span of the words.
@isnad1 id=var.0h8v.s8.be878f74f734 from=translated src=- shape=64390d35 vocab=132239e8
-/
theorem induction_wordBasis {P : FreeAlgebra R X → Prop} (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (c : R) x, P x → P (c • x))
    (word : ∀ w, P (wordBasis R X w)) (x : FreeAlgebra R X) : P x := by
  have hx : x ∈ Submodule.span R (Set.range (wordBasis R X)) := by
    rw [span_wordBasis]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨w, rfl⟩ := hy; exact word w
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul c y _ hy => exact smul c y hy

/-! ### Change of coefficients -/

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- The ring homomorphism `FreeAlgebra R X → FreeAlgebra S X`, `xᵢ ↦ xᵢ`, induced by a ring
homomorphism `φ : R → S` on coefficients.-/
def mapCoeffs : FreeAlgebra R X →+* FreeAlgebra S X :=
  letI : Algebra R (FreeAlgebra S X) := Algebra.compHom (FreeAlgebra S X) φ
  (lift R (ι S)).toRingHom

/--
@isnad1 id=eq.0h5v.s7.e3e3d91bef67 from=translated src=- shape=63a3fb35 vocab=3627a9b5
-/
@[simp] lemma mapCoeffs_ι (x : X) : mapCoeffs φ (ι R x) = ι S x := by
  simp [mapCoeffs]

/--
@isnad1 id=eq.0h5v.s8.47a260d53cc4 from=translated src=- shape=24e6de31 vocab=92f324c1
-/
@[simp] lemma mapCoeffs_algebraMap (c : R) :
    mapCoeffs φ (algebraMap R (FreeAlgebra R X) c) = algebraMap S _ (φ c) := by
  let _ : Algebra R (FreeAlgebra S X) := Algebra.compHom (FreeAlgebra S X) φ
  exact (lift R (ι S)).commutes c

/--
@isnad1 id=eq.0h6v.s8.db2333d83e2d from=translated src=- shape=8de5a241 vocab=6d6b286e
-/
lemma mapCoeffs_smul (c : R) (x : FreeAlgebra R X) :
    mapCoeffs φ (c • x) = φ c • mapCoeffs φ x := by
  rw [Algebra.smul_def, map_mul, mapCoeffs_algebraMap, ← Algebra.smul_def]

/--
@isnad1 id=eq.0h5v.s8.3ede178c49a5 from=translated src=- shape=2c285029 vocab=de2b7ef7
-/
@[simp] lemma mapCoeffs_wordBasis (w : List X) :
    mapCoeffs φ (wordBasis R X w) = wordBasis S X w := by
  simp [map_list_prod, Function.comp_def]

/--
@isnad1 id=eq.0h5v.s9.21259d735dfe from=translated src=- shape=efffd02a vocab=0c917276
-/
lemma mapCoeffs_eq_sum (x : FreeAlgebra R X) :
    mapCoeffs φ x = ((wordBasis R X).repr x).sum fun w c ↦ φ c • wordBasis S X w := by
  conv_lhs => rw [← (wordBasis R X).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  simp only [mapCoeffs_smul, mapCoeffs_wordBasis]

/-- `mapCoeffs φ` acts on the coordinates in the word basis by `φ`.
@isnad1 id=eq.0h6v.s10.b5a84888826d from=translated src=- shape=b989ca41 vocab=7b44fe32
-/
theorem wordBasis_repr_mapCoeffs (x : FreeAlgebra R X) (w : List X) :
    (wordBasis S X).repr (mapCoeffs φ x) w = φ ((wordBasis R X).repr x w) := by
  classical
  rw [mapCoeffs_eq_sum, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h, map_zero]

/-- The augmentation commutes with `mapCoeffs φ`.
@isnad1 id=eq.0h5v.s8.71f93b4e19aa from=translated src=- shape=0ab8dcc0 vocab=5649b329
-/
theorem algebraMapInv_mapCoeffs (x : FreeAlgebra R X) :
    algebraMapInv (mapCoeffs φ x) = φ (algebraMapInv x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [mapCoeffs_algebraMap]
    simp [algebraMapInv]
  | grade1 x => simp [algebraMapInv]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-! ### Weights of words -/

variable (R) in
/-- The span of the words of weight `μ ∈ ℕ[X]` in `FreeAlgebra R X`.-/
def wordSpan (μ : X →₀ ℕ) : Submodule R (FreeAlgebra R X) :=
  Submodule.span R ((fun w ↦ (w.map (ι R)).prod) '' {w | LusztigF.wordWeight w = μ})

/--
@isnad1 id=mem.0h3v.s8.31c56729d872 from=translated src=- shape=e245cd8b vocab=841670d1
-/
lemma wordBasis_mem_wordSpan (w : List X) :
    wordBasis R X w ∈ wordSpan R (LusztigF.wordWeight w) := by
  rw [wordBasis_apply]
  exact Submodule.subset_span ⟨w, rfl, rfl⟩

/--
@isnad1 id=mem.1h4v.s8.dc5edf4e0a77 from=translated src=- shape=0c540cbd vocab=8ff986e7
-/
lemma wordBasis_mem_wordSpan_of_eq {w : List X} {μ : X →₀ ℕ} (h : LusztigF.wordWeight w = μ) :
    wordBasis R X w ∈ wordSpan R μ :=
  h ▸ wordBasis_mem_wordSpan w

/-- Induction over `wordSpan R μ`.
@isnad1 id=var.1h9v.s10.df19f76c03d4 from=translated src=- shape=47cc2580 vocab=d3394f4f
-/
theorem wordSpan_induction {μ : X →₀ ℕ} {P : (x : FreeAlgebra R X) → x ∈ wordSpan R μ → Prop}
    (word : ∀ w (hw : LusztigF.wordWeight w = μ),
      P (wordBasis R X w) (wordBasis_mem_wordSpan_of_eq hw))
    (zero : P 0 (zero_mem _))
    (add : ∀ x y hx hy, P x hx → P y hy → P (x + y) (add_mem hx hy))
    (smul : ∀ (c : R) x hx, P x hx → P (c • x) (Submodule.smul_mem _ c hx))
    {x : FreeAlgebra R X} (hx : x ∈ wordSpan R μ) : P x hx := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have := word w hw
    simpa using this
  | zero => exact zero
  | add y z hy hz ihy ihz => exact add y z hy hz ihy ihz
  | smul c y hy ih => exact smul c y hy ih

/--
@isnad1 id=mem.1h5v.s8.1c054bb4de1a from=translated src=- shape=320f2655 vocab=c353aa96
-/
lemma ι_mul_mem_wordSpan (x : X) {μ : X →₀ ℕ} {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) :
    ι R x * y ∈ wordSpan R (Finsupp.single x 1 + μ) := by
  induction hy using wordSpan_induction with
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  | word w hw =>
    rw [ι_mul_wordBasis]
    exact wordBasis_mem_wordSpan_of_eq (by rw [LusztigF.wordWeight_cons, hw])

/--
@isnad1 id=eq.2h4v.s8.f8d6184df89c from=translated src=- shape=a85ac74b vocab=bc0208d3
-/
lemma algebraMapInv_eq_zero_of_mem_wordSpan {μ : X →₀ ℕ} (hμ : μ ≠ 0) {y : FreeAlgebra R X}
    (hy : y ∈ wordSpan R μ) : algebraMapInv y = 0 := by
  induction hy using wordSpan_induction with
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]
  | word w hw =>
    cases w with
    | nil => exact absurd hw.symm (by simpa using hμ)
    | cons x w => simp [algebraMapInv]

end FreeAlgebra
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
