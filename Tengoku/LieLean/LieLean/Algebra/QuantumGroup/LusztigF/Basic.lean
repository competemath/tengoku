/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.Seed.Algebra.FreeAlgebra
import Tengoku.Seed.Algebra.MonoidAlgebra.Basic
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.CartanDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lusztig's algebra `'f`: grading, twists and skew derivations

Let `(I, ·)` be a Cartan datum, `k` a field and `v ∈ k` (Lusztig takes `k = ℚ(v)`; the
downstream specialization is `k = RatFunc ℚ`, `v = RatFunc.X`). Lusztig's algebra `'f`
([Lus] 1.2.1) is the free associative `k`-algebra on generators `θᵢ`, `i ∈ I`; we take
it to be `FreeAlgebra k I` (`LusztigF k I` is an abbreviation). It is graded by `ℕ[I]`, modelled
as `I →₀ ℕ`: `'f_ν` is spanned by the monomials `θ_{i₁} ⋯ θ_{iₙ}` with `i₁ + ⋯ + iₙ = ν`.

For `i ∈ I` we define
* the twist `σᵢ = twist D v i`, the algebra automorphism `θⱼ ↦ v^{i·j} θⱼ`, so that
  `σᵢ(x) = v^{i·|x|} x` for homogeneous `x`;
* the skew derivations `rᵢ` and `ᵢr` of [Lus] 1.2.13, characterized by `rᵢ(θⱼ) = δᵢⱼ`,
  `ᵢr(θⱼ) = δᵢⱼ` and
  `rᵢ(xy) = x rᵢ(y) + v^{|y|·i} rᵢ(x) y = x rᵢ(y) + rᵢ(x) σᵢ(y)`,
  `ᵢr(xy) = ᵢr(x) y + v^{|x|·i} x ᵢr(y) = ᵢr(x) y + σᵢ(x) ᵢr(y)`.
  They are constructed as the off-diagonal entries of algebra homomorphisms from `'f` to
  `2 × 2` upper triangular matrices over `'f`.

## Main definitions

* `LusztigF k I`: the free algebra `'f`; `LusztigF.θ k i`: its generators.
* `LusztigF.counit`: the augmentation `'f → k` (the constant term).
* `LusztigF.monomial`, `LusztigF.wordWeight`, `LusztigF.weightSpace ν` (= `'f_ν`).
* `LusztigF.gradingHom`: the algebra map `'f → 'f[ℕ[I]]`, `θᵢ ↦ θᵢ e^{i}`, encoding the grading.
* `LusztigF.twist D v i` (`σᵢ`), `LusztigF.rDeriv D v i` (`rᵢ`), `LusztigF.lDeriv D v i` (`ᵢr`).

## Main results

* `LusztigF.induction_left`, `LusztigF.induction_right`: induction on `'f` by left or right
  multiplication by generators.
* `LusztigF.mul_mem_weightSpace`, `LusztigF.iSup_weightSpace`, `LusztigF.iSupIndep_weightSpace`:
  `'f = ⊕_ν 'f_ν` is a grading; `LusztigF.finiteDimensional_weightSpace`.
* `LusztigF.rDeriv_mul`, `LusztigF.lDeriv_mul`, `LusztigF.rDeriv_θ`, `LusztigF.lDeriv_θ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.2.
-/

noncomputable section
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean 
open Finset

variable {k I : Type*} [Field k]

/-- Lusztig's algebra `'f` ([Lus] 1.2.1): the free associative `k`-algebra with `1` on
generators `θᵢ`, `i ∈ I`.-/
abbrev _root_.Tengoku.LieLean.LusztigF (k I : Type*) [Field k] := FreeAlgebra k I

namespace Tengoku.LieLean.LusztigF

variable (k) in
/-- The generator `θᵢ` of `'f`.-/
abbrev θ (i : I) : LusztigF k I := FreeAlgebra.ι k i

/-- The augmentation `'f → k` (the constant term), the counit of `'f`.-/
abbrev counit : LusztigF k I →ₐ[k] k := FreeAlgebra.algebraMapInv

/--
@isnad1 id=eq.0h3v.s7.265138ed3362 from=translated src=- shape=643a5636 vocab=5a7d1abd
-/
@[simp] lemma counit_θ (i : I) : counit (θ k i) = 0 := by
  simp [counit, FreeAlgebra.algebraMapInv]

/--
@isnad1 id=eq.0h3v.s7.b655a20d82b9 from=translated src=- shape=87643048 vocab=e6c7eea3
-/
@[simp] lemma counit_algebraMap (c : k) : counit (algebraMap k (LusztigF k I) c) = c :=
  FreeAlgebra.algebraMap_leftInverse c

/-! ### Induction principles -/

/-- Induction on `'f` by left multiplication with generators.
@isnad1 id=var.0h8v.s8.38a4ef3bcad9 from=translated src=- shape=b2b84623 vocab=f5a115b2
-/
theorem induction_left {P : LusztigF k I → Prop} (algebraMap : ∀ c, P (algebraMap k _ c))
    (smul : ∀ (c : k) x, P x → P (c • x)) (add : ∀ x y, P x → P y → P (x + y))
    (θ_mul : ∀ i x, P x → P (θ k i * x)) (x : LusztigF k I) : P x := by
  have key : ∀ a : LusztigF k I, ∀ y, P y → P (a * y) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c => intro y hy; rw [← Algebra.smul_def]; exact smul c y hy
    | grade1 i => exact θ_mul i
    | mul a b ha hb => intro y hy; rw [mul_assoc]; exact ha _ (hb _ hy)
    | add a b ha hb => intro y hy; rw [add_mul]; exact add _ _ (ha _ hy) (hb _ hy)
  simpa using key x 1 (by simpa using algebraMap 1)

/-- Induction on `'f` by right multiplication with generators.
@isnad1 id=var.0h8v.s8.05773c9b1224 from=translated src=- shape=4fc16ffa vocab=f5a115b2
-/
theorem induction_right {P : LusztigF k I → Prop} (algebraMap : ∀ c, P (algebraMap k _ c))
    (smul : ∀ (c : k) x, P x → P (c • x)) (add : ∀ x y, P x → P y → P (x + y))
    (mul_θ : ∀ x i, P x → P (x * θ k i)) (x : LusztigF k I) : P x := by
  have key : ∀ a : LusztigF k I, ∀ y, P y → P (y * a) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c => intro y hy; rw [← Algebra.commutes, ← Algebra.smul_def]; exact smul c y hy
    | grade1 i => exact fun y hy ↦ mul_θ y i hy
    | mul a b ha hb => intro y hy; rw [← mul_assoc]; exact hb _ (ha _ hy)
    | add a b ha hb => intro y hy; rw [mul_add]; exact add _ _ (ha _ hy) (hb _ hy)
  simpa using key x 1 (by simpa using algebraMap 1)

/-! ### Monomials and the grading -/

variable (k) in
/-- The monomial `θ_{i₁} ⋯ θ_{iₙ}` of a word `[i₁, …, iₙ]`.-/
def monomial (w : List I) : LusztigF k I := (w.map (θ k)).prod

/-- The weight `i₁ + ⋯ + iₙ ∈ ℕ[I]` of a word `[i₁, …, iₙ]`.-/
def wordWeight (w : List I) : I →₀ ℕ := (w.map fun i ↦ Finsupp.single i 1).sum

/--
@isnad1 id=eq.0h2v.s5.7a3c7bedf965 from=translated src=- shape=b393f0ee vocab=1647720c
-/
@[simp] lemma monomial_nil : monomial k ([] : List I) = 1 := rfl

/--
@isnad1 id=eq.0h4v.s5.976636b5dbbc from=translated src=- shape=3236e9d3 vocab=acc2d96d
-/
@[simp] lemma monomial_cons (i : I) (w : List I) :
    monomial k (i :: w) = θ k i * monomial k w := by simp [monomial]

/--
@isnad1 id=eq.0h4v.s6.729b8e470f83 from=translated src=- shape=f60ddac9 vocab=58c6b6ee
-/
lemma monomial_append (w w' : List I) :
    monomial k (w ++ w') = monomial k w * monomial k w' := by simp [monomial]

/--
@isnad1 id=eq.0h1v.s5.e33bc95e8723 from=translated src=- shape=9e49d37a vocab=0b61c718
-/
@[simp] lemma wordWeight_nil : wordWeight ([] : List I) = 0 := rfl

/--
@isnad1 id=eq.0h3v.s6.aa67098d2fba from=translated src=- shape=4c37c369 vocab=cf6b4c7b
-/
@[simp] lemma wordWeight_cons (i : I) (w : List I) :
    wordWeight (i :: w) = Finsupp.single i 1 + wordWeight w := by simp [wordWeight]

/--
@isnad1 id=eq.0h3v.s6.dbf44873b2c5 from=translated src=- shape=7e4b7a89 vocab=cf3e72d7
-/
lemma wordWeight_append (w w' : List I) :
    wordWeight (w ++ w') = wordWeight w + wordWeight w' := by simp [wordWeight]

/--
@isnad1 id=eq.0h3v.s5.09e59b65e80e from=translated src=- shape=9dc43b16 vocab=46407cf1
-/
lemma wordWeight_apply (w : List I) (i : I) [DecidableEq I] :
    wordWeight w i = w.count i := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [wordWeight_cons, Finsupp.add_apply, ih, List.count_cons, Finsupp.single_apply,
      beq_iff_eq]
    split_ifs <;> omega

/--
@isnad1 id=eq.0h2v.s4.e110f42e0927 from=translated src=- shape=373b5316 vocab=afb1ffe3
-/
lemma length_eq_sum_wordWeight (w : List I) : w.length = (wordWeight w).sum fun _ n ↦ n := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordWeight_cons, Finsupp.sum_add_index' (by simp) (by simp), ← ih]
    simp [add_comm]

variable (k) in
/-- The weight space `'f_ν`, spanned by the monomials of weight `ν` ([Lus] 1.2.1).-/
def weightSpace (ν : I →₀ ℕ) : Submodule k (LusztigF k I) :=
  Submodule.span k (monomial k '' {w | wordWeight w = ν})

/--
@isnad1 id=mem.0h3v.s7.a42aecfb663d from=translated src=- shape=d1a136de vocab=76824809
-/
lemma monomial_mem_weightSpace (w : List I) : monomial k w ∈ weightSpace k (wordWeight w) :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

/--
@isnad1 id=mem.0h2v.s7.f2cd888e245f from=translated src=- shape=20767247 vocab=511a6e24
-/
lemma one_mem_weightSpace : (1 : LusztigF k I) ∈ weightSpace k 0 :=
  monomial_mem_weightSpace (k := k) ([] : List I)

/--
@isnad1 id=mem.0h3v.s8.031f1ffe16df from=translated src=- shape=84b263f3 vocab=c199f99d
-/
lemma algebraMap_mem_weightSpace (c : k) : algebraMap k (LusztigF k I) c ∈ weightSpace k 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ one_mem_weightSpace

/--
@isnad1 id=mem.0h3v.s7.a7f386a61aa5 from=translated src=- shape=490e5afb vocab=a144f9bf
-/
lemma θ_mem_weightSpace (i : I) : θ k i ∈ weightSpace k (Finsupp.single i 1) := by
  simpa [monomial] using monomial_mem_weightSpace (k := k) [i]

/--
@isnad1 id=mem.2h6v.s9.049434fa415a from=translated src=- shape=7de7f900 vocab=e7ce91f6
-/
lemma mul_mem_weightSpace {ν μ : I →₀ ℕ} {x y : LusztigF k I} (hx : x ∈ weightSpace k ν)
    (hy : y ∈ weightSpace k μ) : x * y ∈ weightSpace k (ν + μ) := by
  have : weightSpace k ν * weightSpace k μ ≤ weightSpace k (ν + μ) := by
    rw [weightSpace, weightSpace, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, _, ⟨w', hw', rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq] at hw hw'
    dsimp only
    rw [← monomial_append, ← hw, ← hw', ← wordWeight_append]
    exact monomial_mem_weightSpace _
  exact this (Submodule.mul_mem_mul hx hy)

/--
@isnad1 id=eq.0h2v.s8.fdffddaae7e0 from=translated src=- shape=2a9b26d8 vocab=578f7b4d
-/
lemma span_monomial : Submodule.span k (Set.range (monomial k (I := I))) = ⊤ := by
  suffices h : ∀ x, x ∈ Submodule.span k (Set.range (monomial k (I := I))) from
    eq_top_iff.2 fun x _ ↦ h x
  intro x
  induction x using induction_left with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | smul c x hx => exact Submodule.smul_mem _ _ hx
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | θ_mul i x hx =>
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact Submodule.subset_span ⟨i :: w, monomial_cons i w⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/--
@isnad1 id=eq.0h2v.s8.a78c4cf23e36 from=translated src=- shape=ea8d1b85 vocab=331a6f03
-/
theorem iSup_weightSpace : ⨆ ν, weightSpace k (I := I) ν = ⊤ := by
  rw [eq_top_iff, ← span_monomial, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace w)

variable (k I) in
/-- The algebra homomorphism `'f → 'f[ℕ[I]]`, `θᵢ ↦ θᵢ e^{i}`, which encodes the grading:
`gradingHom x = x e^ν` for `x ∈ 'f_ν` (`gradingHom_of_mem`).-/
def gradingHom : LusztigF k I →ₐ[k] AddMonoidAlgebra (LusztigF k I) (I →₀ ℕ) :=
  FreeAlgebra.lift k fun i ↦ AddMonoidAlgebra.single (Finsupp.single i 1) (θ k i)

/--
@isnad1 id=eq.0h3v.s8.d1e39d0e476d from=translated src=- shape=33f8be87 vocab=6a55764a
-/
lemma gradingHom_monomial (w : List I) :
    gradingHom k I (monomial k w) = AddMonoidAlgebra.single (wordWeight w) (monomial k w) := by
  induction w with
  | nil => simp [AddMonoidAlgebra.one_def]
  | cons i w ih =>
    rw [monomial_cons, map_mul, ih]
    simp [gradingHom, AddMonoidAlgebra.single_mul_single]

/--
@isnad1 id=eq.1h4v.s9.a038598a8746 from=translated src=- shape=0fa167b8 vocab=8568c4d8
-/
lemma gradingHom_of_mem {ν : I →₀ ℕ} {x : LusztigF k I} (hx : x ∈ weightSpace k ν) :
    gradingHom k I x = AddMonoidAlgebra.single ν x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [gradingHom_monomial, hw]
  | zero => simp [AddMonoidAlgebra.single_zero]
  | add y z _ _ hy hz => rw [map_add, hy, hz, AddMonoidAlgebra.single_add]
  | smul c y _ hy =>
    rw [map_smul, hy, AddMonoidAlgebra.smul_single]

/--
@isnad1 id=isupinde.0h2v.s7.044d7c0c5796 from=translated src=- shape=782d1ae5 vocab=e3d658ed
-/
theorem iSupIndep_weightSpace : iSupIndep (weightSpace k (I := I)) := by
  classical
  intro ν
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 : (gradingHom k I x).coeff ν = x := by
    rw [gradingHom_of_mem hx]; simp [AddMonoidAlgebra.coeff_single]
  have h2 : ∀ y ∈ ⨆ μ, ⨆ (_ : μ ≠ ν), weightSpace k μ, (gradingHom k I y).coeff ν = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem μ y hy =>
      induction hy using Submodule.iSup_induction' with
      | mem hμ y hy =>
        rw [gradingHom_of_mem hy]
        simp [AddMonoidAlgebra.coeff_single, hμ]
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
  rw [← h1, h2 x hx']

/-- The words of a given weight form a finite set.
@isnad1 id=finite.0h2v.s4.719cab43dc96 from=translated src=- shape=9ff6d37e vocab=b619bec8
-/
lemma finite_setOf_wordWeight_eq (ν : I →₀ ℕ) : {w : List I | wordWeight w = ν}.Finite := by
  classical
  have key : ∀ n, {w : List I | w.length = n ∧ ∀ i ∈ w, i ∈ ν.support}.Finite := by
    intro n
    induction n with
    | zero => exact (Set.finite_singleton []).subset fun w hw ↦ List.eq_nil_of_length_eq_zero hw.1
    | succ n ih =>
      refine ((ν.support.finite_toSet.image2 (· :: ·) ih)).subset ?_
      rintro (_ | ⟨i, w⟩) ⟨hl, hw⟩
      · simp at hl
      · exact ⟨i, hw i (by simp), w, ⟨by simpa using hl, fun j hj ↦ hw j (by simp [hj])⟩, rfl⟩
  refine (key (ν.sum fun _ n ↦ n)).subset ?_
  rintro w rfl
  refine ⟨length_eq_sum_wordWeight w, fun i hi ↦ ?_⟩
  · rw [Finsupp.mem_support_iff, wordWeight_apply]
    exact (List.count_pos_iff.2 hi).ne'

/--
@isnad1 id=finitedi.0h3v.s8.179905c1aa92 from=translated src=- shape=af25124e vocab=564bc1ce
-/
instance finiteDimensional_weightSpace (ν : I →₀ ℕ) : FiniteDimensional k (weightSpace k ν) :=
  have := (finite_setOf_wordWeight_eq (I := I) ν).image (monomial k)
  have : Finite (monomial k '' {w | wordWeight w = ν}) := this.to_subtype
  FiniteDimensional.span_of_finite k (Set.toFinite _)

/-! ### Twists and skew derivations -/

/-- The diagonal automorphism `θⱼ ↦ cⱼ θⱼ` of `'f` (an endomorphism for arbitrary `c`).-/
def diagTwist (c : I → k) : LusztigF k I →ₐ[k] LusztigF k I :=
  FreeAlgebra.lift k fun j ↦ c j • θ k j

/--
@isnad1 id=eq.0h4v.s7.393dd2238ad3 from=translated src=- shape=478d6c25 vocab=bbca9c47
-/
@[simp] lemma diagTwist_θ (c : I → k) (j : I) : diagTwist c (θ k j) = c j • θ k j := by
  simp [diagTwist]

/--
@isnad1 id=eq.0h5v.s9.a6fc01f6e3d8 from=translated src=- shape=81c4f033 vocab=e91419ab
-/
lemma diagTwist_diagTwist (c c' : I → k) (x : LusztigF k I) :
    diagTwist c (diagTwist c' x) = diagTwist (c * c') x := by
  have : (diagTwist c).comp (diagTwist c') = diagTwist (k := k) (c * c') := by
    ext l
    simp [smul_smul, mul_comm]
  exact congr($this x)

/--
@isnad1 id=eq.0h5v.s9.ed2cf0ff267d from=translated src=- shape=99f5cb66 vocab=c4355cec
-/
lemma diagTwist_comm (c c' : I → k) (x : LusztigF k I) :
    diagTwist c (diagTwist c' x) = diagTwist c' (diagTwist c x) := by
  rw [diagTwist_diagTwist, diagTwist_diagTwist, mul_comm]

/--
@isnad1 id=eq.0h3v.s7.d69354eafc0a from=translated src=- shape=e3ee28e5 vocab=c4355cec
-/
@[simp] lemma diagTwist_one (x : LusztigF k I) : diagTwist (fun _ ↦ (1 : k)) x = x := by
  have : diagTwist (k := k) (I := I) (fun _ ↦ 1) = AlgHom.id k _ := by ext l; simp
  rw [this, AlgHom.id_apply]

/--
@isnad1 id=eq.0h4v.s8.20329ff422f5 from=translated src=- shape=293f91c9 vocab=71aaa0de
-/
@[simp] lemma counit_diagTwist (c : I → k) (x : LusztigF k I) :
    counit (diagTwist c x) = counit x := by
  have : counit.comp (diagTwist (k := k) (I := I) c) = counit := by ext l; simp
  exact congr($this x)

variable (D : LusztigCartanDatum I) (v : k)

/-- The twist `σᵢ : 'f → 'f`, `θⱼ ↦ v^{i·j} θⱼ`; on `'f_ν` it is multiplication by
`v^{i·ν}`.-/
def twist (i : I) : LusztigF k I →ₐ[k] LusztigF k I :=
  FreeAlgebra.lift k fun j ↦ (v ^ D.dot i j) • θ k j

/--
@isnad1 id=eq.0h6v.s8.0acf95a158bf from=translated src=- shape=c32e1f01 vocab=7a9ced6d
-/
@[simp] lemma twist_θ (i j : I) : twist D v i (θ k j) = v ^ D.dot i j • θ k j := by
  simp [twist]

/--
@isnad1 id=eq.0h7v.s9.7b41563bd5dc from=translated src=- shape=cc6f7576 vocab=a3c1edb1
-/
lemma twist_comm (i j : I) (x : LusztigF k I) :
    twist D v i (twist D v j x) = twist D v j (twist D v i x) := by
  have : (twist D v i).comp (twist D v j) = (twist D v j).comp (twist D v i) := by
    ext l
    simp [smul_smul, mul_comm]
  exact congr($this x)

/--
@isnad1 id=eq.0h6v.s8.9aabca5b097d from=translated src=- shape=8cd50e53 vocab=3a8f0f83
-/
@[simp] lemma counit_twist (i : I) (x : LusztigF k I) : counit (twist D v i x) = counit x := by
  have : counit.comp (twist D v i) = counit := by ext l; simp
  exact congr($this x)

variable {D v} in
/-- On `'f_ν` the twist `σᵢ` is multiplication by `v^{i·ν}`.
@isnad1 id=eq.2h7v.s8.3f48ccb8f587 from=translated src=- shape=89ba9a9d vocab=71d9a411
-/
theorem twist_of_mem (hv : v ≠ 0) (i : I) {ν : I →₀ ℕ} {x : LusztigF k I}
    (hx : x ∈ weightSpace k ν) :
    twist D v i x = v ^ D.weightDot (Finsupp.single i 1) ν • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w with
    | nil => simp
    | cons l w ih =>
      rw [monomial_cons, map_mul, ih, twist_θ, smul_mul_smul_comm, wordWeight_cons,
        D.weightDot_add_right, D.weightDot_single_single, zpow_add₀ hv]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul c y _ hy => rw [map_smul, hy, smul_comm]

variable [DecidableEq I]

/-- The algebra homomorphism `'f → M₂('f)`, `x ↦ [[x, rᵢ(x)], [0, σᵢ(x)]]`, used to construct the
skew derivation `rᵢ`.-/
def rMat (i : I) : LusztigF k I →ₐ[k] Matrix (Fin 2) (Fin 2) (LusztigF k I) :=
  FreeAlgebra.lift k fun j ↦ !![θ k j, if i = j then 1 else 0; 0, v ^ D.dot i j • θ k j]

/-- The algebra homomorphism `'f → M₂('f)`, `x ↦ [[σᵢ(x), ᵢr(x)], [0, x]]`, used to construct the
skew derivation `ᵢr`.-/
def lMat (i : I) : LusztigF k I →ₐ[k] Matrix (Fin 2) (Fin 2) (LusztigF k I) :=
  FreeAlgebra.lift k fun j ↦ !![v ^ D.dot i j • θ k j, if i = j then 1 else 0; 0, θ k j]

/-- The linear map extracting the `(0, 1)` entry of a `2 × 2` matrix.-/
def entry01 : Matrix (Fin 2) (Fin 2) (LusztigF k I) →ₗ[k] LusztigF k I where
  toFun M := M 0 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Lusztig's skew derivation `rᵢ : 'f → 'f` ([Lus] 1.2.13): `rᵢ(θⱼ) = δᵢⱼ` and
`rᵢ(xy) = x rᵢ(y) + v^{|y|·i} rᵢ(x) y` (`rDeriv_mul`).-/
def rDeriv (i : I) : LusztigF k I →ₗ[k] LusztigF k I :=
  entry01 ∘ₗ (rMat D v i).toLinearMap

/-- Lusztig's skew derivation `ᵢr : 'f → 'f` ([Lus] 1.2.13): `ᵢr(θⱼ) = δᵢⱼ` and
`ᵢr(xy) = ᵢr(x) y + v^{|x|·i} x ᵢr(y)` (`lDeriv_mul`).-/
def lDeriv (i : I) : LusztigF k I →ₗ[k] LusztigF k I :=
  entry01 ∘ₗ (lMat D v i).toLinearMap

/--
@isnad1 id=and.0h6v.s10.6e361cb6af93 from=translated src=- shape=aff84115 vocab=04703f26
-/
lemma rMat_entries (i : I) (x : LusztigF k I) :
    rMat D v i x 0 0 = x ∧ rMat D v i x 1 0 = 0 ∧ rMat D v i x 1 1 = twist D v i x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Matrix.algebraMap_matrix_apply]
  | grade1 j => simp [rMat]
  | mul a b ha hb =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1,
      hb.2.2]
    simp
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

/--
@isnad1 id=and.0h6v.s10.53ca6bd94e7b from=translated src=- shape=4e924761 vocab=b6bef610
-/
lemma lMat_entries (i : I) (x : LusztigF k I) :
    lMat D v i x 0 0 = twist D v i x ∧ lMat D v i x 1 0 = 0 ∧ lMat D v i x 1 1 = x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Matrix.algebraMap_matrix_apply]
  | grade1 j => simp [lMat]
  | mul a b ha hb =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1,
      hb.2.2]
    simp
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

/--
@isnad1 id=eq.0h6v.s9.b764b1e0b10a from=translated src=- shape=18a42b44 vocab=283ad7a8
-/
lemma rDeriv_apply (i : I) (x : LusztigF k I) : rDeriv D v i x = rMat D v i x 0 1 := rfl

/--
@isnad1 id=eq.0h6v.s9.33c48e87f663 from=translated src=- shape=18a42b44 vocab=d7eeb3ae
-/
lemma lDeriv_apply (i : I) (x : LusztigF k I) : lDeriv D v i x = lMat D v i x 0 1 := rfl

/-- `rᵢ(xy) = x rᵢ(y) + rᵢ(x) σᵢ(y)`.
@isnad1 id=eq.0h7v.s10.a00a729b343f from=translated src=- shape=b4851dd3 vocab=ad33b07b
-/
theorem rDeriv_mul (i : I) (x y : LusztigF k I) :
    rDeriv D v i (x * y) = x * rDeriv D v i y + rDeriv D v i x * twist D v i y := by
  simp only [rDeriv_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (rMat_entries D v i x).1,
    (rMat_entries D v i y).2.2]

/-- `ᵢr(xy) = ᵢr(x) y + σᵢ(x) ᵢr(y)`.
@isnad1 id=eq.0h7v.s10.c0b9371433b4 from=translated src=- shape=4af8de93 vocab=99900c8c
-/
theorem lDeriv_mul (i : I) (x y : LusztigF k I) :
    lDeriv D v i (x * y) = lDeriv D v i x * y + twist D v i x * lDeriv D v i y := by
  simp only [lDeriv_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (lMat_entries D v i x).1,
    (lMat_entries D v i y).2.2]
  rw [add_comm]

/--
@isnad1 id=eq.0h6v.s8.9841373c4122 from=translated src=- shape=7a374f41 vocab=ccea2435
-/
@[simp] lemma rDeriv_θ (i j : I) : rDeriv D v i (θ k j) = if i = j then 1 else 0 := by
  simp [rDeriv_apply, rMat]

/--
@isnad1 id=eq.0h6v.s8.9cffa66cec67 from=translated src=- shape=7a374f41 vocab=80e4654c
-/
@[simp] lemma lDeriv_θ (i j : I) : lDeriv D v i (θ k j) = if i = j then 1 else 0 := by
  simp [lDeriv_apply, lMat]

/--
@isnad1 id=eq.0h6v.s8.8466245330d8 from=translated src=- shape=08739ef4 vocab=0c11f577
-/
@[simp] lemma rDeriv_algebraMap (i : I) (c : k) : rDeriv D v i (algebraMap k _ c) = 0 := by
  simp [rDeriv_apply, Matrix.algebraMap_matrix_apply]

/--
@isnad1 id=eq.0h6v.s8.a008caa053ef from=translated src=- shape=08739ef4 vocab=0ab7c152
-/
@[simp] lemma lDeriv_algebraMap (i : I) (c : k) : lDeriv D v i (algebraMap k _ c) = 0 := by
  simp [lDeriv_apply, Matrix.algebraMap_matrix_apply]

/--
@isnad1 id=eq.0h5v.s8.0562928257bc from=translated src=- shape=a2d7c5a1 vocab=ac7c3aa6
-/
@[simp] lemma rDeriv_one (i : I) : rDeriv D v i 1 = 0 := by
  simpa using rDeriv_algebraMap D v i (1 : k)

/--
@isnad1 id=eq.0h5v.s8.8989a15f84f3 from=translated src=- shape=a2d7c5a1 vocab=0b62bf4d
-/
@[simp] lemma lDeriv_one (i : I) : lDeriv D v i 1 = 0 := by
  simpa using lDeriv_algebraMap D v i (1 : k)

/--
@isnad1 id=eq.0h7v.s9.292ee5397840 from=translated src=- shape=9b0e43b1 vocab=ad6367be
-/
lemma rDeriv_θ_mul (i j : I) (x : LusztigF k I) :
    rDeriv D v i (θ k j * x) = θ k j * rDeriv D v i x + if i = j then twist D v i x else 0 := by
  rw [rDeriv_mul, rDeriv_θ]; split_ifs <;> simp

/--
@isnad1 id=eq.0h7v.s9.6e500c17695d from=translated src=- shape=24dc13c8 vocab=02fadd11
-/
lemma rDeriv_mul_θ (i j : I) (x : LusztigF k I) :
    rDeriv D v i (x * θ k j) =
      (if i = j then x else 0) + v ^ D.dot i j • (rDeriv D v i x * θ k j) := by
  rw [rDeriv_mul, rDeriv_θ, twist_θ, mul_smul_comm]; split_ifs <;> simp

/--
@isnad1 id=eq.0h7v.s9.3ae694ee4d5f from=translated src=- shape=10e38f94 vocab=36de9a89
-/
lemma lDeriv_θ_mul (i j : I) (x : LusztigF k I) :
    lDeriv D v i (θ k j * x) =
      (if i = j then x else 0) + v ^ D.dot i j • (θ k j * lDeriv D v i x) := by
  rw [lDeriv_mul, lDeriv_θ, twist_θ, smul_mul_assoc]; split_ifs <;> simp

/-- `rᵢ ∘ σⱼ = v^{i·j} σⱼ ∘ rᵢ`.
@isnad1 id=eq.0h7v.s9.dafc36603d41 from=translated src=- shape=81b1d569 vocab=1dd45729
-/
lemma rDeriv_twist (i j : I) (x : LusztigF k I) :
    rDeriv D v i (twist D v j x) = v ^ D.dot i j • twist D v j (rDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    simp only [twist_θ, map_smul, rDeriv_θ]
    split_ifs with h <;> simp [h, D.dot_comm]
  | mul a b ha hb =>
    rw [map_mul, rDeriv_mul, rDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist_comm D v i j]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

/-- `ᵢr ∘ σⱼ = v^{i·j} σⱼ ∘ ᵢr`.
@isnad1 id=eq.0h7v.s9.687bd7458eb5 from=translated src=- shape=81b1d569 vocab=35569656
-/
lemma lDeriv_twist (i j : I) (x : LusztigF k I) :
    lDeriv D v i (twist D v j x) = v ^ D.dot i j • twist D v j (lDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    simp only [twist_θ, map_smul, lDeriv_θ]
    split_ifs with h <;> simp [h, D.dot_comm]
  | mul a b ha hb =>
    rw [map_mul, lDeriv_mul, lDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist_comm D v i j]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

omit [DecidableEq I] in
/--
@isnad1 id=eq.0h5v.s6.649e55662fcb from=translated src=- shape=1b48041e vocab=5c8d7e2d
-/
lemma twist_eq_diagTwist (i : I) : twist D v i = diagTwist fun j ↦ v ^ D.dot i j := rfl

/-- `rᵢ ∘ φ = cᵢ φ ∘ rᵢ` for the diagonal twist `φ : θⱼ ↦ cⱼ θⱼ`.
@isnad1 id=eq.0h7v.s9.f76d3f76e6b1 from=translated src=- shape=14868607 vocab=f44d8e9f
-/
lemma rDeriv_diagTwist (c : I → k) (i : I) (x : LusztigF k I) :
    rDeriv D v i (diagTwist c x) = c i • diagTwist c (rDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 a => simp
  | grade1 l =>
    simp only [diagTwist_θ, map_smul, rDeriv_θ]
    split_ifs with h <;> simp [h]
  | mul a b ha hb =>
    rw [map_mul, rDeriv_mul, rDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist_eq_diagTwist,
      diagTwist_comm c]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

/-- `ᵢr ∘ φ = cᵢ φ ∘ ᵢr` for the diagonal twist `φ : θⱼ ↦ cⱼ θⱼ`.
@isnad1 id=eq.0h7v.s9.540d98d09637 from=translated src=- shape=14868607 vocab=d0a5e793
-/
lemma lDeriv_diagTwist (c : I → k) (i : I) (x : LusztigF k I) :
    lDeriv D v i (diagTwist c x) = c i • diagTwist c (lDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 a => simp
  | grade1 l =>
    simp only [diagTwist_θ, map_smul, lDeriv_θ]
    split_ifs with h <;> simp [h]
  | mul a b ha hb =>
    rw [map_mul, lDeriv_mul, lDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist_eq_diagTwist,
      diagTwist_comm c]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

/--
@isnad1 id=eq.0h7v.s9.e14c4dfdf221 from=translated src=- shape=24eab10b vocab=e0fa59dd
-/
lemma counit_rDeriv_θ_mul (i j : I) (x : LusztigF k I) :
    counit (rDeriv D v i (θ k j * x)) = if i = j then counit x else 0 := by
  rw [rDeriv_θ_mul]; split_ifs <;> simp

end Tengoku.LieLean.LusztigF
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
