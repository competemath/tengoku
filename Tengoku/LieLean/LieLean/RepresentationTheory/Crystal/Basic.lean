/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.LinearAlgebra.Matrix.Cartan.Generalized
import Tengoku.Seed.Algebra.Order.Monoid.WithTop
import Tengoku.Seed.Algebra.Order.Ring.WithTop
import Tengoku.Seed.LinearAlgebra.Reflection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract crystals

We define Kashiwara's abstract crystals ([Kas] §7.2, [HK] Def. 4.5.1) over a
Cartan datum, their morphisms, and the basic examples.

## Main definitions

* `CartanDatum ι X`: a weight lattice `X` (an additive commutative group) together with simple
  roots `αᵢ ∈ X` and simple coroots `⟨·, αᵢ^∨⟩ : X → ℤ` with `⟨αᵢ, αᵢ^∨⟩ = 2`.
* `CartanDatum.cartanMatrix`: the matrix `aᵢⱼ = ⟨αⱼ, αᵢ^∨⟩`.
* `CartanDatum.reflection`: the simple reflection `rᵢ μ = μ - ⟨μ, αᵢ^∨⟩ αᵢ` of `X`.
* `Crystal D B`: a crystal structure on a type `B` over the Cartan datum `D`: maps
  `wt : B → X`, `εᵢ, φᵢ : B → ℤ ⊔ {-∞}` and Kashiwara operators `ẽᵢ, f̃ᵢ : B → B ⊔ {0}`.
* `Crystal.eIter`, `Crystal.fIter`: the iterates `ẽᵢⁿ`, `f̃ᵢⁿ`.
* `Crystal.fWord C l b`: `f̃_{i₁} ⋯ f̃_{iₖ} b` for a word `l = [i₁, …, iₖ]`.
* `Crystal.Hom`, `Crystal.StrictHom`, `Crystal.Equiv`: morphisms, strict morphisms and
  isomorphisms of crystals.
* `Crystal.T D λ`: the crystal `T_λ = {t_λ}`; `Crystal.trivial D`: the crystal `C = {c}`;
  `Crystal.elementary D i`: the elementary crystal `Bᵢ = {bᵢ(n) | n ∈ ℤ}`.

## Main results

* `Crystal.wt_f`, `Crystal.ε_f`, `Crystal.φ_e`, `Crystal.φ_f`, `Crystal.f_eq_none_of_φ_eq_bot`:
  the axioms of [HK] Def. 4.5.1 that are not fields of `Crystal` (they follow from the
  others).
* `Crystal.fIter_eq_some_iff`: `f̃ᵢⁿ b = b' ↔ ẽᵢⁿ b' = b`.

## Conventions

The value `0` of `ẽᵢ` and `f̃ᵢ` is modelled by `none : Option B`, and `-∞` by `⊥ : WithBot ℤ`.
Since `WithBot ℤ` has no subtraction, the axiom `εᵢ(ẽᵢ b) = εᵢ(b) - 1` is stated in the equivalent
form `εᵢ(b) = εᵢ(ẽᵢ b) + 1`.

We do not reuse Mathlib's `RootPairing`: a root pairing requires a perfect pairing between the
weight and coweight lattices and a reflection-stable family of roots, while crystals only need the
simple roots `αᵢ` and the linear forms `⟨·, αᵢ^∨⟩` on an arbitrary weight lattice (for a
Kac–Moody algebra the simple roots are not stable under the reflections).

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, Ch. 4.
* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413.
-/
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean
/-- A Cartan datum: a weight lattice `X` (any additive commutative group) with simple roots
`αᵢ ∈ X` and simple coroots given as linear forms `⟨·, αᵢ^∨⟩ : X → ℤ`, such that
`⟨αᵢ, αᵢ^∨⟩ = 2`. This is the part of a Cartan datum `(A, Π, Π^∨, P, P^∨)` of [HK] Def. 2.1.1
used by the theory of abstract crystals; the associated matrix `CartanDatum.cartanMatrix` is
`aᵢⱼ = ⟨αⱼ, αᵢ^∨⟩`, the convention of `Matrix.Realization`.-/
structure _root_.Tengoku.LieLean.CartanDatum (ι X : Type*) [AddCommGroup X] where
  /-- The simple roots `αᵢ`.-/
  root : ι → X
  /-- The simple coroots `αᵢ^∨`, as linear forms `μ ↦ ⟨μ, αᵢ^∨⟩` on the weight lattice.-/
  coroot : ι → Module.Dual ℤ X
  coroot_root_self : ∀ i, coroot i (root i) = 2

namespace Tengoku.LieLean.CartanDatum

variable {ι X : Type*} [AddCommGroup X] (D : CartanDatum ι X)

/-- The Cartan matrix `aᵢⱼ = ⟨αⱼ, αᵢ^∨⟩` of a Cartan datum.-/
def cartanMatrix : Matrix ι ι ℤ := Matrix.of fun i j ↦ D.coroot i (D.root j)

/--
@isnad1 id=eq.0h5v.s6.8011e94cd0de from=translated src=- shape=bddd0de0 vocab=ff04d733
-/
@[simp] lemma cartanMatrix_apply (i j : ι) : D.cartanMatrix i j = D.coroot i (D.root j) := rfl

/--
@isnad1 id=eq.0h4v.s4.f67ac00742d7 from=translated src=- shape=e04f9ca4 vocab=260cec93
-/
lemma cartanMatrix_self (i : ι) : D.cartanMatrix i i = 2 := D.coroot_root_self i

/-- The simple reflection `rᵢ μ = μ - ⟨μ, αᵢ^∨⟩ αᵢ` of the weight lattice.-/
def reflection (i : ι) : X ≃ₗ[ℤ] X := Module.reflection (D.coroot_root_self i)

/--
@isnad1 id=eq.0h5v.s7.636bc9261735 from=translated src=- shape=2f07dd17 vocab=6a369004
-/
lemma reflection_apply (i : ι) (μ : X) :
    D.reflection i μ = μ - D.coroot i μ • D.root i := rfl

/--
@isnad1 id=eq.0h5v.s7.d8c49b4bd0f3 from=translated src=- shape=792775c9 vocab=9a609b21
-/
@[simp] lemma reflection_reflection (i : ι) (μ : X) : D.reflection i (D.reflection i μ) = μ :=
  Module.involutive_reflection (D.coroot_root_self i) μ

/--
@isnad1 id=eq.0h5v.s7.8f6df83ec013 from=translated src=- shape=18a76a1b vocab=7bb9cec2
-/
@[simp] lemma coroot_reflection (i : ι) (μ : X) :
    D.coroot i (D.reflection i μ) = -D.coroot i μ := by
  simp only [reflection_apply, map_sub, map_zsmul, coroot_root_self, smul_eq_mul]
  ring

end Tengoku.LieLean.CartanDatum

/-- An abstract crystal ([Kas] §7.2, [HK] Def. 4.5.1) over the Cartan datum `D`,
on the type `B`: a weight map `wt : B → X`, maps `εᵢ, φᵢ : B → ℤ ⊔ {-∞}` and the Kashiwara
operators `ẽᵢ, f̃ᵢ : B → B ⊔ {0}` (with `0` modelled by `none`), such that

* `φᵢ(b) = εᵢ(b) + ⟨wt b, αᵢ^∨⟩`;
* `f̃ᵢ b = b'` if and only if `b = ẽᵢ b'`;
* if `ẽᵢ b ∈ B` then `wt(ẽᵢ b) = wt b + αᵢ` and `εᵢ(ẽᵢ b) = εᵢ(b) - 1`;
* if `φᵢ(b) = -∞` then `ẽᵢ b = 0`.

The remaining axioms of [HK] Def. 4.5.1 (the behaviour of `wt`, `ε`, `φ` under `f̃ᵢ`, of `φ` under
`ẽᵢ`, and `f̃ᵢ b = 0` if `φᵢ(b) = -∞`) follow from these: see `Crystal.wt_f`, `Crystal.ε_f`,
`Crystal.φ_e`, `Crystal.φ_f`, `Crystal.f_eq_none_of_φ_eq_bot`.-/
structure _root_.Tengoku.LieLean.Crystal {ι X : Type*} [AddCommGroup X] (D : CartanDatum ι X) (B : Type*) where
  /-- The weight map.-/
  wt : B → X
  /-- `εᵢ(b)`, in `ℤ ⊔ {-∞}`.-/
  ε : ι → B → WithBot ℤ
  /-- `φᵢ(b)`, in `ℤ ⊔ {-∞}`.-/
  φ : ι → B → WithBot ℤ
  /-- The raising Kashiwara operator `ẽᵢ`; `none` stands for `0`.-/
  e : ι → B → Option B
  /-- The lowering Kashiwara operator `f̃ᵢ`; `none` stands for `0`.-/
  f : ι → B → Option B
  φ_eq : ∀ i b, φ i b = ε i b + (D.coroot i (wt b) : ℤ)
  f_eq_some_iff : ∀ i b b', f i b = some b' ↔ e i b' = some b
  wt_e : ∀ i b b', e i b = some b' → wt b' = wt b + D.root i
  ε_e : ∀ i b b', e i b = some b' → ε i b = ε i b' + 1
  e_eq_none_of_φ_eq_bot : ∀ i b, φ i b = ⊥ → e i b = none

namespace Tengoku.LieLean.Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B₁ B₂ B₃ : Type*}
  (C : Crystal D B) {i : ι} {b b' : B}

/-! ### Consequences of the axioms -/

/--
@isnad1 id=iff.0h7v.s5.0005eeefaf7f from=translated src=- shape=2c40e4a1 vocab=4b11e8c6
-/
lemma φ_eq_bot_iff : C.φ i b = ⊥ ↔ C.ε i b = ⊥ := by
  rw [C.φ_eq]
  induction C.ε i b using WithBot.recBotCoe <;> simp [← WithBot.coe_add]

/--
@isnad1 id=eq.1h7v.s5.3a9573619dd6 from=translated src=- shape=ab43c55e vocab=22a0cd90
-/
lemma e_eq_none_of_ε_eq_bot (h : C.ε i b = ⊥) : C.e i b = none :=
  C.e_eq_none_of_φ_eq_bot i b ((C.φ_eq_bot_iff).mpr h)

/--
@isnad1 id=ne.1h8v.s5.b1c769d69a85 from=translated src=- shape=c6f5a737 vocab=8421f133
-/
lemma ε_ne_bot_of_e_eq_some (h : C.e i b = some b') : C.ε i b ≠ ⊥ := fun h' ↦ by
  simp [C.e_eq_none_of_ε_eq_bot h'] at h

/--
@isnad1 id=ne.1h8v.s5.9d433b1f247e from=translated src=- shape=c6f5a737 vocab=a4ec2dde
-/
lemma φ_ne_bot_of_e_eq_some (h : C.e i b = some b') : C.φ i b ≠ ⊥ := by
  rw [Ne, C.φ_eq_bot_iff]; exact C.ε_ne_bot_of_e_eq_some h

/--
@isnad1 id=iff.0h8v.s5.3eb70a483f22 from=translated src=- shape=afa2404d vocab=9765e720
-/
lemma e_eq_some_iff : C.e i b = some b' ↔ C.f i b' = some b := (C.f_eq_some_iff i b' b).symm

/-- `wt(f̃ᵢ b) = wt b - αᵢ`.
@isnad1 id=eq.1h8v.s6.b131719b9e3c from=translated src=- shape=bec2c868 vocab=9688ca41
-/
lemma wt_f (h : C.f i b = some b') : C.wt b' = C.wt b - D.root i := by
  rw [C.wt_e i b' b ((C.f_eq_some_iff i b b').mp h), add_sub_cancel_right]

/-- `εᵢ(f̃ᵢ b) = εᵢ(b) + 1`.
@isnad1 id=eq.1h8v.s6.d4c9b4d7b37d from=translated src=- shape=0dca2634 vocab=39bd39fe
-/
lemma ε_f (h : C.f i b = some b') : C.ε i b' = C.ε i b + 1 :=
  C.ε_e i b' b ((C.f_eq_some_iff i b b').mp h)

/-- `φᵢ(ẽᵢ b) = φᵢ(b) + 1`.
@isnad1 id=eq.1h8v.s6.c817a1a6ffd9 from=translated src=- shape=0dca2634 vocab=568947e7
-/
lemma φ_e (h : C.e i b = some b') : C.φ i b' = C.φ i b + 1 := by
  rw [C.φ_eq, C.φ_eq, C.wt_e i b b' h, C.ε_e i b b' h, map_add, D.coroot_root_self]
  push_cast
  rw [← one_add_one_eq_two]
  abel

/-- `φᵢ(b) = φᵢ(f̃ᵢ b) + 1`.
@isnad1 id=eq.1h8v.s6.00b242030437 from=translated src=- shape=d4f99ca5 vocab=ecfbc200
-/
lemma φ_f (h : C.f i b = some b') : C.φ i b = C.φ i b' + 1 :=
  C.φ_e ((C.f_eq_some_iff i b b').mp h)

/--
@isnad1 id=ne.1h8v.s5.342734bc3d2b from=translated src=- shape=c6f5a737 vocab=f7004726
-/
lemma ε_ne_bot_of_f_eq_some (h : C.f i b = some b') : C.ε i b ≠ ⊥ := by
  have h' := C.ε_ne_bot_of_e_eq_some ((C.f_eq_some_iff i b b').mp h)
  rw [C.ε_f h] at h'
  rintro h''
  simp [h''] at h'

/--
@isnad1 id=ne.1h8v.s5.bc5a709d7094 from=translated src=- shape=c6f5a737 vocab=6dfdbe42
-/
lemma φ_ne_bot_of_f_eq_some (h : C.f i b = some b') : C.φ i b ≠ ⊥ := by
  rw [Ne, C.φ_eq_bot_iff]; exact C.ε_ne_bot_of_f_eq_some h

/-- If `φᵢ(b) = -∞` then `f̃ᵢ b = 0`.
@isnad1 id=eq.1h7v.s5.2c38b4cf8b3b from=translated src=- shape=ab43c55e vocab=fd35e1f4
-/
lemma f_eq_none_of_φ_eq_bot (h : C.φ i b = ⊥) : C.f i b = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  intro b' h'
  exact C.φ_ne_bot_of_f_eq_some h' h

/--
@isnad1 id=eq.1h7v.s5.a14865c3ff6e from=translated src=- shape=ab43c55e vocab=25b90905
-/
lemma f_eq_none_of_ε_eq_bot (h : C.ε i b = ⊥) : C.f i b = none :=
  C.f_eq_none_of_φ_eq_bot ((C.φ_eq_bot_iff).mpr h)

/--
@isnad1 id=eq.2h9v.s6.670fa889db01 from=translated src=- shape=87f55651 vocab=88883151
-/
lemma e_injective {b₁ b₂ : B} (h₁ : C.e i b₁ = some b) (h₂ : C.e i b₂ = some b) : b₁ = b₂ := by
  rw [C.e_eq_some_iff] at h₁ h₂
  exact Option.some_injective _ (h₁.symm.trans h₂)

/--
@isnad1 id=eq.2h9v.s6.79d0fb1fcfb1 from=translated src=- shape=87f55651 vocab=3546e727
-/
lemma f_injective {b₁ b₂ : B} (h₁ : C.f i b₁ = some b) (h₂ : C.f i b₂ = some b) : b₁ = b₂ := by
  rw [C.f_eq_some_iff] at h₁ h₂
  exact Option.some_injective _ (h₁.symm.trans h₂)

/--
@isnad1 id=eq.0h7v.s5.c01513e4210a from=translated src=- shape=c6b68aa6 vocab=a71df11b
-/
lemma e_bind_f (b : B) : (C.e i b).bind (C.f i) = (C.e i b).map fun _ ↦ b := by
  cases h : C.e i b with
  | none => rfl
  | some b' => simpa using (C.f_eq_some_iff i b' b).mpr h

/--
@isnad1 id=eq.0h7v.s5.995c162c22b1 from=translated src=- shape=c6b68aa6 vocab=a71df11b
-/
lemma f_bind_e (b : B) : (C.f i b).bind (C.e i) = (C.f i b).map fun _ ↦ b := by
  cases h : C.f i b with
  | none => rfl
  | some b' => simpa using (C.f_eq_some_iff i b b').mp h

/-! ### Iterated Kashiwara operators -/

/-- The iterate `ẽᵢⁿ` of the Kashiwara operator `ẽᵢ`.-/
def eIter (i : ι) : ℕ → B → Option B
  | 0, b => some b
  | n + 1, b => (C.e i b).bind (eIter i n)

/-- The iterate `f̃ᵢⁿ` of the Kashiwara operator `f̃ᵢ`.-/
def fIter (i : ι) : ℕ → B → Option B
  | 0, b => some b
  | n + 1, b => (C.f i b).bind (fIter i n)

/--
@isnad1 id=eq.0h7v.s5.07d093a7f843 from=translated src=- shape=f4429cd7 vocab=f8e43de9
-/
@[simp] lemma eIter_zero (b : B) : C.eIter i 0 b = some b := rfl

/--
@isnad1 id=eq.0h7v.s5.ca197ac4e1d7 from=translated src=- shape=f4429cd7 vocab=6e247ef1
-/
@[simp] lemma fIter_zero (b : B) : C.fIter i 0 b = some b := rfl

/--
@isnad1 id=eq.0h8v.s6.70721ccbdb76 from=translated src=- shape=cd6f1b65 vocab=acab2cbf
-/
lemma eIter_succ (n : ℕ) (b : B) : C.eIter i (n + 1) b = (C.e i b).bind (C.eIter i n) := rfl

/--
@isnad1 id=eq.0h8v.s6.06c1d3e51208 from=translated src=- shape=cd6f1b65 vocab=fa6e005c
-/
lemma fIter_succ (n : ℕ) (b : B) : C.fIter i (n + 1) b = (C.f i b).bind (C.fIter i n) := rfl

/--
@isnad1 id=eq.0h7v.s5.f9e795d2cf30 from=translated src=- shape=8ea17f35 vocab=ab5769c4
-/
@[simp] lemma eIter_one (b : B) : C.eIter i 1 b = C.e i b := by
  rw [eIter_succ]; cases C.e i b <;> rfl

/--
@isnad1 id=eq.0h7v.s5.7828a6cd522c from=translated src=- shape=8ea17f35 vocab=9a870b37
-/
@[simp] lemma fIter_one (b : B) : C.fIter i 1 b = C.f i b := by
  rw [fIter_succ]; cases C.f i b <;> rfl

/--
@isnad1 id=eq.0h8v.s6.dd4e47759e01 from=translated src=- shape=b6197bba vocab=acab2cbf
-/
lemma eIter_succ' (n : ℕ) (b : B) : C.eIter i (n + 1) b = (C.eIter i n b).bind (C.e i) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [eIter_succ, eIter_succ]
    cases C.e i b with
    | none => rfl
    | some b' => exact ih b'

/--
@isnad1 id=eq.0h8v.s6.03765d90c934 from=translated src=- shape=b6197bba vocab=fa6e005c
-/
lemma fIter_succ' (n : ℕ) (b : B) : C.fIter i (n + 1) b = (C.fIter i n b).bind (C.f i) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [fIter_succ, fIter_succ]
    cases C.f i b with
    | none => rfl
    | some b' => exact ih b'

/-- `f̃ᵢⁿ b = b'` if and only if `ẽᵢⁿ b' = b`.
@isnad1 id=iff.0h9v.s5.474119782e67 from=translated src=- shape=200b5f19 vocab=e218d481
-/
theorem fIter_eq_some_iff (n : ℕ) (b b' : B) :
    C.fIter i n b = some b' ↔ C.eIter i n b' = some b := by
  induction n generalizing b b' with
  | zero => simp [eq_comm]
  | succ n ih =>
    rw [fIter_succ, eIter_succ', Option.bind_eq_some_iff, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨c, hc, hcb'⟩
      exact ⟨c, (ih c b').mp hcb', (C.f_eq_some_iff i b c).mp hc⟩
    · rintro ⟨c, hc, hcb⟩
      exact ⟨c, (C.f_eq_some_iff i b c).mpr hcb, (ih c b').mpr hc⟩

/--
@isnad1 id=eq.1h9v.s6.4414a0520b12 from=translated src=- shape=2a8b028b vocab=6453abee
-/
lemma wt_eIter {n : ℕ} (h : C.eIter i n b = some b') : C.wt b' = C.wt b + n • D.root i := by
  induction n generalizing b with
  | zero => simp_all
  | succ n ih =>
    obtain ⟨c, hc, hcb'⟩ := Option.bind_eq_some_iff.mp h
    rw [ih hcb', C.wt_e i b c hc, succ_nsmul']
    abel

/--
@isnad1 id=eq.1h9v.s6.ccf46dd42dc2 from=translated src=- shape=2a8b028b vocab=c8dc6b8f
-/
lemma wt_fIter {n : ℕ} (h : C.fIter i n b = some b') : C.wt b' = C.wt b - n • D.root i := by
  rw [C.wt_eIter ((C.fIter_eq_some_iff n b b').mp h), add_sub_cancel_right]

/--
@isnad1 id=eq.1h9v.s6.327149102aeb from=translated src=- shape=b0c8a354 vocab=a18cafeb
-/
lemma ε_eIter {n : ℕ} (h : C.eIter i n b = some b') : C.ε i b = C.ε i b' + n := by
  induction n generalizing b with
  | zero => simp_all
  | succ n ih =>
    obtain ⟨c, hc, hcb'⟩ := Option.bind_eq_some_iff.mp h
    rw [C.ε_e i b c hc, ih hcb']
    push_cast
    abel

/--
@isnad1 id=eq.1h9v.s6.bd1be0ec6a8f from=translated src=- shape=6c670993 vocab=4f39cc5e
-/
lemma φ_eIter {n : ℕ} (h : C.eIter i n b = some b') : C.φ i b' = C.φ i b + n := by
  induction n generalizing b with
  | zero => simp_all
  | succ n ih =>
    obtain ⟨c, hc, hcb'⟩ := Option.bind_eq_some_iff.mp h
    rw [ih hcb', C.φ_e hc]
    push_cast
    abel

/--
@isnad1 id=eq.1h9v.s6.1f357a43f986 from=translated src=- shape=6c670993 vocab=0df83671
-/
lemma ε_fIter {n : ℕ} (h : C.fIter i n b = some b') : C.ε i b' = C.ε i b + n :=
  C.ε_eIter ((C.fIter_eq_some_iff n b b').mp h)

/--
@isnad1 id=eq.1h9v.s6.ea7875808b93 from=translated src=- shape=b0c8a354 vocab=4992ecbf
-/
lemma φ_fIter {n : ℕ} (h : C.fIter i n b = some b') : C.φ i b = C.φ i b' + n :=
  C.φ_eIter ((C.fIter_eq_some_iff n b b').mp h)

/-- `fWord [i₁, …, iₖ] b = f̃_{i₁} ⋯ f̃_{iₖ} b` (`none` if some step gives `0`).-/
def fWord : List ι → B → Option B
  | [], b => some b
  | j :: l, b => (fWord l b).bind (C.f j)

/--
@isnad1 id=eq.0h6v.s5.c74a4ed2962c from=translated src=- shape=2cf0df1f vocab=65b1176e
-/
@[simp] lemma fWord_nil (b : B) : C.fWord [] b = some b := rfl

/--
@isnad1 id=eq.0h8v.s5.c4cff6a90e64 from=translated src=- shape=c8b9a4da vocab=80728fe3
-/
lemma fWord_cons (j : ι) (l : List ι) (b : B) :
    C.fWord (j :: l) b = (C.fWord l b).bind (C.f j) := rfl

/-! ### Morphisms -/

variable (C₁ : Crystal D B₁) (C₂ : Crystal D B₂) (C₃ : Crystal D B₃)

/-- A morphism of crystals ([Kas] §7.2, [HK] Def. 4.5.5): a map `ψ : B₁ → B₂ ⊔ {0}` (with `0`
modelled by `none`) such that for `b ∈ B₁` with `ψ(b) ∈ B₂`, `wt`, `εᵢ` and `φᵢ` are preserved, and
such that if `b, ẽᵢ b ∈ B₁` both have nonzero image then `ψ(ẽᵢ b) = ẽᵢ ψ(b)`, and likewise for
`f̃ᵢ`. Morphisms in this sense are not closed under composition in general; see `Crystal.StrictHom`
for the better behaved strict morphisms.-/
structure Hom where
  /-- The underlying map `B₁ → B₂ ⊔ {0}`.-/
  toFun : B₁ → Option B₂
  wt_map : ∀ b c, toFun b = some c → C₂.wt c = C₁.wt b
  ε_map : ∀ i b c, toFun b = some c → C₂.ε i c = C₁.ε i b
  φ_map : ∀ i b c, toFun b = some c → C₂.φ i c = C₁.φ i b
  e_map : ∀ i b b' c c', C₁.e i b = some b' → toFun b = some c → toFun b' = some c' →
    C₂.e i c = some c'
  f_map : ∀ i b b' c c', C₁.f i b = some b' → toFun b = some c → toFun b' = some c' →
    C₂.f i c = some c'

/-- A strict morphism of crystals never taking the value `0` ([Kas] §7.6, [HK]
Def. 4.5.6 (1)): a map `ψ : B₁ → B₂` preserving `wt` and the `εᵢ` and commuting with all the
`ẽᵢ` and `f̃ᵢ` (the `φᵢ` are then preserved as well, `Crystal.StrictHom.φ_map`).-/
structure StrictHom where
  /-- The underlying map `B₁ → B₂`.-/
  toFun : B₁ → B₂
  wt_map : ∀ b, C₂.wt (toFun b) = C₁.wt b
  ε_map : ∀ i b, C₂.ε i (toFun b) = C₁.ε i b
  e_map : ∀ i b, C₂.e i (toFun b) = (C₁.e i b).map toFun
  f_map : ∀ i b, C₂.f i (toFun b) = (C₁.f i b).map toFun

/-- An isomorphism of crystals: a bijection `B₁ ≃ B₂` which is a strict morphism.-/
structure Equiv extends B₁ ≃ B₂ where
  wt_map : ∀ b, C₂.wt (toFun b) = C₁.wt b
  ε_map : ∀ i b, C₂.ε i (toFun b) = C₁.ε i b
  e_map : ∀ i b, C₂.e i (toFun b) = (C₁.e i b).map toFun
  f_map : ∀ i b, C₂.f i (toFun b) = (C₁.f i b).map toFun

namespace StrictHom

variable {C₁ C₂ C₃}

instance : FunLike (StrictHom C₁ C₂) B₁ B₂ where
  coe ψ := ψ.toFun
  coe_injective ψ ψ' h := by cases ψ; cases ψ'; congr

/--
@isnad1 id=eq.0h8v.s6.4d42bc963dc9 from=translated src=- shape=7fbda0c5 vocab=4277ca70
-/
@[simp] lemma toFun_eq_coe (ψ : StrictHom C₁ C₂) : ψ.toFun = ψ := rfl

/--
@isnad1 id=eq.1h9v.s6.d10389964904 from=translated src=- shape=6b22a1c4 vocab=00845a7d
-/
@[ext] lemma ext {ψ ψ' : StrictHom C₁ C₂} (h : ∀ b, ψ b = ψ' b) : ψ = ψ' :=
  DFunLike.ext _ _ h

/--
@isnad1 id=eq.0h9v.s6.8f83041839ea from=translated src=- shape=e696d342 vocab=17417ba5
-/
@[simp] lemma wt_apply (ψ : StrictHom C₁ C₂) (b : B₁) : C₂.wt (ψ b) = C₁.wt b := ψ.wt_map b

/--
@isnad1 id=eq.0h10v.s6.28d6dfacbc28 from=translated src=- shape=8b38b2ed vocab=ec12bf3e
-/
@[simp] lemma ε_apply (ψ : StrictHom C₁ C₂) (i : ι) (b : B₁) : C₂.ε i (ψ b) = C₁.ε i b :=
  ψ.ε_map i b

/--
@isnad1 id=eq.0h10v.s6.651d09725d76 from=translated src=- shape=c07e7708 vocab=3160fd88
-/
lemma e_apply (ψ : StrictHom C₁ C₂) (i : ι) (b : B₁) : C₂.e i (ψ b) = (C₁.e i b).map ψ :=
  ψ.e_map i b

/--
@isnad1 id=eq.0h10v.s6.0386f7cde28d from=translated src=- shape=c07e7708 vocab=d5b557a7
-/
lemma f_apply (ψ : StrictHom C₁ C₂) (i : ι) (b : B₁) : C₂.f i (ψ b) = (C₁.f i b).map ψ :=
  ψ.f_map i b

/--
@isnad1 id=eq.0h10v.s6.dfdb849e3984 from=translated src=- shape=e3c58fb9 vocab=85164160
-/
lemma fWord_apply (ψ : StrictHom C₁ C₂) (l : List ι) (b : B₁) :
    C₂.fWord l (ψ b) = (C₁.fWord l b).map ψ := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [fWord_cons, fWord_cons, ih]
    cases C₁.fWord l b <;> simp [ψ.f_apply]

/-- Strict morphisms preserve the `φᵢ`.
@isnad1 id=eq.0h10v.s6.bd735ed35c49 from=translated src=- shape=8b38b2ed vocab=94006e90
-/
@[simp] lemma φ_map (ψ : StrictHom C₁ C₂) (i : ι) (b : B₁) : C₂.φ i (ψ b) = C₁.φ i b := by
  rw [C₂.φ_eq, C₁.φ_eq, ψ.ε_apply, ψ.wt_apply]

/-- A strict morphism, seen as a morphism.-/
def toHom (ψ : StrictHom C₁ C₂) : Hom C₁ C₂ where
  toFun b := some (ψ b)
  wt_map b c h := by cases h; simp
  ε_map i b c h := by cases h; simp
  φ_map i b c h := by cases h; simp
  e_map i b b' c c' h hc hc' := by cases hc; cases hc'; simp [ψ.e_apply, h]
  f_map i b b' c c' h hc hc' := by cases hc; cases hc'; simp [ψ.f_apply, h]

variable (C₁) in
/-- The identity strict morphism.-/
@[simps -fullyApplied]
def id : StrictHom C₁ C₁ where
  toFun b := b
  wt_map _ := rfl
  ε_map _ _ := rfl
  e_map _ _ := by simp
  f_map _ _ := by simp

/-- The composition of strict morphisms.-/
def comp (ψ' : StrictHom C₂ C₃) (ψ : StrictHom C₁ C₂) : StrictHom C₁ C₃ where
  toFun b := ψ' (ψ b)
  wt_map _ := by simp
  ε_map _ _ := by simp
  e_map _ _ := by simp [e_apply, Option.map_map, Function.comp_def]
  f_map _ _ := by simp [f_apply, Option.map_map, Function.comp_def]

/--
@isnad1 id=eq.0h12v.s7.70ee1553e71f from=translated src=- shape=f70e8556 vocab=b8a5245a
-/
@[simp] lemma comp_apply (ψ' : StrictHom C₂ C₃) (ψ : StrictHom C₁ C₂) (b : B₁) :
    ψ'.comp ψ b = ψ' (ψ b) := rfl

end StrictHom

namespace Equiv

variable {C₁ C₂ C₃}

instance : EquivLike (Equiv C₁ C₂) B₁ B₂ where
  coe ψ := ψ.toFun
  inv ψ := ψ.invFun
  left_inv ψ := ψ.left_inv
  right_inv ψ := ψ.right_inv
  coe_injective' ψ ψ' h _ := by
    rcases ψ with ⟨⟨⟩⟩; rcases ψ' with ⟨⟨⟩⟩; simp_all

/--
@isnad1 id=eq.1h9v.s7.bb370e2b29bf from=translated src=- shape=6b22a1c4 vocab=b94ceacf
-/
@[ext] lemma ext {ψ ψ' : Equiv C₁ C₂} (h : ∀ b, ψ b = ψ' b) : ψ = ψ' :=
  DFunLike.ext _ _ h

/-- An isomorphism of crystals, as a strict morphism.-/
def toStrictHom (ψ : Equiv C₁ C₂) : StrictHom C₁ C₂ where
  toFun := ψ
  wt_map := ψ.wt_map
  ε_map := ψ.ε_map
  e_map := ψ.e_map
  f_map := ψ.f_map

/--
@isnad1 id=eq.0h8v.s6.1bd37b3409b2 from=translated src=- shape=46ef6328 vocab=2aa7e34b
-/
@[simp] lemma coe_toStrictHom (ψ : Equiv C₁ C₂) : ⇑ψ.toStrictHom = ψ := rfl

/--
@isnad1 id=eq.0h8v.s6.75ae71351430 from=translated src=- shape=4ba86877 vocab=0c12ceb6
-/
@[simp] lemma coe_toEquiv (ψ : Equiv C₁ C₂) : ⇑ψ.toEquiv = ψ := rfl

/--
@isnad1 id=eq.0h9v.s6.4fff6ee60bb5 from=translated src=- shape=1439fc5f vocab=cd5cb042
-/
@[simp] lemma toEquiv_symm_apply_apply (ψ : Equiv C₁ C₂) (b : B₁) : ψ.toEquiv.symm (ψ b) = b :=
  ψ.toEquiv.symm_apply_apply b

/--
@isnad1 id=eq.0h9v.s6.4ca008c7d257 from=translated src=- shape=e696d342 vocab=9bc0d1e6
-/
@[simp] lemma wt_apply (ψ : Equiv C₁ C₂) (b : B₁) : C₂.wt (ψ b) = C₁.wt b := ψ.wt_map b

/--
@isnad1 id=eq.0h10v.s6.bedf9449e9aa from=translated src=- shape=8b38b2ed vocab=5b8efca7
-/
@[simp] lemma ε_apply (ψ : Equiv C₁ C₂) (i : ι) (b : B₁) : C₂.ε i (ψ b) = C₁.ε i b :=
  ψ.ε_map i b

/--
@isnad1 id=eq.0h10v.s6.5bbb8390b6ae from=translated src=- shape=8b38b2ed vocab=834a7e02
-/
@[simp] lemma φ_apply (ψ : Equiv C₁ C₂) (i : ι) (b : B₁) : C₂.φ i (ψ b) = C₁.φ i b :=
  ψ.toStrictHom.φ_map i b

/--
@isnad1 id=eq.0h10v.s7.08640b45f5b8 from=translated src=- shape=c07e7708 vocab=33f477f4
-/
lemma e_apply (ψ : Equiv C₁ C₂) (i : ι) (b : B₁) : C₂.e i (ψ b) = (C₁.e i b).map ψ :=
  ψ.e_map i b

/--
@isnad1 id=eq.0h10v.s7.c6bb857e01b8 from=translated src=- shape=c07e7708 vocab=1801ae2c
-/
lemma f_apply (ψ : Equiv C₁ C₂) (i : ι) (b : B₁) : C₂.f i (ψ b) = (C₁.f i b).map ψ :=
  ψ.f_map i b

variable (C₁) in
/-- The identity isomorphism.-/
def refl : Equiv C₁ C₁ where
  toEquiv := _root_.Equiv.refl B₁
  wt_map _ := rfl
  ε_map _ _ := rfl
  e_map _ _ := by simp
  f_map _ _ := by simp

/-- The inverse of an isomorphism of crystals.-/
def symm (ψ : Equiv C₁ C₂) : Equiv C₂ C₁ where
  toEquiv := ψ.toEquiv.symm
  wt_map c := by
    obtain ⟨b, rfl⟩ := ψ.toEquiv.surjective c
    simp
  ε_map i c := by
    obtain ⟨b, rfl⟩ := ψ.toEquiv.surjective c
    simp
  e_map i c := by
    obtain ⟨b, rfl⟩ := ψ.toEquiv.surjective c
    simp [ψ.e_apply, Option.map_map, Function.comp_def]
  f_map i c := by
    obtain ⟨b, rfl⟩ := ψ.toEquiv.surjective c
    simp [ψ.f_apply, Option.map_map, Function.comp_def]

/-- The composition of isomorphisms of crystals.-/
def trans (ψ : Equiv C₁ C₂) (ψ' : Equiv C₂ C₃) : Equiv C₁ C₃ where
  toEquiv := ψ.toEquiv.trans ψ'.toEquiv
  wt_map _ := by simp
  ε_map _ _ := by simp
  e_map _ _ := by simp [e_apply, Option.map_map, Function.comp_def]
  f_map _ _ := by simp [f_apply, Option.map_map, Function.comp_def]

end Equiv

/-! ### Examples -/

variable (D)

/-- The crystal `T_λ = {t_λ}` ([Kas] Example 7.3, [HK] Example 4.5.2 (2)):
`wt t_λ = λ`, `εᵢ(t_λ) = φᵢ(t_λ) = -∞`, `ẽᵢ t_λ = f̃ᵢ t_λ = 0`.-/
def T (μ : X) : Crystal D Unit where
  wt _ := μ
  ε _ _ := ⊥
  φ _ _ := ⊥
  e _ _ := none
  f _ _ := none
  φ_eq _ _ := by simp
  f_eq_some_iff _ _ _ := by simp
  wt_e _ _ _ h := by simp at h
  ε_e _ _ _ h := by simp at h
  e_eq_none_of_φ_eq_bot _ _ _ := rfl

/-- The crystal `C = {c}` ([Kas94] Example 1.5.3 (1)): `wt c = 0`, `εᵢ(c) = φᵢ(c) = 0`,
`ẽᵢ c = f̃ᵢ c = 0`.-/
def trivial : Crystal D Unit where
  wt _ := 0
  ε _ _ := 0
  φ _ _ := 0
  e _ _ := none
  f _ _ := none
  φ_eq _ _ := by simp
  f_eq_some_iff _ _ _ := by simp
  wt_e _ _ _ h := by simp at h
  ε_e _ _ _ h := by simp at h
  e_eq_none_of_φ_eq_bot _ _ _ := rfl

variable [DecidableEq ι]

/-- The elementary crystal `Bᵢ = {bᵢ(n) | n ∈ ℤ}` ([Kas] Example 7.4, [HK] Example 4.5.2 (3)), with
`bᵢ(n)` modelled by `n : ℤ`: `wt bᵢ(n) = n αᵢ`, `φᵢ(bᵢ(n)) = n`, `εᵢ(bᵢ(n)) = -n`, `εⱼ = φⱼ = -∞`
for `j ≠ i`, `ẽᵢ bᵢ(n) = bᵢ(n + 1)`, `f̃ᵢ bᵢ(n) = bᵢ(n - 1)` and `ẽⱼ = f̃ⱼ = 0` for `j ≠ i`.-/
def elementary (i : ι) : Crystal D ℤ where
  wt n := n • D.root i
  ε j n := if j = i then ((-n : ℤ) : WithBot ℤ) else ⊥
  φ j n := if j = i then ((n : ℤ) : WithBot ℤ) else ⊥
  e j n := if j = i then some (n + 1) else none
  f j n := if j = i then some (n - 1) else none
  φ_eq j n := by
    split_ifs with h
    · subst h
      simp only [map_zsmul, D.coroot_root_self, smul_eq_mul]
      norm_cast
      ring
    · simp
  f_eq_some_iff j n n' := by
    split_ifs with h
    · simp only [Option.some.injEq]; omega
    · simp
  wt_e j n n' h := by
    split_ifs at h with hj
    cases h; subst hj
    simp [add_smul]
  ε_e j n n' h := by
    split_ifs at h with hj
    cases h
    simp only [hj, ite_true]
    norm_cast
    ring
  e_eq_none_of_φ_eq_bot j n h := by
    split_ifs at h ⊢ with hj
    · simp at h
    · rfl

end Tengoku.LieLean.Crystal
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
