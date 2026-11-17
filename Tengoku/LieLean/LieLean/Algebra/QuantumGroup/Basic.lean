/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.Seed.Algebra.FreeAlgebra
import Tengoku.Seed.Algebra.RingQuot
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.CartanDatum
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.QBinomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The quantized enveloping algebra `U_q(𝔤)`

Let `(I, ·)` be a Cartan datum with Cartan matrix `aᵢⱼ = 2 (i·j)/(i·i)` and `dᵢ = (i·i)/2`, and
let `(Y, …)` be a root datum of type `(I, ·)` (after [Lus] 2.2.1, which asks for
free `Y`, `X` of finite rank in perfect duality): an abelian group `Y` (the
coweight lattice) with elements `i ∈ Y` (the simple coroots,
`LusztigCartanDatum.RootDatum.coroot`) and homomorphisms `⟨·, j'⟩ : Y → ℤ` (the simple roots,
`LusztigCartanDatum.RootDatum.root`) such that
`⟨i, j'⟩ = aᵢⱼ`. Let `k` be a field and `v ∈ k`, `vᵢ = v^{dᵢ}`, `K̃ᵢ = K_{dᵢ i}`.

Following [Lus] 3.1.1 and Cor. 33.1.5, `U = U_q(𝔤)` is the associative `k`-algebra with generators
`Eᵢ`, `Fᵢ` (`i ∈ I`) and `K_μ` (`μ ∈ Y`) and relations
* (a) `K_0 = 1`, `K_μ K_ν = K_{μ+ν}`;
* (b) `K_μ Eᵢ = v^{⟨μ, i'⟩} Eᵢ K_μ`;
* (c) `K_μ Fᵢ = v^{-⟨μ, i'⟩} Fᵢ K_μ`;
* (d) `Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ (K̃ᵢ - K̃₋ᵢ)/(vᵢ - vᵢ⁻¹)`;
* (e) the quantum Serre relations `Σ_{r=0}^{1-aᵢⱼ} (-1)^r [1-aᵢⱼ, r]ᵢ Eᵢ^{1-aᵢⱼ-r} Eⱼ Eᵢ^r = 0`
  and likewise for `F`, for `i ≠ j`.

We state the Serre relations in the binomial form of [Jan] 4.3 (R5)–(R6), which makes sense for
every `v`; when `[1 - aᵢⱼ]ᵢ! ≠ 0` (e.g. `v` not a root of unity) it is equivalent to Lusztig's
divided-power form `Σ_{r+s=1-aᵢⱼ} (-1)^r Eᵢ^{(s)} Eⱼ Eᵢ^{(r)} = 0`
(`QuantumGroup.qSerreDiv_eq`). The algebra is constructed as a quotient (`RingQuot`) of the free
algebra on the generators.

## Main definitions

* `LusztigCartanDatum.RootDatum`: a root datum of type `(I, ·)`.
* `QuantumGroup R v`: the algebra `U`; generators `QuantumGroup.E`, `QuantumGroup.F`,
  `QuantumGroup.K`, and `QuantumGroup.Kt i = K̃ᵢ`.
* `QuantumGroup.Relations`: the relations (b)–(e) for elements of an arbitrary `k`-algebra.
* `QuantumGroup.lift`: the universal property.

## Main results

* `QuantumGroup.K_zero`, `K_add`, `K_mul_E`, `K_mul_F`, `E_mul_F_sub`, `serre_E`, `serre_F`.
* `QuantumGroup.lift_E`, `lift_F`, `lift_K`, `QuantumGroup.hom_ext`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §2.2, §3.1, §33.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 4.
-/
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean
open LieLean

noncomputable section

variable {I : Type*}

/-- A root datum of type `(I, ·)` after [Lus] 2.2.1, recorded through the coweight lattice `Y`:
elements `coroot i ∈ Y` and homomorphisms `root j : Y →+ ℤ` with
`⟨i, j'⟩ = root j (coroot i) = aᵢⱼ`. (Lusztig's `X` is the dual lattice, which we do not need; nor
do we require `Y` to be free of finite rank.)-/
structure Tengoku.LieLean.LusztigCartanDatum.RootDatum (D : LusztigCartanDatum I) (Y : Type*) [AddCommGroup Y] where
  /-- The simple coroots `i ∈ Y`.-/
  coroot : I → Y
  /-- The simple roots `j' ∈ X = Hom(Y, ℤ)`.-/
  root : I → Y →+ ℤ
  root_coroot : ∀ i j, root j (coroot i) = D.cartanMatrix i j

namespace LieLean.QuantumGroup

variable (I) in
/-- The generators `Eᵢ`, `Fᵢ`, `K_μ` of the free algebra of which `U` is a quotient.-/
inductive Generator (Y : Type*)
  | E : I → Generator Y
  | F : I → Generator Y
  | K : Y → Generator Y

variable {k Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-- `K̃ᵢ = K_{dᵢ i}`: the element `dᵢ • coroot i ∈ Y`.-/
def ktilde (i : I) : Y := D.d i • R.coroot i

omit [DecidableEq I] in
/--
@isnad1 id=eq.0h6v.s6.c7aef8ef0068 from=translated src=- shape=b9e7d29e vocab=8409c2f6
-/
lemma root_ktilde (i j : I) : R.root j (ktilde R i) = D.d i * D.cartanMatrix i j := by
  simp [ktilde, R.root_coroot]

omit [DecidableEq I] in
/--
@isnad1 id=eq.0h6v.s6.495c5c562a83 from=translated src=- shape=0fefbab9 vocab=f3bbc736
-/
lemma root_ktilde_eq_dot (i j : I) : R.root j (ktilde R i) = D.dot i j := by
  rw [root_ktilde, D.d_mul_cartanMatrix]

omit [DecidableEq I] in
/--
@isnad1 id=eq.0h6v.s7.0daf4da101a9 from=translated src=- shape=183b98cb vocab=7b48d5af
-/
lemma root_ktilde_comm (i j : I) : R.root j (ktilde R i) = R.root i (ktilde R j) := by
  rw [root_ktilde, root_ktilde, D.d_mul_cartanMatrix_comm]

section Relations

variable {A : Type*} [Ring A] [Algebra k A]

/-- The defining relations (b)–(d) of `U` ([Lus] 3.1.1), i.e. all relations except the
quantum Serre relations, for elements `eᵢ, fᵢ` and a family `κ : Y → A` with
`κ(μ + ν) = κ(μ) κ(ν)`, `κ(0) = 1` (encoded as a monoid homomorphism `Multiplicative Y →* A`).-/
structure PreRelations (e f : I → A) (κ : Multiplicative Y →* A) : Prop where
  K_mul_E : ∀ μ i, κ (.ofAdd μ) * e i = v ^ R.root i μ • (e i * κ (.ofAdd μ))
  K_mul_F : ∀ μ i, κ (.ofAdd μ) * f i = v ^ (-R.root i μ) • (f i * κ (.ofAdd μ))
  E_mul_F : ∀ i j, e i * f j - f j * e i = if i = j then
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (κ (.ofAdd (ktilde R i)) - κ (.ofAdd (-ktilde R i))) else 0

/-- The defining relations (b)–(e) of `U` ([Lus] 3.1.1, Cor. 33.1.5; Serre relations in the
binomial form of [Jan] 4.3).-/
structure Relations (e f : I → A) (κ : Multiplicative Y →* A) : Prop
    extends PreRelations R v e f κ where
  serre_E : ∀ i j, i ≠ j → qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (e i) (e j) = 0
  serre_F : ∀ i j, i ≠ j → qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (f i) (f j) = 0

end Relations

variable (k) in
/-- The generator `Eᵢ` of the free algebra.-/
abbrev genE (i : I) : FreeAlgebra k (Generator I Y) := FreeAlgebra.ι k (.E i)

variable (k) in
/-- The generator `Fᵢ` of the free algebra.-/
abbrev genF (i : I) : FreeAlgebra k (Generator I Y) := FreeAlgebra.ι k (.F i)

variable (k) in
/-- The generator `K_μ` of the free algebra.-/
abbrev genK (μ : Y) : FreeAlgebra k (Generator I Y) := FreeAlgebra.ι k (.K μ)

/-- The defining relations of `U` in the free algebra on the generators.-/
inductive Rel : FreeAlgebra k (Generator I Y) → FreeAlgebra k (Generator I Y) → Prop
  | K_zero : Rel (genK k 0) 1
  | K_add (μ ν : Y) : Rel (genK k μ * genK k ν) (genK k (μ + ν))
  | K_E (μ : Y) (i : I) : Rel (genK k μ * genE k i) (v ^ R.root i μ • (genE k i * genK k μ))
  | K_F (μ : Y) (i : I) : Rel (genK k μ * genF k i) (v ^ (-R.root i μ) • (genF k i * genK k μ))
  | E_F (i j : I) : Rel (genE k i * genF k j - genF k j * genE k i) (if i = j then
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (genK k (ktilde R i) - genK k (-ktilde R i)) else 0)
  | serre_E (i j : I) (h : i ≠ j) :
      Rel (qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (genE k i) (genE k j)) 0
  | serre_F (i j : I) (h : i ≠ j) :
      Rel (qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (genF k i) (genF k j)) 0

end LieLean.QuantumGroup

open LieLean.QuantumGroup in
/-- The quantized enveloping algebra `U = U_q(𝔤)` of a root datum `R` of type `(I, ·)` over a
field `k`, at the parameter `v ∈ k` (cf. [Lus] 3.1.1, Cor. 33.1.5, where `k = ℚ(v)`).-/
def LieLean.QuantumGroup {k Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
    {D : LusztigCartanDatum I}
    (R : D.RootDatum Y) (v : k) : Type _ :=
  RingQuot (Rel R v)

namespace LieLean.QuantumGroup

variable {k Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

instance : Ring (QuantumGroup R v) := inferInstanceAs (Ring (RingQuot _))

instance : Algebra k (QuantumGroup R v) := inferInstanceAs (Algebra k (RingQuot _))

/-- The quotient map from the free algebra.-/
def mkAlgHom : FreeAlgebra k (Generator I Y) →ₐ[k] QuantumGroup R v := RingQuot.mkAlgHom k _

/-- The generator `Eᵢ` of `U`.-/
def E (i : I) : QuantumGroup R v := mkAlgHom R v (genE k i)

/-- The generator `Fᵢ` of `U`.-/
def F (i : I) : QuantumGroup R v := mkAlgHom R v (genF k i)

/-- The generators `K_μ` of `U`, as a monoid homomorphism `Multiplicative Y →* U`.-/
def KHom : Multiplicative Y →* QuantumGroup R v where
  toFun μ := mkAlgHom R v (genK k μ.toAdd)
  map_one' := RingQuot.mkAlgHom_rel k Rel.K_zero |>.trans (map_one _)
  map_mul' μ ν := by
    rw [← map_mul]
    exact (RingQuot.mkAlgHom_rel k (Rel.K_add μ.toAdd ν.toAdd)).symm

/-- The generator `K_μ` of `U`.-/
def K (μ : Y) : QuantumGroup R v := KHom R v (.ofAdd μ)

/-- `K̃ᵢ = K_{dᵢ i}`.-/
abbrev Kt (i : I) : QuantumGroup R v := K R v (ktilde R i)

/--
@isnad1 id=eq.0h7v.s8.83b900d58777 from=translated src=- shape=e25eca09 vocab=fe29629d
-/
@[simp] lemma KHom_apply (μ : Multiplicative Y) : KHom R v μ = K R v μ.toAdd := rfl

/--
@isnad1 id=eq.0h7v.s8.fb25288e61c0 from=translated src=- shape=a887488f vocab=f31c3d7c
-/
lemma KHom_apply' (μ : Multiplicative Y) : KHom R v μ = mkAlgHom R v (genK k μ.toAdd) := rfl

/-- `K_0 = 1`.
@isnad1 id=eq.0h6v.s7.92d2f315b86b from=translated src=- shape=8578afe7 vocab=36b26299
-/
@[simp] theorem K_zero : K R v 0 = 1 := map_one (KHom R v)

/-- `K_μ K_ν = K_{μ+ν}`.
@isnad1 id=eq.0h8v.s7.482e5b951c16 from=translated src=- shape=03d7a51a vocab=736c6f72
-/
theorem K_add (μ ν : Y) : K R v μ * K R v ν = K R v (μ + ν) :=
  (map_mul (KHom R v) (.ofAdd μ) (.ofAdd ν)).symm

/--
@isnad1 id=eq.0h7v.s7.d831585ca1c4 from=translated src=- shape=6d915106 vocab=2e482025
-/
theorem K_mul_K_neg (μ : Y) : K R v μ * K R v (-μ) = 1 := by rw [K_add, add_neg_cancel, K_zero]

/--
@isnad1 id=eq.0h7v.s7.29b0bc0fe8a1 from=translated src=- shape=b34618a2 vocab=2e482025
-/
theorem K_neg_mul_K (μ : Y) : K R v (-μ) * K R v μ = 1 := by rw [K_add, neg_add_cancel, K_zero]

/--
@isnad1 id=eq.0h8v.s7.089bec71896a from=translated src=- shape=af7cb989 vocab=f7469b0e
-/
theorem K_comm (μ ν : Y) : K R v μ * K R v ν = K R v ν * K R v μ := by
  rw [K_add, K_add, add_comm]

/-- `K_μ Eᵢ = v^{⟨μ, i'⟩} Eᵢ K_μ`.
@isnad1 id=eq.0h8v.s8.3d11b5592cfc from=translated src=- shape=cc615b7f vocab=dd89cd8c
-/
theorem K_mul_E (μ : Y) (i : I) : K R v μ * E R v i = v ^ R.root i μ • (E R v i * K R v μ) := by
  change mkAlgHom R v (genK k μ) * mkAlgHom R v (genE k i) =
    v ^ R.root i μ • (mkAlgHom R v (genE k i) * mkAlgHom R v (genK k μ))
  rw [← map_mul, ← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k (Rel.K_E μ i)

/-- `K_μ Fᵢ = v^{-⟨μ, i'⟩} Fᵢ K_μ`.
@isnad1 id=eq.0h8v.s8.67dae8f255dc from=translated src=- shape=83bfa070 vocab=39fe7ca5
-/
theorem K_mul_F (μ : Y) (i : I) :
    K R v μ * F R v i = v ^ (-R.root i μ) • (F R v i * K R v μ) := by
  change mkAlgHom R v (genK k μ) * mkAlgHom R v (genF k i) =
    v ^ (-R.root i μ) • (mkAlgHom R v (genF k i) * mkAlgHom R v (genK k μ))
  rw [← map_mul, ← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k (Rel.K_F μ i)

/-- `Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ (K̃ᵢ - K̃₋ᵢ)/(vᵢ - vᵢ⁻¹)`.
@isnad1 id=eq.0h8v.s9.1414da5912d0 from=translated src=- shape=50d6b10a vocab=a2e03aa2
-/
theorem E_mul_F_sub (i j : I) : E R v i * F R v j - F R v j * E R v i = if i = j then
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (Kt R v i - K R v (-ktilde R i)) else 0 := by
  have := RingQuot.mkAlgHom_rel k (Rel.E_F (R := R) (v := v) i j)
  change mkAlgHom R v (genE k i) * mkAlgHom R v (genF k j) -
    mkAlgHom R v (genF k j) * mkAlgHom R v (genE k i) = if i = j then
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ •
      (mkAlgHom R v (genK k (ktilde R i)) - mkAlgHom R v (genK k (-ktilde R i))) else 0
  rw [← map_mul, ← map_mul, ← map_sub]
  split_ifs at this ⊢
  · rw [← map_sub, ← map_smul]; exact this
  · rw [← map_zero (mkAlgHom R v)]; exact this

/-- The quantum Serre relations for the `Eᵢ`.
@isnad1 id=eq.1h8v.s7.6f6e80fbf60d from=translated src=- shape=dd3904c9 vocab=42b0e844
-/
theorem serre_E {i j : I} (h : i ≠ j) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (E R v i) (E R v j) = 0 := by
  change qSerre _ _ (mkAlgHom R v (genE k i)) (mkAlgHom R v (genE k j)) = 0
  rw [← map_qSerre, ← map_zero (mkAlgHom R v)]
  exact RingQuot.mkAlgHom_rel k (Rel.serre_E i j h)

/-- The quantum Serre relations for the `Fᵢ`.
@isnad1 id=eq.1h8v.s7.6305749b88fb from=translated src=- shape=dd3904c9 vocab=edea9692
-/
theorem serre_F {i j : I} (h : i ≠ j) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (F R v i) (F R v j) = 0 := by
  change qSerre _ _ (mkAlgHom R v (genF k i)) (mkAlgHom R v (genF k j)) = 0
  rw [← map_qSerre, ← map_zero (mkAlgHom R v)]
  exact RingQuot.mkAlgHom_rel k (Rel.serre_F i j h)

/-- The generators of `U` satisfy the defining relations.
@isnad1 id=relation.0h6v.s6.7d503c29c36e from=translated src=- shape=14dcc74b vocab=70cb373d
-/
theorem relations : Relations R v (E R v) (F R v) (KHom R v) where
  K_mul_E μ i := K_mul_E R v μ i
  K_mul_F μ i := K_mul_F R v μ i
  E_mul_F i j := E_mul_F_sub R v i j
  serre_E _ _ h := serre_E R v h
  serre_F _ _ h := serre_F R v h

/-- Induction on `U`: a property of elements of `U` that holds for scalars and the generators
and is closed under sums and products holds everywhere.
@isnad1 id=var.0h14v.s9.3e38e58ea9a9 from=translated src=- shape=5da9a2a4 vocab=2634db2b
-/
theorem induction_on {P : QuantumGroup R v → Prop} (x : QuantumGroup R v)
    (algebraMap : ∀ c, P (algebraMap k _ c)) (E : ∀ i, P (E R v i)) (F : ∀ i, P (F R v i))
    (K : ∀ μ, P (K R v μ)) (add : ∀ x y, P x → P y → P (x + y))
    (mul : ∀ x y, P x → P y → P (x * y)) : P x := by
  obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective k (Rel R v) x
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact algebraMap c
  | grade1 g =>
    cases g with
    | E i => exact E i
    | F i => exact F i
    | K μ => exact K μ
  | mul a b ha hb => rw [map_mul]; exact mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact add _ _ ha hb

section lift

variable {R v} {A : Type*} [Ring A] [Algebra k A]

/-- The map on the free algebra defined by `eᵢ, fᵢ, κ`.-/
def freeLift (e f : I → A) (κ : Multiplicative Y →* A) : FreeAlgebra k (Generator I Y) →ₐ[k] A :=
  FreeAlgebra.lift k fun
    | .E i => e i
    | .F i => f i
    | .K μ => κ (.ofAdd μ)

/-- The universal property of `U`: elements `eᵢ, fᵢ` and `κ : Y → A` of a `k`-algebra `A`
satisfying the defining relations determine an algebra homomorphism `U → A`.-/
def lift {e f : I → A} {κ : Multiplicative Y →* A} (h : Relations R v e f κ) :
    QuantumGroup R v →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨freeLift e f κ, fun x y hxy ↦ by
    induction hxy with
    | K_zero => simp [freeLift]
    | K_add μ ν => simp [freeLift, map_mul]
    | K_E μ i => simpa [freeLift] using h.K_mul_E μ i
    | K_F μ i => simpa [freeLift] using h.K_mul_F μ i
    | E_F i j =>
      have := h.E_mul_F i j
      split_ifs at this ⊢ <;> simpa [freeLift] using this
    | serre_E i j hij => simpa [freeLift, map_qSerre] using h.serre_E i j hij
    | serre_F i j hij => simpa [freeLift, map_qSerre] using h.serre_F i j hij⟩

variable {e f : I → A} {κ : Multiplicative Y →* A} (h : Relations R v e f κ)

/--
@isnad1 id=eq.1h11v.s9.c1c68797b31e from=translated src=- shape=76bf0708 vocab=3ea4747c
-/
lemma lift_mkAlgHom (x : FreeAlgebra k (Generator I Y)) :
    lift h (mkAlgHom R v x) = freeLift e f κ x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

/--
@isnad1 id=eq.1h11v.s8.e1d1d225f592 from=translated src=- shape=8911d373 vocab=dec370eb
-/
@[simp] theorem lift_E (i : I) : lift h (E R v i) = e i := by
  rw [E, lift_mkAlgHom]; simp [freeLift]

/--
@isnad1 id=eq.1h11v.s8.78330da8534a from=translated src=- shape=1d4df1ed vocab=6ccc51d6
-/
@[simp] theorem lift_F (i : I) : lift h (F R v i) = f i := by
  rw [F, lift_mkAlgHom]; simp [freeLift]

/--
@isnad1 id=eq.1h11v.s8.5c927405cd4a from=translated src=- shape=588051b2 vocab=b42bc6c9
-/
@[simp] theorem lift_K (μ : Y) : lift h (K R v μ) = κ (.ofAdd μ) := by
  rw [K, KHom_apply']; rw [lift_mkAlgHom]; simp [freeLift]

/-- Algebra homomorphisms out of `U` are determined by their values on the generators.
@isnad1 id=eq.3h9v.s10.479fef19eb5b from=translated src=- shape=680e8764 vocab=ed026795
-/
@[ext]
theorem hom_ext {φ ψ : QuantumGroup R v →ₐ[k] A} (hE : ∀ i, φ (E R v i) = ψ (E R v i))
    (hF : ∀ i, φ (F R v i) = ψ (F R v i)) (hK : ∀ μ, φ (K R v μ) = ψ (K R v μ)) : φ = ψ := by
  refine RingQuot.ringQuot_ext' k φ ψ (FreeAlgebra.hom_ext (funext fun g ↦ ?_))
  cases g with
  | E i => exact hE i
  | F i => exact hF i
  | K μ => exact hK μ

end lift

end LieLean.QuantumGroup
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
