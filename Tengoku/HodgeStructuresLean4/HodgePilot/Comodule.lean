import Tengoku.Seed.RingTheory.Coalgebra.Basic
import Tengoku.Seed.RingTheory.Coalgebra.Hom
import Tengoku.Seed.RingTheory.Bialgebra.Basic
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.RightExactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Right comodules over a coalgebra

The pinned Mathlib has **no comodule API whatsoever** (zero hits for
`comodule`/`coaction` across the whole library), yet every route to Tannaka
reconstruction passes through comodules: representations of an affine group
scheme *are* comodules over its Hopf algebra. This file supplies the missing
substrate — right comodules over a coalgebra, with the regular comodule,
comodule morphisms, and corestriction — as Stage 1 of the reconstruction
campaign (`reconstruction_design_memo.md` §6, §10; design record in
`comodule_design_memo.md`).

The content is pure Mathlib (no HodgePilot imports), written in the house style
of `Mathlib.RingTheory.Coalgebra.Basic`/`Hom`, as an upstream candidate; only
the namespace is local.

## Main definitions

* `HodgePilot.ComoduleStruct R A M` — the data layer, mirroring
  `CoalgebraStruct`: a right coaction `coaction : M →ₗ[R] M ⊗[R] A`.
* `HodgePilot.Comodule R A M` — the law layer, mirroring `Coalgebra`:
  counitality and coassociativity, stated in the `lTensor`/`rTensor`
  composition style of `Coalgebra`.
* `HodgePilot.Comodule.Repr` — finite-sum representations of `coaction m`,
  mirroring the `Coalgebra.Repr` (Sweedler-notation) idiom, with the
  counit/coassociativity laws in summation form.
* `HodgePilot.Comodule.regular` — the **regular comodule**: `A` is a right
  comodule over itself via `comul`. This is the design validator: the two
  comodule laws are precisely the right counit law and
  `Coalgebra.coassoc_symm`.
* `HodgePilot.ComodHom R A M N` — bundled comodule morphisms, extending
  `M →ₗ[R] N`, with `id`, `comp`, `ext` and the category axioms at the raw
  level (the bundled category is Stage 2).
* `HodgePilot.Comodule.base R A` — `R` as a right `A`-comodule via
  `r ↦ r ⊗ₜ 1` when `A` is a bialgebra (the "trivial representation").
  Deliberately **not** an instance: at `A = R` it would collide
  non-definitionally with the regular comodule.
* `HodgePilot.ComoduleStruct.corestrict` / `HodgePilot.Comodule.corestrict` —
  corestriction of a comodule along a coalgebra morphism `f : A →ₗc[R] B`
  (postcomposition with `LinearMap.lTensor M f`), with functoriality lemmas;
  `HodgePilot.ComodHom.corestrict` transports morphisms.
* `HodgePilot.IsCoactionInvariant` — the submodules `p ⊆ M` to which the
  coaction restricts (`ρ(p) ⊆ p ⊗ A` inside `M ⊗ A`). When `A` is `R`-flat
  (so that `p ⊗[R] A → M ⊗[R] A` is injective and the factorization is
  legitimate), `HodgePilot.IsCoactionInvariant.comodule` makes such a `p` a
  comodule, and `HodgePilot.ComodHom.isCoactionInvariant_ker` shows kernels of
  comodule morphisms qualify (over a ring, by right-exactness of `⊗`).

## Conventions

**Right** comodules, in the Waterhouse/Milne convention (*Introduction to
Affine Group Schemes*, ch. 3): the coaction lands in `M ⊗[R] A` with the
coalgebra in the **right** tensor factor — the Tannakian literature's matrix
coefficients sit there. Coassociativity is stated with the *inverse* associator
`(TensorProduct.assoc R M A A).symm` on the comultiplication side, so that for
the regular comodule it is `Coalgebra.coassoc_symm.symm` on the nose.
-/

open scoped TensorProduct
open Coalgebra

universe u v w w'

namespace HodgePilot

/-- Data fields for `HodgePilot.Comodule`, to allow API to be constructed before
proving the comodule laws; mirrors the `CoalgebraStruct`/`Coalgebra` layering.

See `HodgePilot.Comodule` for documentation.-/
class ComoduleStruct (R : Type u) (A : Type v) (M : Type w) [CommSemiring R]
    [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
    [AddCommMonoid M] [Module R M] where
  /-- The right coaction of the coalgebra `A` on `M`.-/
  coaction : M →ₗ[R] M ⊗[R] A

/-- A right comodule `M` over an `R`-coalgebra `A` is an `R`-module equipped
with a coaction `ρ : M →ₗ[R] M ⊗[R] A` that is counital and coassociative.

The two laws are stated in the `lTensor`/`rTensor` composition style of
`Coalgebra`:
* counitality: `(1_M ⊗ ε) ∘ ρ = 1_M` after collapsing `M ⊗[R] R` via
  `TensorProduct.rid`;
* coassociativity: `(ρ ⊗ 1_A) ∘ ρ = α⁻¹ ∘ (1_M ⊗ Δ) ∘ ρ`, where `α` is
  `TensorProduct.assoc R M A A`.-/
class Comodule (R : Type u) (A : Type v) (M : Type w) [CommSemiring R]
    [AddCommMonoid A] [Module R A] [Coalgebra R A]
    [AddCommMonoid M] [Module R M] extends ComoduleStruct R A M where
  /-- The coaction is counital.-/
  coaction_counit :
    (TensorProduct.rid R M).toLinearMap ∘ₗ
      LinearMap.lTensor M (Coalgebra.counit (R := R) (A := A)) ∘ₗ coaction = LinearMap.id
  /-- The coaction is coassociative.-/
  coaction_coassoc :
    LinearMap.rTensor A coaction ∘ₗ coaction =
      (TensorProduct.assoc R M A A).symm.toLinearMap ∘ₗ
        LinearMap.lTensor M (Coalgebra.comul (R := R) (A := A)) ∘ₗ coaction

namespace Comodule
export ComoduleStruct (coaction)
end Comodule

section ComoduleStructLemmas

variable {R : Type u} {A : Type v} {M : Type w} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
  [AddCommMonoid M] [Module R M]

/-- Two comodule structures with the same coaction are equal.-/
theorem ComoduleStruct.ext {inst₁ inst₂ : ComoduleStruct R A M}
    (h : inst₁.coaction = inst₂.coaction) : inst₁ = inst₂ := by
  cases inst₁; cases inst₂; congr 1

/--
A representation of an element `m` of a right `A`-comodule `M` is a finite sum
of pure tensors `∑ mᵢ ⊗ aᵢ` that is equal to `coaction m`; mirrors
`Coalgebra.Repr` (the Sweedler-notation idiom of the pinned Mathlib).-/
structure Comodule.Repr (R : Type u) (A : Type v) {M : Type w} [CommSemiring R]
    [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
    [AddCommMonoid M] [Module R M] [ComoduleStruct R A M] (m : M) (ι : Type*) where
  /-- the finite indexing set of a representation of `coaction m`-/
  index : Finset ι
  /-- the first (module) coordinate of a representation of `coaction m`-/
  left : ι → M
  /-- the second (coalgebra) coordinate of a representation of `coaction m`-/
  right : ι → A
  /-- `coaction m` is equal to a finite sum of pure tensors-/
  eq : ∑ i ∈ index, left i ⊗ₜ[R] right i = ComoduleStruct.coaction (R := R) (A := A) m

/-- An arbitrarily chosen representation; mirrors `Coalgebra.Repr.arbitrary`.-/
noncomputable def Comodule.Repr.arbitrary (R : Type u) (A : Type v) {M : Type w}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
    [AddCommMonoid M] [Module R M] [ComoduleStruct R A M] (m : M) :
    Comodule.Repr R A m (M × A) where
  left := Prod.fst
  right := Prod.snd
  index :=
    (TensorProduct.exists_finset (R := R)
      (ComoduleStruct.coaction (R := R) (A := A) m)).choose
  eq :=
    (TensorProduct.exists_finset (R := R)
      (ComoduleStruct.coaction (R := R) (A := A) m)).choose_spec.symm

end ComoduleStructLemmas

section ComoduleExt

variable {R : Type u} {A : Type v} {M : Type w} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [Coalgebra R A] [AddCommMonoid M] [Module R M]

/-- Two comodule instances with the same coaction are equal.-/
theorem Comodule.ext {inst₁ inst₂ : Comodule R A M}
    (h : inst₁.coaction = inst₂.coaction) : inst₁ = inst₂ := by
  cases inst₁; cases inst₂
  obtain rfl := ComoduleStruct.ext h
  rfl

end ComoduleExt

section ComoduleLemmas

namespace Comodule

variable {R : Type u} {A : Type v} {M : Type w} {ι : Type*} {κ Λ : ι → Type*}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] {m : M}

@[simp]
theorem coaction_counit_apply (m : M) :
    TensorProduct.rid R M
      (LinearMap.lTensor M (Coalgebra.counit (R := R) (A := A))
        (coaction (R := R) (A := A) m)) = m :=
  LinearMap.congr_fun (coaction_counit (R := R) (A := A) (M := M)) m

@[simp]
theorem lTensor_counit_coaction (m : M) :
    LinearMap.lTensor M (Coalgebra.counit (R := R) (A := A))
      (coaction (R := R) (A := A) m) = m ⊗ₜ[R] 1 := by
  rw [← TensorProduct.rid_symm_apply, LinearEquiv.eq_symm_apply]
  exact coaction_counit_apply m

theorem coaction_coassoc_apply (m : M) :
    LinearMap.rTensor A (coaction (R := R) (A := A) (M := M))
        (coaction (R := R) (A := A) m) =
      (TensorProduct.assoc R M A A).symm
        (LinearMap.lTensor M (Coalgebra.comul (R := R) (A := A))
          (coaction (R := R) (A := A) m)) :=
  LinearMap.congr_fun (coaction_coassoc (R := R) (A := A) (M := M)) m

@[simp]
theorem assoc_rTensor_coaction (m : M) :
    TensorProduct.assoc R M A A
        (LinearMap.rTensor A (coaction (R := R) (A := A) (M := M))
          (coaction (R := R) (A := A) m)) =
      LinearMap.lTensor M (Coalgebra.comul (R := R) (A := A))
        (coaction (R := R) (A := A) m) := by
  rw [coaction_coassoc_apply]
  exact (TensorProduct.assoc R M A A).apply_symm_apply _

/-- Coassociativity with the associator on the coaction side; mirrors
`Coalgebra.coassoc`.-/
theorem coaction_coassoc' :
    (TensorProduct.assoc R M A A).toLinearMap ∘ₗ
        LinearMap.rTensor A (coaction (R := R) (A := A) (M := M)) ∘ₗ coaction =
      LinearMap.lTensor M (Coalgebra.comul (R := R) (A := A)) ∘ₗ coaction :=
  LinearMap.ext fun m => assoc_rTensor_coaction m

/-- The counit law in summation form: for `coaction m = ∑ mᵢ ⊗ aᵢ` we get
`∑ ε(aᵢ) • mᵢ = m`; mirrors `Coalgebra.sum_counit_smul`.-/
lemma sum_counit_smul (repr : Comodule.Repr R A m ι) :
    ∑ i ∈ repr.index, Coalgebra.counit (R := R) (repr.right i) • repr.left i = m := by
  have h := coaction_counit_apply (R := R) (A := A) m
  rw [← repr.eq] at h
  simpa [map_sum] using h

/-- The counit law in summation form, tensor version: for
`coaction m = ∑ mᵢ ⊗ aᵢ` we get `∑ mᵢ ⊗ ε(aᵢ) = m ⊗ 1`; mirrors
`Coalgebra.sum_tmul_counit_eq`.-/
@[simp]
lemma sum_tmul_counit_eq (repr : Comodule.Repr R A m ι) :
    ∑ i ∈ repr.index, repr.left i ⊗ₜ Coalgebra.counit (R := R) (repr.right i) =
      m ⊗ₜ[R] 1 := by
  simpa [← repr.eq, map_sum] using lTensor_counit_coaction (R := R) (A := A) m

/-- Coassociativity in summation form ("Sweedler bookkeeping"): expanding
`(ρ ⊗ 1) ∘ ρ` along a representation of `m` and representations of its left
legs agrees with expanding `(1 ⊗ Δ) ∘ ρ` along representations of its right
legs; mirrors `Coalgebra.sum_tmul_tmul_eq`.-/
lemma sum_tmul_tmul_eq (repr : Comodule.Repr R A m ι)
    (m₁ : (i : ι) → Comodule.Repr R A (repr.left i) (κ i))
    (a₂ : (i : ι) → Coalgebra.Repr R (repr.right i) (Λ i)) :
    ∑ i ∈ repr.index, ∑ j ∈ (m₁ i).index,
      (m₁ i).left j ⊗ₜ[R] ((m₁ i).right j ⊗ₜ[R] repr.right i)
      = ∑ i ∈ repr.index, ∑ j ∈ (a₂ i).index,
      repr.left i ⊗ₜ[R] ((a₂ i).left j ⊗ₜ[R] (a₂ i).right j) := by
  simpa [(a₂ _).eq, ← (m₁ _).eq, ← TensorProduct.tmul_sum, TensorProduct.sum_tmul,
    ← repr.eq] using assoc_rTensor_coaction (R := R) (A := A) m

end Comodule

end ComoduleLemmas

section Regular

variable (R : Type u) (A : Type v) [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Coalgebra R A]

/-- **The regular comodule**: a coalgebra is a right comodule over itself, with
the comultiplication as coaction. The two comodule laws are the right counit
law and `Coalgebra.coassoc_symm` — this instance is the design validator for
the shape of the `Comodule` fields (memo §10, risk R1).-/
instance Comodule.regular : Comodule R A A where
  coaction := Coalgebra.comul
  coaction_counit := by ext a; simp
  coaction_coassoc := Coalgebra.coassoc_symm.symm

variable {R A}

/-- On the regular comodule the coaction is the comultiplication.-/
@[simp]
theorem Comodule.coaction_eq_comul :
    Comodule.coaction (R := R) (A := A) (M := A) = Coalgebra.comul := rfl

end Regular

/-! ## Morphisms of comodules -/

/-- Given right `A`-comodules `M, N` with coactions `ρ_M, ρ_N`, a comodule
morphism `ComodHom R A M N` is an `R`-linear map `f : M →ₗ[R] N` such that
`(f ⊗ 1_A) ∘ ρ_M = ρ_N ∘ f`. Mirrors `CoalgHom`.-/
structure ComodHom (R : Type u) (A : Type v) (M : Type w) (N : Type w')
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [ComoduleStruct R A M] [ComoduleStruct R A N] extends M →ₗ[R] N where
  coaction_comm :
    LinearMap.rTensor A toLinearMap ∘ₗ ComoduleStruct.coaction =
      ComoduleStruct.coaction ∘ₗ toLinearMap

namespace ComodHom

variable {R : Type u} {A : Type v} {M N P Q : Type*}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
  [ComoduleStruct R A M] [ComoduleStruct R A N] [ComoduleStruct R A P]
  [ComoduleStruct R A Q]

instance funLike : FunLike (ComodHom R A M N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr

instance linearMapClass : LinearMapClass (ComodHom R A M N) R M N where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'

@[simp]
theorem coe_mk {f : M →ₗ[R] N} (h) : ((⟨f, h⟩ : ComodHom R A M N) : M → N) = f :=
  rfl

@[simp]
theorem toLinearMap_eq_coe (f : ComodHom R A M N) : f.toLinearMap = f :=
  rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : ComodHom R A M N) : ⇑(f : M →ₗ[R] N) = f :=
  rfl

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : ComodHom R A M N → M →ₗ[R] N) :=
  fun _f _g h => DFunLike.ext _ _ fun m => DFunLike.congr_fun h m

@[ext]
theorem ext {f g : ComodHom R A M N} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext _ _ h

protected theorem congr_fun {f g : ComodHom R A M N} (h : f = g) (m : M) : f m = g m :=
  DFunLike.congr_fun h m

/-- The defining law of a comodule morphism, applied to an element.-/
@[simp]
theorem coaction_comm_apply (f : ComodHom R A M N) (m : M) :
    LinearMap.rTensor A (f : M →ₗ[R] N) (Comodule.coaction (R := R) (A := A) m) =
      Comodule.coaction (R := R) (A := A) (f m) :=
  LinearMap.congr_fun f.coaction_comm m

variable (R A M) in
/-- The identity map as a comodule morphism.-/
protected def id : ComodHom R A M M :=
  { LinearMap.id with
    coaction_comm := by rw [LinearMap.rTensor_id, LinearMap.id_comp, LinearMap.comp_id] }

@[simp]
theorem coe_id : ⇑(ComodHom.id R A M) = _root_.id :=
  rfl

@[simp]
theorem id_apply (m : M) : ComodHom.id R A M m = m :=
  rfl

@[simp]
theorem id_toLinearMap : (ComodHom.id R A M).toLinearMap = LinearMap.id :=
  rfl

/-- Composition of comodule morphisms.-/
def comp (g : ComodHom R A N P) (f : ComodHom R A M N) : ComodHom R A M P :=
  { g.toLinearMap ∘ₗ f.toLinearMap with
    coaction_comm := by
      rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, f.coaction_comm,
        ← LinearMap.comp_assoc, g.coaction_comm, LinearMap.comp_assoc] }

@[simp]
theorem coe_comp (g : ComodHom R A N P) (f : ComodHom R A M N) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem comp_apply (g : ComodHom R A N P) (f : ComodHom R A M N) (m : M) :
    g.comp f m = g (f m) :=
  rfl

@[simp]
theorem comp_toLinearMap (g : ComodHom R A N P) (f : ComodHom R A M N) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  rfl

/-! Raw-level category axioms (the bundled category is Stage 2). -/

@[simp]
theorem id_comp (f : ComodHom R A M N) : (ComodHom.id R A N).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : ComodHom R A M N) : f.comp (ComodHom.id R A M) = f :=
  ext fun _ => rfl

theorem comp_assoc (h : ComodHom R A P Q) (g : ComodHom R A N P) (f : ComodHom R A M N) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

end ComodHom

section ReprInduced

variable {R : Type u} {A : Type v} {M N : Type*} {ι : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [ComoduleStruct R A M] [ComoduleStruct R A N]

/-- If `φ : M → N` is a comodule map and `coaction m = ∑ mᵢ ⊗ aᵢ`, then
`coaction (φ m) = ∑ φ mᵢ ⊗ aᵢ`; mirrors `Coalgebra.Repr.induced`.-/
@[simps]
def Comodule.Repr.induced {m : M} (repr : Comodule.Repr R A m ι)
    (φ : ComodHom R A M N) : Comodule.Repr R A (φ m) ι where
  index := repr.index
  left := ⇑φ ∘ repr.left
  right := repr.right
  eq := by
    rw [← ComodHom.coaction_comm_apply, ← repr.eq, map_sum]
    simp

end ReprInduced

/-! ## The base comodule over a bialgebra -/

section Base

variable (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- The **base comodule**: `R` is a right comodule over any `R`-bialgebra `A`
via the unit, `r ↦ r ⊗ₜ 1` — the "trivial representation". (A bialgebra is
needed: counitality uses `ε(1) = 1` and coassociativity uses `Δ(1) = 1 ⊗ 1`.)

This is deliberately **not** an instance: at `A = R` it would overlap with the
regular comodule `Comodule.regular R R` with a propositionally equal but not
definitionally equal coaction (`r ↦ r ⊗ₜ 1` versus `r ↦ 1 ⊗ₜ r`) — an
instance diamond. Use `letI := Comodule.base R A` where needed.-/
abbrev Comodule.base : Comodule R A R where
  coaction := (TensorProduct.mk R R A).flip 1
  coaction_counit := by ext; simp
  coaction_coassoc := by ext; simp [Algebra.TensorProduct.one_def]

@[simp]
theorem Comodule.base_coaction_apply (r : R) :
    (Comodule.base R A).coaction r = r ⊗ₜ[R] (1 : A) :=
  rfl

end Base

/-! ## Corestriction along a coalgebra morphism -/

section Corestrict

variable {R : Type u} {A : Type v} {B : Type w} {C M N : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section Struct

variable [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C]

variable (M) in
/-- Corestriction of a comodule structure along a coalgebra morphism: if `M` is
a right `A`-comodule and `f : A →ₗc[R] B`, then `M` is a right `B`-comodule
with coaction `(1_M ⊗ f) ∘ ρ`.-/
abbrev ComoduleStruct.corestrict [ComoduleStruct R A M] (f : A →ₗc[R] B) :
    ComoduleStruct R B M where
  coaction := LinearMap.lTensor M f.toLinearMap ∘ₗ coaction (R := R) (A := A)

@[simp]
theorem ComoduleStruct.corestrict_coaction [ComoduleStruct R A M] (f : A →ₗc[R] B) :
    (ComoduleStruct.corestrict M f).coaction =
      LinearMap.lTensor M f.toLinearMap ∘ₗ coaction (R := R) (A := A) :=
  rfl

/-- Corestriction along the identity is the identity.-/
theorem ComoduleStruct.corestrict_id [ComoduleStruct R A M] :
    ComoduleStruct.corestrict M (CoalgHom.id R A) = ‹ComoduleStruct R A M› :=
  ComoduleStruct.ext (by simp)

/-- Corestriction along a composite is the composite of the corestrictions
(functoriality at the raw level).-/
theorem ComoduleStruct.corestrict_comp [ComoduleStruct R A M]
    (g : B →ₗc[R] C) (f : A →ₗc[R] B) :
    ComoduleStruct.corestrict M (g.comp f) =
      (letI := ComoduleStruct.corestrict M f; ComoduleStruct.corestrict M g) := by
  letI := ComoduleStruct.corestrict M f
  exact ComoduleStruct.ext (by simp [LinearMap.lTensor_comp, LinearMap.comp_assoc])

/-- A comodule morphism over `A` is also a comodule morphism over `B` after
corestriction along `f : A →ₗc[R] B` (functoriality in the comodule slot).-/
def ComodHom.corestrict [ComoduleStruct R A M] [ComoduleStruct R A N]
    (f : A →ₗc[R] B) (φ : ComodHom R A M N) :
    letI := ComoduleStruct.corestrict M f
    letI := ComoduleStruct.corestrict N f
    ComodHom R B M N :=
  letI := ComoduleStruct.corestrict M f
  letI := ComoduleStruct.corestrict N f
  { toLinearMap := φ.toLinearMap
    coaction_comm := by
      show LinearMap.rTensor B φ.toLinearMap ∘ₗ
          (LinearMap.lTensor M f.toLinearMap ∘ₗ
            ComoduleStruct.coaction (R := R) (A := A) (M := M)) =
        (LinearMap.lTensor N f.toLinearMap ∘ₗ
            ComoduleStruct.coaction (R := R) (A := A) (M := N)) ∘ₗ
          φ.toLinearMap
      rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, φ.coaction_comm,
        ← LinearMap.comp_assoc] }

@[simp]
theorem ComodHom.coe_corestrict [ComoduleStruct R A M] [ComoduleStruct R A N]
    (f : A →ₗc[R] B) (φ : ComodHom R A M N) : ⇑(φ.corestrict f) = ⇑φ :=
  rfl

end Struct

section Laws

variable [Coalgebra R A] [Coalgebra R B]

variable (M) in
/-- Corestriction of a comodule along a coalgebra morphism: the corestricted
structure `ComoduleStruct.corestrict` satisfies the comodule laws.-/
abbrev Comodule.corestrict [Comodule R A M] (f : A →ₗc[R] B) : Comodule R B M where
  toComoduleStruct := ComoduleStruct.corestrict M f
  coaction_counit := by
    rw [ComoduleStruct.corestrict_coaction,
      ← LinearMap.comp_assoc (ComoduleStruct.coaction (R := R) (A := A) (M := M))
        (LinearMap.lTensor M f.toLinearMap)
        (LinearMap.lTensor M (Coalgebra.counit (R := R) (A := B))),
      ← LinearMap.lTensor_comp, f.counit_comp]
    exact Comodule.coaction_counit
  coaction_coassoc := by
    have hnat :
        TensorProduct.map (LinearMap.lTensor M f.toLinearMap) f.toLinearMap ∘ₗ
            (TensorProduct.assoc R M A A).symm.toLinearMap =
          (TensorProduct.assoc R M B B).symm.toLinearMap ∘ₗ
            LinearMap.lTensor M (TensorProduct.map f.toLinearMap f.toLinearMap) := by
      simpa only [← LinearMap.lTensor_def] using
        TensorProduct.map_map_comp_assoc_symm_eq (LinearMap.id (M := M))
          f.toLinearMap f.toLinearMap
    rw [ComoduleStruct.corestrict_coaction, LinearMap.rTensor_comp, LinearMap.comp_assoc,
      ← LinearMap.comp_assoc (ComoduleStruct.coaction (R := R) (A := A) (M := M))
        (LinearMap.lTensor M f.toLinearMap)
        (LinearMap.rTensor B (ComoduleStruct.coaction (R := R) (A := A) (M := M))),
      LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_assoc, Comodule.coaction_coassoc,
      ← LinearMap.comp_assoc _ (LinearMap.lTensor (M ⊗[R] A) f.toLinearMap)
        (LinearMap.rTensor B (LinearMap.lTensor M f.toLinearMap)),
      LinearMap.rTensor_comp_lTensor,
      ← LinearMap.comp_assoc _ (TensorProduct.assoc R M A A).symm.toLinearMap
        (TensorProduct.map (LinearMap.lTensor M f.toLinearMap) f.toLinearMap),
      hnat, LinearMap.comp_assoc,
      ← LinearMap.comp_assoc (ComoduleStruct.coaction (R := R) (A := A) (M := M))
        (LinearMap.lTensor M f.toLinearMap)
        (LinearMap.lTensor M (Coalgebra.comul (R := R) (A := B))),
      ← LinearMap.lTensor_comp, ← f.map_comp_comul, LinearMap.lTensor_comp,
      LinearMap.comp_assoc]

@[simp]
theorem Comodule.corestrict_coaction [Comodule R A M] (f : A →ₗc[R] B) :
    (Comodule.corestrict M f).coaction =
      LinearMap.lTensor M f.toLinearMap ∘ₗ Comodule.coaction (R := R) (A := A) :=
  rfl

/-- Corestriction along the identity is the identity (law level).-/
theorem Comodule.corestrict_id [Comodule R A M] :
    Comodule.corestrict M (CoalgHom.id R A) = ‹Comodule R A M› :=
  Comodule.ext (by simp)

end Laws

end Corestrict

/-! ## Submodule comodules (stretch layer)

A submodule `p ⊆ M` of a right comodule inherits a comodule structure as soon
as the coaction restricts to it — the classical "subcomodule" notion. The
factorization through `p ⊗[R] A ⊆ M ⊗[R] A` is only legitimate when
`p ⊗[R] A → M ⊗[R] A` is injective, which flatness of `A` guarantees (over a
field — the Tannakian case — this is automatic). -/

section SubComodule

variable {R : Type u} {A : Type v} {M : Type w} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M]

section Struct

variable [CoalgebraStruct R A]

variable (A) in
/-- A submodule `p` of a right `A`-comodule `M` is **coaction-invariant** if
the coaction sends `p` into the canonical image of `p ⊗[R] A` in `M ⊗[R] A`.-/
def IsCoactionInvariant [ComoduleStruct R A M] (p : Submodule R M) : Prop :=
  ∀ x ∈ p, ComoduleStruct.coaction (R := R) (A := A) x ∈
    LinearMap.range (LinearMap.rTensor A p.subtype)

variable [ComoduleStruct R A M] [Module.Flat R A] {p : Submodule R M}

/-- The coaction of `M`, restricted to a coaction-invariant submodule `p` and
corestricted to `p ⊗[R] A`; flatness of `A` makes `p ⊗[R] A → M ⊗[R] A`
injective, which legitimizes the factorization.-/
noncomputable def IsCoactionInvariant.coactionRestrict (hp : IsCoactionInvariant A p) :
    ↥p →ₗ[R] ↥p ⊗[R] A :=
  (LinearEquiv.ofInjective (LinearMap.rTensor A p.subtype)
        (Module.Flat.rTensor_preserves_injective_linearMap p.subtype
          p.injective_subtype)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (LinearMap.rTensor A p.subtype))
      (ComoduleStruct.coaction (R := R) (A := A) ∘ₗ p.subtype)
      fun x => hp x x.2

/-- The comodule structure (data layer) on a coaction-invariant submodule.-/
noncomputable abbrev IsCoactionInvariant.comoduleStruct (hp : IsCoactionInvariant A p) :
    ComoduleStruct R A ↥p where
  coaction := hp.coactionRestrict

end Struct

section Laws

variable [Coalgebra R A] [Comodule R A M] [Module.Flat R A] {p : Submodule R M}

end Laws

section Kernel

variable {R : Type u} {A : Type v} {M : Type w} {N : Type w'} [CommRing R]
  [AddCommGroup A] [Module R A] [CoalgebraStruct R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [ComoduleStruct R A M] [ComoduleStruct R A N]

/-- **Kernels of comodule morphisms are coaction-invariant.** Over a ring, by
right-exactness of the tensor product, `ker (φ ⊗ 1) = im (ker φ ⊗ 1 → M ⊗ A)`
once the injective `M ⧸ ker φ → N` stays injective after tensoring — which
flatness of `A` guarantees.-/
theorem ComodHom.isCoactionInvariant_ker [Module.Flat R A] (φ : ComodHom R A M N) :
    IsCoactionInvariant A (LinearMap.ker φ.toLinearMap) := by
  intro x hx
  rw [← rTensor_mkQ A (LinearMap.ker φ.toLinearMap), LinearMap.mem_ker]
  have hinj : Function.Injective
      (LinearMap.rTensor A
        ((LinearMap.ker φ.toLinearMap).liftQ φ.toLinearMap le_rfl)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _
      (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ le_rfl le_rfl))
  apply hinj
  have hφ : LinearMap.rTensor A
        ((LinearMap.ker φ.toLinearMap).liftQ φ.toLinearMap le_rfl) ∘ₗ
      LinearMap.rTensor A (LinearMap.ker φ.toLinearMap).mkQ =
        LinearMap.rTensor A φ.toLinearMap := by
    rw [← LinearMap.rTensor_comp, Submodule.liftQ_mkQ]
  calc LinearMap.rTensor A ((LinearMap.ker φ.toLinearMap).liftQ φ.toLinearMap le_rfl)
        (LinearMap.rTensor A (LinearMap.ker φ.toLinearMap).mkQ
          (ComoduleStruct.coaction (R := R) (A := A) x))
      = LinearMap.rTensor A φ.toLinearMap
          (ComoduleStruct.coaction (R := R) (A := A) x) := LinearMap.congr_fun hφ _
    _ = ComoduleStruct.coaction (R := R) (A := A) (φ.toLinearMap x) :=
        LinearMap.congr_fun φ.coaction_comm x
    _ = 0 := by rw [LinearMap.mem_ker.mp hx, map_zero]
    _ = LinearMap.rTensor A
          ((LinearMap.ker φ.toLinearMap).liftQ φ.toLinearMap le_rfl) 0 :=
        (map_zero _).symm

end Kernel

end SubComodule

end HodgePilot
