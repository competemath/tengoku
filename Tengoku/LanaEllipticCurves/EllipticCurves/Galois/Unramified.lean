/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.Valuation.RamificationGroup
import Tengoku.Seed.GroupTheory.GroupAction.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unramified Galois modules

This file introduces the representation-theoretic vocabulary needed to state the
Néron–Ogg–Shafarevich criterion (issue #73): the notion of a Galois module being
*unramified*, meaning that a distinguished *inertia* subgroup acts trivially.

We work with a group `G` (thought of as a Galois group `Gal(K̄/K)` or `Gal(L/K)`)
together with a subgroup `I ≤ G` (the inertia subgroup) and a `G`-action on some
type `M` (the Galois module).

## Main definitions

* `IsUnramified I M` : the subgroup `I` acts trivially on `M`, i.e. every `σ ∈ I`
  fixes every element of `M`.

## Main results

* `isUnramified_iff_fixedPoints_eq_univ`, `IsUnramified.mem_fixedPoints` : the
  relation with the set of fixed points `M ^ I`.
* `IsUnramified.of_injective`, `IsUnramified.of_surjective` : `IsUnramified` is
  inherited by `G`-equivariant sub-objects and quotients.
* `IsUnramified.prod`, `IsUnramified.pi` : `IsUnramified` is preserved by
  (finite) products.
* `IsUnramified.mono`, `isUnramified_bot` : monotonicity in the inertia subgroup,
  and the trivial inertia subgroup gives no ramification.
* `ValuationSubring.IsUnramifiedAt` : the special case where `I` is the inertia
  subgroup `ValuationSubring.inertiaSubgroup` of a valuation subring, which is the
  situation for the ℓ-adic Tate module of an elliptic curve.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.7.
-/

open scoped Pointwise

variable {G : Type*} [Group G] (I : Subgroup G)

/-- A type `M` carrying a `G`-action is **unramified** with respect to the subgroup
`I ≤ G` (thought of as an inertia subgroup) if `I` acts trivially on `M`, i.e. every
`σ ∈ I` fixes every element of `M`.

This is the module-theoretic input to the Néron–Ogg–Shafarevich criterion: an elliptic
curve has good reduction exactly when its Tate module is unramified in this sense. -/
def IsUnramified (M : Type*) [SMul G M] : Prop :=
  ∀ σ ∈ I, ∀ m : M, σ • m = m

variable {I}

theorem IsUnramified.smul_eq {M : Type*} [SMul G M] (h : IsUnramified I M)
    {σ : G} (hσ : σ ∈ I) (m : M) : σ • m = m :=
  h σ hσ m

section FixedPoints

variable {M : Type*} [MulAction G M]

end FixedPoints

section Hom

variable {M N : Type*} [SMul G M] [SMul G N]

/-- `IsUnramified` passes to a `G`-equivariant quotient (a surjective equivariant map). -/
theorem IsUnramified.of_surjective (hM : IsUnramified I M) {f : M → N}
    (hf : Function.Surjective f) (hf_smul : ∀ (σ : G) (m : M), f (σ • m) = σ • f m) :
    IsUnramified I N := by
  intro σ hσ n
  obtain ⟨m, rfl⟩ := hf n
  rw [← hf_smul, hM σ hσ m]

/-- `IsUnramified` passes to a `G`-equivariant sub-object (an injective equivariant map). -/
theorem IsUnramified.of_injective (hM : IsUnramified I M) {f : N → M}
    (hf : Function.Injective f) (hf_smul : ∀ (σ : G) (n : N), f (σ • n) = σ • f n) :
    IsUnramified I N := by
  intro σ hσ n
  apply hf
  rw [hf_smul, hM σ hσ (f n)]

end Hom

section Prod

variable {M N : Type*} [SMul G M] [SMul G N]

/-- A product of two unramified modules is unramified. -/
theorem IsUnramified.prod (hM : IsUnramified I M) (hN : IsUnramified I N) :
    IsUnramified I (M × N) := by
  intro σ hσ mn
  refine Prod.ext ?_ ?_
  · rw [Prod.smul_fst]; exact hM σ hσ mn.1
  · rw [Prod.smul_snd]; exact hN σ hσ mn.2

end Prod

section Pi

variable {ι : Type*} {M : ι → Type*} [∀ i, SMul G (M i)]

/-- A product of a family of unramified modules is unramified. -/
theorem IsUnramified.pi (h : ∀ i, IsUnramified I (M i)) :
    IsUnramified I (∀ i, M i) := by
  intro σ hσ f
  funext i
  exact h i σ hσ (f i)

end Pi

section Lattice

variable {M : Type*}

/-- If the inertia subgroup gets smaller, unramifiedness is preserved. -/
theorem IsUnramified.mono [SMul G M] {I J : Subgroup G} (h : I ≤ J)
    (hJ : IsUnramified J M) : IsUnramified I M :=
  fun σ hσ m => hJ σ (h hσ) m

/-- With the trivial inertia subgroup, every module is unramified. -/
theorem isUnramified_bot [MulAction G M] : IsUnramified (⊥ : Subgroup G) M := by
  intro σ hσ m
  rw [Subgroup.mem_bot.mp hσ, one_smul]

/-- A subsingleton (e.g. the zero module) is unramified for any inertia subgroup. -/
theorem isUnramified_of_subsingleton [SMul G M] [Subsingleton M] :
    IsUnramified I M :=
  fun _ _ _ => Subsingleton.elim _ _

end Lattice

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A `Gal(L/K)`-module `M` is **unramified at the valuation subring `A`** if the
inertia subgroup `A.inertiaSubgroup K` acts trivially on `M`.

This is the shape in which the notion is applied to elliptic curves: `M` is the
ℓ-adic Tate module `T_ℓ E` with its Galois action, and being unramified here is one
of the equivalent conditions in the Néron–Ogg–Shafarevich criterion. -/
noncomputable abbrev IsUnramifiedAt (A : ValuationSubring L)
    (M : Type*) [MulAction (L ≃ₐ[K] L) M] : Prop :=
  IsUnramified (A.inertiaSubgroup K) M

end ValuationSubring
