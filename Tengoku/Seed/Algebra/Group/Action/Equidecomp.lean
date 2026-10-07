/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Action.Defs
public import Tengoku.Seed.Logic.Equiv.PartialEquiv
public import Tengoku.Seed.Algebra.Group.Pointwise.Finset.Basic

/-!
# Equidecompositions

This file develops the basic theory of equidecompositions.

## Main Definitions

Let `G` be a group acting on a space `X`, and `A B : Set X`.

An *equidecomposition* of `A` and `B` is typically defined as a finite partition of `A` together
with a finite list of elements of `G` of the same size such that applying each element to the
matching piece of the partition yields a partition of `B`.

This yields a bijection `f : A ≃ B` where, given `a : A`, `f a = γ • a` for `γ : G` the group
element for `a`'s piece of the partition. Reversing this is easy, and so we get an equivalent
(up to the choice of group elements) definition: an *Equidecomposition* of `A` and `B` is a
bijection `f : A ≃ B` such that for some `S : Finset G`, `f a ∈ S • a` for all `a`.

We take this as our definition as it is easier to work with. It is implemented as an element
`PartialEquiv X X` with source `A` and target `B`.

## Implementation Notes

* Equidecompositions are implemented as elements of `PartialEquiv X X` together with a
  `Finset` of elements of the acting group and a proof that every point in the source is moved
  by an element in the finset.

* The requirement that `G` be a group is relaxed where possible.

* We introduce a non-standard predicate, `IsDecompOn`, to state that a function satisfies the main
  combinatorial property of equidecompositions, even if it is not injective or surjective.

## TODO

* Prove that if two sets equidecompose into subsets of each other, they are equidecomposable
  (Schroeder-Bernstein type theorem)
* Define equidecomposability into subsets as a preorder on sets and
  prove that its induced equivalence relation is equidecomposability.
* Prove the definition of equidecomposition used here is equivalent to the more familiar one
  using partitions.

-/

@[expose] public section

variable {X G : Type*} {A B : Set X}

open Function Set Pointwise PartialEquiv

namespace Equidecomp

section SMul

variable [SMul G X]

/-- Let `G` act on a space `X` and `A : Set X`. We say `f : X → X` is a decomposition on `A`
as witnessed by some `S : Finset G` if for all `a ∈ A`, the value `f a` can be obtained
by applying some element of `S` to `a` instead.

More familiarly, the restriction of `f` to `A` is the result of partitioning `A` into finitely many
pieces, then applying a single element of `G` to each piece. -/
def IsDecompOn (f : X → X) (A : Set X) (S : Finset G) : Prop := ∀ a ∈ A, ∃ g ∈ S, f a = g • a

variable (X G)

/-- Let `G` act on a space `X`. An `Equidecomposition` with respect to `X` and `G` is a partial
bijection `f : PartialEquiv X X` with the property that for some set `elements : Finset G`,
(which we record), for each `a ∈ f.source`, `f a` can be obtained by applying some `g ∈ elements`
instead. We call `f` an equidecomposition of `f.source` with `f.target`.

More familiarly, `f` is the result of partitioning `f.source` into finitely many pieces,
then applying a single element of `G` to each to get a partition of `f.target`.
-/
structure _root_.Equidecomp extends PartialEquiv X X where
  isDecompOn' : ∃ S : Finset G, IsDecompOn toFun source S

variable {X G}

/-- Note that `Equidecomp X G` is not `FunLike`. -/
instance : CoeFun (Equidecomp X G) fun _ => X → X := ⟨fun f => f.toFun⟩

/-- A finite set of group elements witnessing that `f` is an equidecomposition. -/
noncomputable
def witness (f : Equidecomp X G) : Finset G := f.isDecompOn'.choose

/--
@isnad1 id=isdecomp.0h3v.s5.fc7da925b14f from=seed src=0 shape=6bbcb8d5 vocab=cd493863
-/
theorem isDecompOn (f : Equidecomp X G) : IsDecompOn f f.source f.witness :=
  f.isDecompOn'.choose_spec

/--
@isnad1 id=mem.1h4v.s5.bb74cac21540 from=seed src=0 shape=d14cc467 vocab=f73914d0
-/
theorem apply_mem_target {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f x ∈ f.target := by simp [h]

/--
@isnad1 id=injectiv.0h2v.s4.bdfe481cb81c from=seed src=0 shape=59ac6c86 vocab=3bafb970
-/
theorem toPartialEquiv_injective : Injective <| toPartialEquiv (X := X) (G := G) := by
  intro ⟨_, _, _⟩ _ _
  congr

/--
@isnad1 id=isdecomp.3h7v.s5.94bff89466b0 from=seed src=0 shape=aeb8195d vocab=2c829384
-/
theorem IsDecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
    (hA' : A' ⊆ A) (hf' : EqOn f f' A') : IsDecompOn f' A' S := by
  intro a ha
  rw [← hf' ha]
  exact h a (hA' ha)

/-- The restriction of an equidecomposition as an equidecomposition. -/
@[simps!]
def restr (f : Equidecomp X G) (A : Set X) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.restr A
  isDecompOn' := ⟨f.witness,
    f.isDecompOn.mono (source_restr_subset_source _ _) fun _ ↦ congrFun rfl⟩

/--
@isnad1 id=eq.0h4v.s5.377977b5cb9c from=seed src=0 shape=d1ee3e64 vocab=b6120c71
-/
@[simp]
theorem toPartialEquiv_restr (f : Equidecomp X G) (A : Set X) :
    (f.restr A).toPartialEquiv = f.toPartialEquiv.restr A := rfl

/--
@isnad1 id=eq.1h4v.s5.d19935706afd from=seed src=0 shape=2de99ae2 vocab=ab92f437
-/
theorem source_restr (f : Equidecomp X G) {A : Set X} (hA : A ⊆ f.source) :
    (f.restr A).source = A := by rw [restr_source, inter_eq_self_of_subset_right hA]

/--
@isnad1 id=eq.1h4v.s5.6ff3260328e7 from=seed src=0 shape=4b45ccfa vocab=ab92f437
-/
theorem restr_of_source_subset {f : Equidecomp X G} {A : Set X} (hA : f.source ⊆ A) :
    f.restr A = f := by
  apply toPartialEquiv_injective
  rw [toPartialEquiv_restr, PartialEquiv.restr_eq_of_source_subset hA]

/--
@isnad1 id=eq.0h3v.s4.ec80ca6af5bd from=seed src=0 shape=d1e6f9a6 vocab=474d23ec
-/
@[simp]
theorem restr_univ (f : Equidecomp X G) : f.restr univ = f :=
  restr_of_source_subset <| subset_univ _

end SMul

section Monoid

variable [Monoid G] [MulAction G X]

variable (X G)

/-- The identity function is an equidecomposition of the space with itself. -/
@[simps toPartialEquiv]
def refl : Equidecomp X G where
  toPartialEquiv := .refl _
  isDecompOn' := ⟨{1}, by simp [IsDecompOn]⟩

variable {X} {G}

open scoped Classical in
/--
@isnad1 id=isdecomp.2h8v.s7.2ddd9567c9c0 from=seed src=0 shape=e7d9a3d8 vocab=a230f902
-/
theorem IsDecompOn.comp' {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) :
    IsDecompOn (g ∘ f) (A ∩ f ⁻¹' B) (T * S) := by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

open scoped Classical in
/--
@isnad1 id=isdecomp.3h8v.s6.0f4a9f2a269e from=seed src=0 shape=f5204f06 vocab=0c377990
-/
theorem IsDecompOn.comp {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : IsDecompOn g B T) (hf : IsDecompOn f A S) (h : MapsTo f A B) :
    IsDecompOn (g ∘ f) A (T * S) := by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

/-- The composition of two equidecompositions as an equidecomposition. -/
@[simps toPartialEquiv, trans]
noncomputable def trans (f g : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.trans g.toPartialEquiv
  isDecompOn' := by classical exact ⟨g.witness * f.witness, g.isDecompOn.comp' f.isDecompOn⟩

end Monoid

section Group

variable [Group G] [MulAction G X]

open scoped Classical in
/--
@isnad1 id=isdecomp.2h6v.s6.fa1500abb817 from=seed src=0 shape=b4fc02a9 vocab=2c30f26a
-/
theorem IsDecompOn.of_leftInvOn {f g : X → X} {A : Set X} {S : Finset G}
    (hf : IsDecompOn f A S) (h : LeftInvOn g f A) : IsDecompOn g (f '' A) S⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ, inv_smul_smul, ← hγ, h ha]

/-- The inverse function of an equidecomposition as an equidecomposition. -/
@[symm, simps toPartialEquiv]
noncomputable def symm (f : Equidecomp X G) : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.symm
  isDecompOn' := by classical exact ⟨f.witness⁻¹, by
    convert! f.isDecompOn.of_leftInvOn f.leftInvOn
    rw [image_source_eq_target, symm_source]⟩

/--
@isnad1 id=mem.1h4v.s7.bd57ca80cbd7 from=seed src=0 shape=b82531fd vocab=46fd101f
-/
theorem map_target {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f.symm x ∈ f.source := f.toPartialEquiv.map_target h

/--
@isnad1 id=eq.1h4v.s7.7e10dac21426 from=seed src=0 shape=48c16eff vocab=def88e16
-/
theorem left_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f.toPartialEquiv.symm (f x) = x := by simp [h]

/--
@isnad1 id=eq.1h4v.s7.9265b208cab5 from=seed src=0 shape=a8da53ad vocab=ec98a003
-/
theorem right_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f (f.toPartialEquiv.symm x) = x := by simp [h]

/--
@isnad1 id=eq.0h3v.s6.51dacf6d1fa8 from=seed src=0 shape=2acdac3f vocab=7e7bf306
-/
@[simp]
theorem symm_symm (f : Equidecomp X G) : f.symm.symm = f := rfl

/--
@isnad1 id=iff.2h5v.s7.5dee1b1a60ff from=seed src=0 shape=5901a814 vocab=46fd101f
-/
theorem symm_apply_eq (f : Equidecomp X G) {x y} (hx : x ∈ f.toPartialEquiv.target)
    (hy : y ∈ f.toPartialEquiv.source) : f.symm x = y ↔ x = f y :=
  f.toPartialEquiv.symm_apply_eq hy hx

theorem eq_symm_apply (f : Equidecomp X G) {x y} (hx : x ∈ f.toPartialEquiv.target)
    (hy : y ∈ f.toPartialEquiv.source) : y = f.symm x ↔ f y = x :=
  f.toPartialEquiv.eq_symm_apply hy hx

/--
@isnad1 id=involuti.0h2v.s5.be97adbd5f55 from=seed src=0 shape=13c55453 vocab=a216ace7
-/
theorem symm_involutive : Function.Involutive (symm : Equidecomp X G → _) := symm_symm

/--
@isnad1 id=bijectiv.0h2v.s6.d1fd1d3786d3 from=seed src=0 shape=2d59515c vocab=899b3cac
-/
theorem symm_bijective : Function.Bijective (symm : Equidecomp X G → _) := symm_involutive.bijective

/--
@isnad1 id=eq.0h2v.s5.8dc0cbec0c81 from=seed src=0 shape=8a3f3ba9 vocab=511385e0
-/
@[simp]
theorem refl_symm : (refl X G).symm = refl X G := rfl

/--
@isnad1 id=eq.0h3v.s6.9bffc6b0deda from=seed src=0 shape=8a2a9940 vocab=ff3e759e
-/
@[simp]
theorem restr_refl_symm (A : Set X) :
    ((Equidecomp.refl X G).restr A).symm = (Equidecomp.refl X G).restr A := rfl

end Group

end Equidecomp
