/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.SubcomplexOp

/-!
# The type of nondegenerate simplices not in a subcomplex

In this file, given a subcomplex `A` of a simplicial set `X`,
we introduce the type `A.N` of nondegenerate simplices of `X`
that are not in `A`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The type of nondegenerate simplices which do not belong to
a given subcomplex of a simplicial set. -/
structure N extends X.N where mk' ::
  notMem : simplex ∉ A.obj _

namespace N

variable {A}

/--
@isnad1 id=ex.0h3v.s7.3f8d4bb674d6 from=seed src=0 shape=7210bbb3 vocab=7006a0f1
-/
lemma mk'_surjective (s : A.N) :
    ∃ (t : X.N) (ht : t.simplex ∉ A.obj _), s = mk' t ht :=
  ⟨s.toN, s.notMem, rfl⟩

/-- Constructor for the type of nondegenerate simplices which
do not belong to a given subcomplex of a simplicial set. -/
@[simps!]
def mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
    (hx' : x ∉ A.obj _) : A.N where
  simplex := x
  nonDegenerate := hx
  notMem := hx'

/-- A unification hint for the dimension of `Subcomplex.N.mk`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (n : ℕ) (x : X _⦋n⦌)
    (hx : x ∈ X.nonDegenerate n) (hx' : x ∉ A.obj _) where
  ⊢ (mk x hx hx').dim ≟ n

/--
@isnad1 id=ex.0h3v.s8.83decd6d4c45 from=seed src=0 shape=ac220cf7 vocab=99c4bcba
-/
lemma mk_surjective (s : A.N) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
      (hx' : x ∉ A.obj _), s = mk x hx hx' :=
  ⟨s.dim, s.simplex, s.nonDegenerate, s.notMem, rfl⟩

/--
@isnad1 id=iff.0h4v.s4.e0baf1023faf from=seed src=0 shape=a88e8f85 vocab=d8c7ac1b
-/
lemma ext_iff (x y : A.N) :
    x = y ↔ x.toN = y.toN := by
  grind [cases SSet.Subcomplex.N]

variable (A) in
/--
@isnad1 id=var.0h6v.s5.d192f009777f from=seed src=0 shape=91b24ac0 vocab=5bfb6a64
-/
@[elab_as_elim]
lemma cases {motive : X.N → Prop}
    (mem : ∀ (s : X.N), s.subcomplex ≤ A → motive s)
    (notMem : ∀ (s : A.N), motive s.toN)
    (s : X.N) :
    motive s := by
  by_cases hs : s.subcomplex ≤ A
  · exact mem s hs
  · exact notMem (.mk' s (by simpa using hs))

lemma eq_iff_sMk_eq {X : SSet.{u}} {A : X.Subcomplex} (x y : A.N) :
    x = y ↔ S.mk x.simplex = S.mk y.simplex := by
  rw [N.ext_iff, SSet.N.ext_iff]

instance : PartialOrder A.N :=
  PartialOrder.lift toN (fun _ _ ↦ by simp [ext_iff])

/--
@isnad1 id=iff.0h4v.s5.9243f8b82911 from=seed src=0 shape=a88e8f85 vocab=480d2a75
-/
lemma le_iff {x y : A.N} : x ≤ y ↔ x.toN ≤ y.toN :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s5.aeae52e512c4 from=seed src=0 shape=a88e8f85 vocab=b6a49770
-/
lemma lt_iff {x y : A.N} : x < y ↔ x.toN < y.toN :=
  Iff.rfl

section

variable (s : A.N) {d : ℕ} (hd : s.dim = d)

/-- When `A` is a subcomplex of a simplicial set `X`,
and `s : A.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
abbrev cast : A.N where
  toN := s.toN.cast hd
  notMem := hd ▸ s.notMem

/--
@isnad1 id=eq.1h4v.s5.c9204f892aef from=seed src=0 shape=6c46f8d1 vocab=1302b3d2
-/
lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

/-- A unification hint for the dimension of `Subcomplex.N.cast`. -/
unif_hint {X : SSet.{u}} {A : X.Subcomplex} (s : A.N) (d : ℕ)
    (hd : s.dim = d) where
  ⊢ (s.cast hd).dim ≟ d

/-- The bijection `A.op.N ≃ A.N` for a subcomplex `A` of a simplicial set.. -/
@[simps -isSimp apply symm_apply]
def opEquiv : A.op.N ≃o A.N where
  toFun x := N.mk' (SSet.N.opEquiv x.toN) x.notMem
  invFun y := N.mk' (SSet.N.opEquiv.symm y.toN) y.notMem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := SSet.N.opEquiv.map_rel_iff

/-- The bijection `A.N ≃ B.N` on nondegenerate simplices not belonging
to a certain subcomplex that is induced by an isomorphism `X ≅ Y` of
simplicial sets which maps `A : X.Subcomplex` to `B : Y.Subcomplex`. -/
@[simps -isSimp apply symm_apply]
def orderIsoOfIso {Y : SSet.{u}} {B : Y.Subcomplex} (e : X ≅ Y)
    (hA : B.preimage e.hom = A) : A.N ≃o B.N where
  toFun x := N.mk' (SSet.N.orderIsoOfIso e x.toN) (by subst hA; exact x.notMem)
  invFun y := N.mk' ((SSet.N.orderIsoOfIso e).symm y.toN) (by
    obtain rfl : A.preimage e.inv = B := by aesop
    exact y.notMem)
  left_inv _ := by aesop
  right_inv _ := by aesop
  map_rel_iff' {_ _} := (SSet.N.orderIsoOfIso e).map_rel_iff'

end N

/--
@isnad1 id=ex.1h4v.s8.9d7c7d0bfe12 from=seed src=0 shape=7c26c3f3 vocab=5839a8d4
-/
lemma existsN {X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌) {A : X.Subcomplex}
    (hs : s ∉ A.obj _) :
    ∃ (x : A.N) (f : ⦋n⦌ ⟶ ⦋x.dim⦌), Epi f ∧ X.map f.op x.simplex = s := by
  refine ⟨⟨(S.mk s).toN, fun h ↦ hs ?_⟩, ⟨(S.mk s).toNπ, inferInstance, S.map_toNπ_op_apply _⟩⟩
  simp only [← ofSimplex_le_iff] at h ⊢
  simpa using h

end SSet.Subcomplex
