/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.Seed.GroupTheory.Index
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal-unit filtrations

This file provides a theorem API for antitone principal-unit filtrations used by
ramification and norm arguments.
-/

namespace LocalFieldTheory

universe u v

open scoped BigOperators

namespace DiscreteValuationField

/-- A generic antitone filtration by subgroups of a group.  No valued-field
semantics are asserted by this interface alone.-/
structure AntitoneSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each natural-number filtration level.-/
  subgroup : ℕ → Subgroup G
  /-- Higher filtration levels are contained in lower ones.-/
  antitone : ∀ {m n : ℕ}, m ≤ n → subgroup n ≤ subgroup m

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The `n`-th principal-unit subgroup.-/
def principalUnitSubgroup (n : ℕ) : Subgroup G :=
  U.subgroup n

/-- Characterizes `x ∈ U.principalUnitSubgroup n` by the equivalent condition `x ∈ U.subgroup n`.
@isnad1 id=iff.0h4v.s5.8e5799f2a3be from=translated src=- shape=c4300b8e vocab=6877f635
-/
@[simp] theorem mem_principalUnitSubgroup_iff (n : ℕ) (x : G) :
    x ∈ U.principalUnitSubgroup n ↔ x ∈ U.subgroup n :=
  Iff.rfl

/-- Higher filtration levels are contained in lower levels.
@isnad1 id=le.1h4v.s5.55db408dfc13 from=translated src=- shape=3807b0d9 vocab=36f41021
-/
theorem principalUnitSubgroup_antitone {m n : ℕ} (h : m ≤ n) :
    U.principalUnitSubgroup n ≤ U.principalUnitSubgroup m :=
  U.antitone h

/-- Establishes the membership statement `x ∈ U.principalUnitSubgroup m`.
@isnad1 id=mem.2h5v.s5.0ee51ac1156b from=translated src=- shape=fd6deaa9 vocab=f0ae03a5
-/
theorem mem_of_mem_of_le {m n : ℕ} (h : m ≤ n) {x : G}
    (hx : x ∈ U.principalUnitSubgroup n) :
    x ∈ U.principalUnitSubgroup m :=
  U.principalUnitSubgroup_antitone h hx

/-- The natural map from a finer filtration quotient to a coarser filtration
quotient.  If `m ≤ n`, then `U^n ≤ U^m`, so quotienting by `U^n` maps to
quotienting by `U^m`.-/
def quotient_principalUnitSubgroup_mapOfLe {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    G ⧸ U.principalUnitSubgroup n →*
      G ⧸ U.principalUnitSubgroup m :=
  QuotientGroup.map (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
    (MonoidHom.id G) (by
      intro x hx
      exact U.mem_of_mem_of_le hmn hx)

/--
The defining evaluation formula for `quotient_principalUnitSubgroup_mapOfLe` is
`U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk x) = QuotientGroup.mk x`.
@isnad1 id=eq.1h5v.s8.21ea0aace4c1 from=translated src=- shape=f428d0f7 vocab=55c98067
-/
@[simp] theorem quotient_principalUnitSubgroup_mapOfLe_apply_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk x) =
      QuotientGroup.mk x :=
  rfl

/--
Establishes the identity `U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk'
(U.principalUnitSubgroup n) x) = QuotientGroup.mk' (U.principalUnitSubgroup m) x`.
@isnad1 id=eq.1h5v.s9.5a4d872363c8 from=translated src=- shape=baae3d99 vocab=fe6e4e05
-/
@[simp] theorem quotient_principalUnitSubgroup_mapOfLe_apply_mk'
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn
        (QuotientGroup.mk' (U.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x :=
  rfl

/-- The class of `U^m` inside `G ⧸ U^n`.  For `m ≤ n`, this is the kernel of
the natural map `G ⧸ U^n →* G ⧸ U^m`.-/
def principalUnitSubgroupClassInQuotient (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal] :
    Subgroup (G ⧸ U.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n))
    (U.principalUnitSubgroup m)

/-- The subgroup appearing in `(U.principalUnitSubgroupClassInQuotient m n).Normal` is normal.
@isnad1 id=normal.0h4v.s5.2a775c2a5381 from=translated src=- shape=6409fa5f vocab=525b9957
-/
instance principalUnitSubgroupClassInQuotient_normal
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitSubgroupClassInQuotient m n).Normal := by
  dsimp [principalUnitSubgroupClassInQuotient]
  infer_instance

/--
Characterizes `q ∈ U.principalUnitSubgroupClassInQuotient m n` by the equivalent condition `∃ x :
G, x ∈ U.principalUnitSubgroup m ∧ QuotientGroup.mk' (U.principalUnitSubgroup n) x = q`.
@isnad1 id=iff.0h5v.s8.757e333016fb from=translated src=- shape=b44a4bf5 vocab=1e4ca450
-/
theorem mem_principalUnitSubgroupClassInQuotient_iff
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    (q : G ⧸ U.principalUnitSubgroup n) :
    q ∈ U.principalUnitSubgroupClassInQuotient m n ↔
      ∃ x : G, x ∈ U.principalUnitSubgroup m ∧
        QuotientGroup.mk' (U.principalUnitSubgroup n) x = q :=
  Iff.rfl

/--
Establishes the membership statement `QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
U.principalUnitSubgroupClassInQuotient m n`.
@isnad1 id=mem.1h5v.s8.39ab4182e473 from=translated src=- shape=e9f55762 vocab=1e4ca450
-/
theorem principalUnitSubgroupClassInQuotient_mk_mem
    {m n : ℕ} [(U.principalUnitSubgroup n).Normal] {x : G}
    (hx : x ∈ U.principalUnitSubgroup m) :
    QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
      U.principalUnitSubgroupClassInQuotient m n :=
  Subgroup.mem_map_of_mem
    (QuotientGroup.mk' (U.principalUnitSubgroup n)) hx

/-- The subquotient `U^m/U^n` of a principal-unit filtration.  Under
`m ≤ n`, antitonicity makes this the usual quotient of `U^m` by `U^n`.-/
def principalUnitSubquotient (m n : ℕ) : Type u :=
  U.principalUnitSubgroup m ⧸
    (U.principalUnitSubgroup n).subgroupOf (U.principalUnitSubgroup m)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitSubquotient
m n)`.-/
instance principalUnitSubquotientGroup
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    Group (U.principalUnitSubquotient m n) := by
  change Group
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  infer_instance

/-- Explicit access to the concrete quotient representation.-/
def principalUnitSubquotientConcreteEquiv
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) := by
  change
    (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m))
  exact MulEquiv.refl _

/-- A subquotient of a commutative principal-unit filtration retains the
commutative group structure of its concrete quotient representation.-/
instance principalUnitSubquotientCommGroup
    {H : Type u} [CommGroup H] (V : AntitoneSubgroupFiltration H)
    (m n : ℕ) [(V.principalUnitSubgroup n).Normal] :
    CommGroup (V.principalUnitSubquotient m n) :=
  { (inferInstance : Group (V.principalUnitSubquotient m n)) with
    mul_comm := fun x y => by
      apply (V.principalUnitSubquotientConcreteEquiv m n).injective
      simp only [map_mul]
      exact mul_comm _ _ }

/-- The canonical class map `U^m → U^m/U^n`.-/
def principalUnitSubquotientMk
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubgroup m →* U.principalUnitSubquotient m n := by
  change U.principalUnitSubgroup m →*
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  exact QuotientGroup.mk'
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m))

/--
Establishes the identity `U.principalUnitSubquotientConcreteEquiv m n
(U.principalUnitSubquotientMk m n x) = QuotientGroup.mk x`.
@isnad1 id=eq.0h5v.s11.d383adbec9de from=translated src=- shape=2a6ae579 vocab=6cc108f5
-/
@[simp]
theorem principalUnitSubquotientConcreteEquiv_mk
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientConcreteEquiv m n
        (U.principalUnitSubquotientMk m n x) =
      QuotientGroup.mk x :=
  rfl

/-- The specified map is surjective: `Function.Surjective (U.principalUnitSubquotientMk m n)`.
@isnad1 id=surjecti.0h4v.s8.780b5a41c907 from=translated src=- shape=d60a0a61 vocab=ad8ab0c9
-/
theorem principalUnitSubquotientMk_surjective
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    Function.Surjective (U.principalUnitSubquotientMk m n) :=
  QuotientGroup.mk'_surjective
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m))

/-- Eliminate a principal-unit subquotient through its canonical map.
@isnad1 id=var.0h7v.s8.eef7edd9db21 from=translated src=- shape=56468630 vocab=d8c191a7
-/
protected theorem principalUnitSubquotient.inductionOn
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    {motive : U.principalUnitSubquotient m n → Prop}
    (q : U.principalUnitSubquotient m n)
    (h : ∀ x : U.principalUnitSubgroup m,
      motive (U.principalUnitSubquotientMk m n x)) :
    motive q := by
  change motive
    (show U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m) from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- Descend a homomorphism that kills `U^n` inside `U^m`.-/
def principalUnitSubquotientLift
    {H : Type*} [Group H] (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal]
    (f : U.principalUnitSubgroup m →* H)
    (h : (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m) ≤ f.ker) :
    U.principalUnitSubquotient m n →* H := by
  change
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m)) →* H
  exact QuotientGroup.lift
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)) f h

/--
Establishes the identity `U.principalUnitSubquotientLift m n f h (U.principalUnitSubquotientMk m n
x) = f x`.
@isnad1 id=eq.1h7v.s10.7b81a3e8ca81 from=translated src=- shape=b3788566 vocab=5acc3957
-/
@[simp]
theorem principalUnitSubquotientLift_mk
    {H : Type*} [Group H] (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal]
    (f : U.principalUnitSubgroup m →* H)
    (h : (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m) ≤ f.ker)
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientLift m n f h
        (U.principalUnitSubquotientMk m n x) = f x :=
  rfl

/-- The principal-unit graded piece `U^n/U^{n+1}`.-/
def principalUnitGradedPiece (n : ℕ) : Type u :=
  U.principalUnitSubquotient n (n + 1)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitGradedPiece
n)`.-/
instance principalUnitGradedPieceGroup
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    Group (U.principalUnitGradedPiece n) := by
  change Group (U.principalUnitSubquotient n (n + 1))
  infer_instance

/-- The canonical class map into the adjacent graded piece.-/
def principalUnitGradedPieceMk
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    U.principalUnitSubgroup n →* U.principalUnitGradedPiece n := by
  change U.principalUnitSubgroup n →*
    U.principalUnitSubquotient n (n + 1)
  exact U.principalUnitSubquotientMk n (n + 1)

/-- Explicit identification of a graded piece with its named adjacent
subquotient.-/
def principalUnitGradedPieceEquivSubquotient
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    U.principalUnitGradedPiece n ≃*
      U.principalUnitSubquotient n (n + 1) := by
  change U.principalUnitSubquotient n (n + 1) ≃*
    U.principalUnitSubquotient n (n + 1)
  exact MulEquiv.refl _

/-- Representative criterion for the identity in `U^m/U^n`.
@isnad1 id=iff.0h5v.s9.84e28ddfc695 from=translated src=- shape=882df821 vocab=2b7cfba9
-/
theorem principalUnitSubquotient_mk_eq_one_iff
    {m n : ℕ} [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientMk m n x = 1 ↔
      (x : G) ∈ U.principalUnitSubgroup n := by
  change (QuotientGroup.mk x :
      U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) =
    1 ↔ x ∈ (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)
  exact QuotientGroup.eq_one_iff
    (N := (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)) x

/-- The map from `U^m` into `G/U^n`.-/
def principalUnitSubgroupToQuotient {m n : ℕ} (_hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubgroup m →* G ⧸ U.principalUnitSubgroup n :=
  (QuotientGroup.mk' (U.principalUnitSubgroup n)).comp
    (U.principalUnitSubgroup m).subtype

/--
The defining evaluation formula for `principalUnitSubgroupToQuotient` is
`U.principalUnitSubgroupToQuotient hmn x = QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G)`.
@isnad1 id=eq.1h5v.s9.4fd24b4d4c99 from=translated src=- shape=1160a621 vocab=4076b489
-/
@[simp] theorem principalUnitSubgroupToQuotient_apply
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubgroupToQuotient hmn x =
      QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) :=
  rfl

/-- The kernel of `U^m → G/U^n` is `U^n` inside `U^m`.
@isnad1 id=eq.1h4v.s7.7ce7d830af6d from=translated src=- shape=ae3debdd vocab=fd5be19c
-/
theorem principalUnitSubgroupToQuotient_ker_eq
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupToQuotient hmn).ker =
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [principalUnitSubgroupToQuotient_apply, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq_one_iff (N := U.principalUnitSubgroup n) (x : G)

/-- The range of `U^m → G/U^n` is the class of `U^m` in `G/U^n`.
@isnad1 id=eq.1h4v.s6.5ad9cfbc82ee from=translated src=- shape=818191ec vocab=04468abf
-/
theorem principalUnitSubgroupToQuotient_range_eq_classInQuotient
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupToQuotient hmn).range =
      U.principalUnitSubgroupClassInQuotient m n := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : G), x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The subquotient `U^m/U^n` as the class of `U^m` inside `G/U^n`.-/
noncomputable def principalUnitSubquotientEquivClassInQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      U.principalUnitSubgroupClassInQuotient m n :=
  (U.principalUnitSubquotientConcreteEquiv m n).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (U.principalUnitSubgroupToQuotient_ker_eq hmn).symm).trans
      ((QuotientGroup.quotientKerEquivRange
        (U.principalUnitSubgroupToQuotient hmn)).trans
          (MulEquiv.subgroupCongr
            (U.principalUnitSubgroupToQuotient_range_eq_classInQuotient hmn))))

/--
Establishes the identity `((U.principalUnitSubquotientEquivClassInQuotientOfLe hmn
(U.principalUnitSubquotientMk m n x) : U.principalUnitSubgroupClassInQuotient m n) : G ⧸
U.principalUnitSubgroup n) = QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G)`.
@isnad1 id=eq.1h5v.s10.42aaf9d01c60 from=translated src=- shape=a31bf365 vocab=85b64d3a
-/
@[simp] theorem coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    ((U.principalUnitSubquotientEquivClassInQuotientOfLe hmn
        (U.principalUnitSubquotientMk m n x) :
      U.principalUnitSubgroupClassInQuotient m n) :
      G ⧸ U.principalUnitSubgroup n) =
      QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) := by
  simp [principalUnitSubquotientEquivClassInQuotientOfLe]
  rfl

/-- The graded piece `U^n/U^{n+1}` as the class of `U^n` inside
`G/U^{n+1}`.-/
noncomputable def principalUnitGradedPieceEquivClassInQuotient
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    U.principalUnitGradedPiece n ≃*
      U.principalUnitSubgroupClassInQuotient n (n + 1) :=
  (U.principalUnitGradedPieceEquivSubquotient n).trans
    (U.principalUnitSubquotientEquivClassInQuotientOfLe (Nat.le_succ n))

/--
Establishes the identity `((U.principalUnitGradedPieceEquivClassInQuotient n
(U.principalUnitGradedPieceMk n x) : U.principalUnitSubgroupClassInQuotient n (n + 1)) : G ⧸
U.principalUnitSubgroup (n + 1)) = QuotientGroup.mk' (U.principalUnitSubgroup (n + 1)) (x : G)`.
@isnad1 id=eq.0h4v.s11.0931f88bbb59 from=translated src=- shape=92dbdc14 vocab=02d9d4ac
-/
@[simp] theorem coe_principalUnitGradedPieceEquivClassInQuotient_mk
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal]
    (x : U.principalUnitSubgroup n) :
    ((U.principalUnitGradedPieceEquivClassInQuotient n
        (U.principalUnitGradedPieceMk n x) :
      U.principalUnitSubgroupClassInQuotient n (n + 1)) :
      G ⧸ U.principalUnitSubgroup (n + 1)) =
      QuotientGroup.mk' (U.principalUnitSubgroup (n + 1)) (x : G) := by
  exact U.coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk
    (Nat.le_succ n) x

/-- The kernel of `G ⧸ U^n →* G ⧸ U^m` is the image of `U^m` in
`G ⧸ U^n`.
@isnad1 id=eq.1h4v.s7.3a644a18035b from=translated src=- shape=efa11eb6 vocab=111d04fe
-/
theorem quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.quotient_principalUnitSubgroup_mapOfLe hmn).ker =
      U.principalUnitSubgroupClassInQuotient m n := by
  exact (QuotientGroup.ker_map (U.principalUnitSubgroup n)
    (U.principalUnitSubgroup m) (MonoidHom.id G) (by
      intro x hx
      exact U.mem_of_mem_of_le hmn hx)).trans
    (congrArg (Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n)))
      (Subgroup.comap_id (U.principalUnitSubgroup m)))

/-- Level-change maps send the class of `U^l` in `G/U^n` into the class of
`U^l` in `G/U^m`, for `l ≤ m ≤ n`.
@isnad1 id=mem.3h6v.s9.904480f0abe7 from=translated src=- shape=cf24ffc1 vocab=24a0daa8
-/
theorem quotient_principalUnitSubgroup_mapOfLe_mem_classInQuotient
    {l m n : ℕ} (_hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    {q : G ⧸ U.principalUnitSubgroup n}
    (hq : q ∈ U.principalUnitSubgroupClassInQuotient l n) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn q ∈
      U.principalUnitSubgroupClassInQuotient l m := by
  rcases (U.mem_principalUnitSubgroupClassInQuotient_iff l n q).1 hq with
    ⟨x, hx, hxq⟩
  rw [← hxq, U.quotient_principalUnitSubgroup_mapOfLe_apply_mk']
  exact U.principalUnitSubgroupClassInQuotient_mk_mem hx

/-- The level-change map restricted to principal-unit classes:
`U^l/U^n → U^l/U^m`, for `l ≤ m ≤ n`.-/
def principalUnitClassMapOfLe {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    U.principalUnitSubgroupClassInQuotient l n →*
      U.principalUnitSubgroupClassInQuotient l m :=
  ((U.quotient_principalUnitSubgroup_mapOfLe hmn).domRestrict
      (U.principalUnitSubgroupClassInQuotient l n)).codRestrict
    (U.principalUnitSubgroupClassInQuotient l m)
    (by
      intro q
      exact U.quotient_principalUnitSubgroup_mapOfLe_mem_classInQuotient
        hlm hmn q.property)

/--
The defining evaluation formula for `principalUnitClassMapOfLe` is `((U.principalUnitClassMapOfLe
hlm hmn q : U.principalUnitSubgroupClassInQuotient l m) : G ⧸ U.principalUnitSubgroup m) =
U.quotient_principalUnitSubgroup_mapOfLe hmn (q : G ⧸ U.principalUnitSubgroup n)`.
@isnad1 id=eq.2h6v.s11.b2d656f10b1e from=translated src=- shape=494ef09a vocab=b1a4ce6e
-/
@[simp] theorem principalUnitClassMapOfLe_apply {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    (q : U.principalUnitSubgroupClassInQuotient l n) :
    ((U.principalUnitClassMapOfLe hlm hmn q :
      U.principalUnitSubgroupClassInQuotient l m) :
      G ⧸ U.principalUnitSubgroup m) =
      U.quotient_principalUnitSubgroup_mapOfLe hmn
        (q : G ⧸ U.principalUnitSubgroup n) :=
  rfl

/-- The restricted map `U^l/U^n → U^l/U^m` has kernel `U^m/U^n`.
@isnad1 id=eq.2h5v.s9.9d902bff7c47 from=translated src=- shape=70c211c3 vocab=7a2d011e
-/
theorem principalUnitClassMapOfLe_ker_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitClassMapOfLe hlm hmn).ker =
      (U.principalUnitSubgroupClassInQuotient m n).subgroupOf
        (U.principalUnitSubgroupClassInQuotient l n) := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hq
    have hq' := congrArg Subtype.val hq
    change
      U.quotient_principalUnitSubgroup_mapOfLe hmn
          (q : G ⧸ U.principalUnitSubgroup n) = 1 at hq'
    rw [← U.quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient hmn,
      MonoidHom.mem_ker]
    exact hq'
  · intro hq
    apply Subtype.ext
    change
      U.quotient_principalUnitSubgroup_mapOfLe hmn
          (q : G ⧸ U.principalUnitSubgroup n) = 1
    rw [← MonoidHom.mem_ker,
      U.quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient hmn]
    exact hq

/-- The restricted map `U^l/U^n → U^l/U^m` is surjective.
@isnad1 id=surjecti.2h5v.s11.249126b1968d from=translated src=- shape=ea590091 vocab=f8c0ff6f
-/
theorem principalUnitClassMapOfLe_surjective {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    Function.Surjective (U.principalUnitClassMapOfLe hlm hmn) := by
  intro q
  rcases q with ⟨q, hq⟩
  rcases (U.mem_principalUnitSubgroupClassInQuotient_iff l m q).1 hq with
    ⟨x, hx, hxq⟩
  refine ⟨⟨QuotientGroup.mk' (U.principalUnitSubgroup n) x,
    U.principalUnitSubgroupClassInQuotient_mk_mem hx⟩, ?_⟩
  apply Subtype.ext
  rw [U.principalUnitClassMapOfLe_apply, U.quotient_principalUnitSubgroup_mapOfLe_apply_mk']
  exact hxq

/-- First isomorphism theorem inside principal-unit classes:
`(U^l/U^n)/ker(U^l/U^n → U^l/U^m) ≃ U^l/U^m`, for `l ≤ m ≤ n`.
The kernel is identified with `U^m/U^n` by
`principalUnitClassMapOfLe_ker_eq`.-/
noncomputable def principalUnitClassQuotientKerEquivClassOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    U.principalUnitSubgroupClassInQuotient l n ⧸
        (U.principalUnitClassMapOfLe hlm hmn).ker ≃*
      U.principalUnitSubgroupClassInQuotient l m :=
  QuotientGroup.quotientKerEquivOfSurjective
    (U.principalUnitClassMapOfLe hlm hmn)
    (U.principalUnitClassMapOfLe_surjective hlm hmn)

/--
Establishes the identity `U.principalUnitClassQuotientKerEquivClassOfLe hlm hmn (QuotientGroup.mk'
(U.principalUnitClassMapOfLe hlm hmn).ker q) = U.principalUnitClassMapOfLe hlm hmn q`.
@isnad1 id=eq.2h6v.s15.d14c28b404de from=translated src=- shape=0d68f801 vocab=1ae11b65
-/
@[simp] theorem principalUnitClassQuotientKerEquivClassOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    (q : U.principalUnitSubgroupClassInQuotient l n) :
    U.principalUnitClassQuotientKerEquivClassOfLe hlm hmn
        (QuotientGroup.mk' (U.principalUnitClassMapOfLe hlm hmn).ker q) =
      U.principalUnitClassMapOfLe hlm hmn q := by
  exact QuotientGroup.kerLift_mk (U.principalUnitClassMapOfLe hlm hmn) q

/-- The subgroup of `U^l/U^n` represented by `U^m/U^n` is canonically
the class of `U^m` in `G/U^n`.-/
noncomputable def principalUnitClassSubgroupOfEquivClassOfLe {l m n : ℕ}
    (hlm : l ≤ m) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupClassInQuotient m n).subgroupOf
        (U.principalUnitSubgroupClassInQuotient l n) ≃*
      U.principalUnitSubgroupClassInQuotient m n where
  toFun q :=
    ⟨((q : U.principalUnitSubgroupClassInQuotient l n) :
        G ⧸ U.principalUnitSubgroup n), by
      exact q.property⟩
  invFun q :=
    ⟨⟨(q : G ⧸ U.principalUnitSubgroup n), by
        rcases (U.mem_principalUnitSubgroupClassInQuotient_iff m n
            (q : G ⧸ U.principalUnitSubgroup n)).1 q.property with
          ⟨x, hx, hxq⟩
        exact ⟨x, U.mem_of_mem_of_le hlm hx, hxq⟩⟩, by
      change (q : G ⧸ U.principalUnitSubgroup n) ∈
        U.principalUnitSubgroupClassInQuotient m n
      exact q.property⟩
  left_inv q := by
    ext
    rfl
  right_inv q := by
    ext
    rfl
  map_mul' q r := by
    ext
    rfl

/-- Kernel form of `principalUnitClassMapOfLe_ker_eq`, with the kernel
identified as the class `U^m/U^n`.-/
noncomputable def principalUnitClassMapOfLeKerEquivClass {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitClassMapOfLe hlm hmn).ker ≃*
      U.principalUnitSubgroupClassInQuotient m n :=
  (MulEquiv.subgroupCongr
      (U.principalUnitClassMapOfLe_ker_eq hlm hmn)).trans
    (U.principalUnitClassSubgroupOfEquivClassOfLe hlm)

/-- The third-isomorphism equivalence for principal-unit filtration quotients:
`(G / U^n) / (U^m / U^n) ≃ G / U^m` when `m ≤ n`.-/
noncomputable def quotientModuloPrincipalUnitClassEquivQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (G ⧸ U.principalUnitSubgroup n) ⧸
        U.principalUnitSubgroupClassInQuotient m n ≃*
      G ⧸ U.principalUnitSubgroup m :=
  QuotientGroup.quotientQuotientEquivQuotient
    (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
    (U.principalUnitSubgroup_antitone hmn)

/--
Establishes the identity `U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
(QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n) q) =
U.quotient_principalUnitSubgroup_mapOfLe hmn q`.
@isnad1 id=eq.1h5v.s11.8d33f75ef95b from=translated src=- shape=0d33be84 vocab=fbaa46ca
-/
@[simp] theorem quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    (q : G ⧸ U.principalUnitSubgroup n) :
    U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        (QuotientGroup.mk'
          (U.principalUnitSubgroupClassInQuotient m n) q) =
      U.quotient_principalUnitSubgroup_mapOfLe hmn q := by
  change
    QuotientGroup.quotientQuotientEquivQuotientAux
        (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
        (U.principalUnitSubgroup_antitone hmn) q =
      U.quotient_principalUnitSubgroup_mapOfLe hmn q
  exact
    QuotientGroup.quotientQuotientEquivQuotientAux_mk
      (N := U.principalUnitSubgroup n)
      (M := U.principalUnitSubgroup m)
      (h := U.principalUnitSubgroup_antitone hmn) q

/--
Establishes the identity `U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
(QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n) (QuotientGroup.mk'
(U.principalUnitSubgroup n) x)) = QuotientGroup.mk' (U.principalUnitSubgroup m) x`.
@isnad1 id=eq.1h5v.s11.422528f874dc from=translated src=- shape=8fa89483 vocab=7c700751
-/
@[simp] theorem quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        (QuotientGroup.mk'
          (U.principalUnitSubgroupClassInQuotient m n)
          (QuotientGroup.mk' (U.principalUnitSubgroup n) x)) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x := by
  rw [U.quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk hmn,
    U.quotient_principalUnitSubgroup_mapOfLe_apply_mk' hmn x]

/--
Establishes the identity `(U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).symm
(QuotientGroup.mk' (U.principalUnitSubgroup m) x) = QuotientGroup.mk'
(U.principalUnitSubgroupClassInQuotient m n) (QuotientGroup.mk' (U.principalUnitSubgroup n) x)`.
@isnad1 id=eq.1h5v.s11.953f069377ee from=translated src=- shape=e92043e2 vocab=e89f281f
-/
@[simp] theorem quotientModuloPrincipalUnitClassEquivQuotientOfLe_symm_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).symm
        (QuotientGroup.mk' (U.principalUnitSubgroup m) x) =
      QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n)
        (QuotientGroup.mk' (U.principalUnitSubgroup n) x) := by
  apply (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).injective
  calc
    U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        ((U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).symm
          (QuotientGroup.mk' (U.principalUnitSubgroup m) x)) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x := by
        exact (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn).apply_symm_apply _
    _ =
      U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        (QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n)
          (QuotientGroup.mk' (U.principalUnitSubgroup n) x)) := by
        rw [U.quotientModuloPrincipalUnitClassEquivQuotientOfLe_mk_mk hmn x]

end AntitoneSubgroupFiltration

end DiscreteValuationField

end LocalFieldTheory
