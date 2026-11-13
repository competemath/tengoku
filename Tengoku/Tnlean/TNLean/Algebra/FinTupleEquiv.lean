/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.Data.Fintype.Basic
import Tengoku.Seed.Logic.Equiv.Fin.Basic
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equivalences for finite tuples

This file records canonical product coordinates for functions on finite index
types.  It includes right-associated coordinates in lengths three and four,
and equivalences separating the first one or two coordinates from a tuple of
arbitrary remaining length.

## Main definitions

* `finTupleProdEquiv`: splits a tuple of encoded product indices pointwise.
* `finDoubledProdEquiv`: regroups two encoded product indices by their two factors.
* `finThreeArrowEquiv`: identifies a function on `Fin 3` with a right-associated triple.
* `finFourArrowEquiv`: identifies a function on `Fin 4` with a right-associated quadruple.
* `finSuccArrowEquiv`: separates the first coordinate from a finite tuple.
* `finAddTwoArrowEquiv`: separates the first two coordinates.

## Main statements

* `finTupleProdEquiv_apply`: gives the two pointwise component tuples.
* `finDoubledProdEquiv_apply`: gives the regrouped doubled-product coordinate.
* `finDoubledProdEquiv_symm_apply`: gives the inverse coordinate regrouping.
* `finSuccArrowEquiv_apply`: gives the first coordinate and the remaining tuple.
* `finSuccArrowEquiv_symm_apply`: reconstructs a tuple from its first coordinate and tail.
* `finAddTwoArrowEquiv_apply`: gives the first two coordinates and the remaining tuple.
* `finAddTwoArrowEquiv_symm_apply`: reconstructs a tuple from its first two coordinates and tail.
* `finThreeArrowEquiv_apply`: gives the ordered coordinates of the forward map.
* `finThreeArrowEquiv_symm_apply`: gives the ordered coordinates of the inverse map.
* `finFourArrowEquiv_apply`: gives the ordered coordinates of the forward map.
* `finFourArrowEquiv_symm_apply`: gives the ordered coordinates of the inverse map.

## Implementation notes

The fixed-length product coordinates are right-associated and are constructed
recursively from Mathlib's `finTwoArrowEquiv` using `Fin.consEquiv`.  The
variable-length equivalences use `Fin.consEquiv` to separate the prescribed
initial coordinates from the remaining tuple.  Product-valued tuples use
Mathlib's canonical `finProdFinEquiv` at every coordinate.

## Tags

finite tuples, equivalence, product coordinates
-/
namespace Tengoku.Tnlean end Tengoku.Tnlean open Tengoku.Tnlean
/-- Split a finite tuple of canonically encoded product indices into its two
component tuples.-/
def _root_.Tengoku.Tnlean.finTupleProdEquiv (N d e : ℕ) :
    (Fin N → Fin (d * e)) ≃ (Fin N → Fin d) × (Fin N → Fin e) :=
  (Equiv.arrowCongr (Equiv.refl (Fin N)) finProdFinEquiv.symm).trans
    (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ ↦ Fin d) (fun _ ↦ Fin e))

/-- The product-tuple equivalence takes the quotient and remainder component
at every coordinate.
@isnad1 id=eq.0h4v.s7.eda498efc5d9 from=translated src=- shape=fe3cc03d vocab=4d37b9ca
-/
@[simp] theorem _root_.Tengoku.Tnlean.finTupleProdEquiv_apply (N d e : ℕ)
    (σ : Fin N → Fin (d * e)) :
    finTupleProdEquiv N d e σ =
      (fun n ↦ (σ n).divNat, fun n ↦ (σ n).modNat) := by
  rfl

/-- Regroup two encoded product indices by their factors:
`((i, k), (j, l)) ↦ ((i, j), (k, l))`.

All four pairs use the standard finite-product encoding `finProdFinEquiv`.-/
def _root_.Tengoku.Tnlean.finDoubledProdEquiv (d e : ℕ) :
    Fin ((d * e) * (d * e)) ≃ Fin ((d * d) * (e * e)) :=
  finProdFinEquiv.symm |>.trans <|
    (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans <|
      (Equiv.prodProdProdComm (Fin d) (Fin e) (Fin d) (Fin e)).trans <|
        (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

/-- Forward coordinate formula for `finDoubledProdEquiv`.
@isnad1 id=eq.0h6v.s10.5c63dd0c42c4 from=translated src=- shape=4b774220 vocab=1e6cd014
-/
@[simp] theorem _root_.Tengoku.Tnlean.finDoubledProdEquiv_apply {d e : ℕ}
    (i j : Fin d) (k l : Fin e) :
    finDoubledProdEquiv d e
        (finProdFinEquiv (finProdFinEquiv (i, k), finProdFinEquiv (j, l))) =
      finProdFinEquiv (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) := by
  simp [finDoubledProdEquiv]

/-- Inverse coordinate formula for `finDoubledProdEquiv`.
@isnad1 id=eq.0h6v.s10.15028a562fb3 from=translated src=- shape=0504b0dc vocab=9cc702bd
-/
@[simp] theorem _root_.Tengoku.Tnlean.finDoubledProdEquiv_symm_apply {d e : ℕ}
    (i j : Fin d) (k l : Fin e) :
    (finDoubledProdEquiv d e).symm
        (finProdFinEquiv (finProdFinEquiv (i, j), finProdFinEquiv (k, l))) =
      finProdFinEquiv (finProdFinEquiv (i, k), finProdFinEquiv (j, l)) := by
  simp [finDoubledProdEquiv]

/-- The canonical right-associated identification of a three-coordinate
function with a triple.-/
def _root_.Tengoku.Tnlean.finThreeArrowEquiv (α : Type*) : (Fin 3 → α) ≃ α × (α × α) :=
  (Fin.consEquiv fun _ : Fin 3 ↦ α).symm.trans
    (Equiv.prodCongr (Equiv.refl α) (finTwoArrowEquiv α))

/-- The canonical right-associated identification of a four-coordinate
function with a quadruple.-/
def _root_.Tengoku.Tnlean.finFourArrowEquiv (α : Type*) : (Fin 4 → α) ≃ α × (α × (α × α)) :=
  (Fin.consEquiv fun _ : Fin 4 ↦ α).symm.trans
    (Equiv.prodCongr (Equiv.refl α) (finThreeArrowEquiv α))

/-- The forward right-associated identification extracts the three coordinates
in order.
@isnad1 id=eq.0h2v.s7.16af36a8cb6d from=translated src=- shape=70b16eb6 vocab=a06befe2
-/
@[simp] theorem _root_.Tengoku.Tnlean.finThreeArrowEquiv_apply
    {α : Type*} (x : Fin 3 → α) :
    finThreeArrowEquiv α x = (x 0, x 1, x 2) := by
  rfl

/-- The inverse right-associated identification sends a triple to its three
coordinates in order.
@isnad1 id=eq.0h2v.s7.9297db2337ec from=translated src=- shape=7c36dab3 vocab=f04011e7
-/
@[simp] theorem _root_.Tengoku.Tnlean.finThreeArrowEquiv_symm_apply
    {α : Type*} (x : α × (α × α)) :
    (finThreeArrowEquiv α).symm x = ![x.1, x.2.1, x.2.2] := by
  funext i
  fin_cases i <;> rfl

/-- The forward right-associated identification extracts the four coordinates
in order.
@isnad1 id=eq.0h2v.s7.c4f401416f45 from=translated src=- shape=51bb65ac vocab=d4d3a91b
-/
@[simp] theorem _root_.Tengoku.Tnlean.finFourArrowEquiv_apply
    {α : Type*} (x : Fin 4 → α) :
    finFourArrowEquiv α x = (x 0, x 1, x 2, x 3) := by
  rfl

/-- The inverse right-associated identification sends a quadruple to its four
coordinates in order.
@isnad1 id=eq.0h2v.s7.299d6a44bf22 from=translated src=- shape=a3e2e381 vocab=f91df5f8
-/
@[simp] theorem _root_.Tengoku.Tnlean.finFourArrowEquiv_symm_apply
    {α : Type*} (x : α × (α × (α × α))) :
    (finFourArrowEquiv α).symm x = ![x.1, x.2.1, x.2.2.1, x.2.2.2] := by
  funext i
  fin_cases i <;> rfl

/-! ### A fixed initial segment and a variable remaining tuple -/

/-- Separate the first coordinate from the remaining `N` coordinates.-/
def _root_.Tengoku.Tnlean.finSuccArrowEquiv (α : Type*) (N : ℕ) :
    (Fin (N + 1) → α) ≃ α × (Fin N → α) :=
  (Fin.consEquiv fun _ : Fin (N + 1) ↦ α).symm

/-- The forward identification extracts the first coordinate and the remaining tuple.
@isnad1 id=eq.0h3v.s7.67a3f984742b from=translated src=- shape=ccf52a28 vocab=f2b4308c
-/
@[simp] theorem _root_.Tengoku.Tnlean.finSuccArrowEquiv_apply {α : Type*} (N : ℕ)
    (σ : Fin (N + 1) → α) :
    finSuccArrowEquiv α N σ = (σ 0, Fin.tail σ) :=
  rfl

/-- The inverse identification reconstructs a tuple from its first coordinate and tail.
@isnad1 id=eq.0h3v.s7.8b92aab83dab from=translated src=- shape=9d85a478 vocab=0dbd8fdb
-/
@[simp] theorem _root_.Tengoku.Tnlean.finSuccArrowEquiv_symm_apply {α : Type*} (N : ℕ)
    (p : α × (Fin N → α)) :
    (finSuccArrowEquiv α N).symm p = Fin.cons p.1 p.2 :=
  rfl

/-- Separate the first two coordinates from the remaining `N` coordinates.-/
def _root_.Tengoku.Tnlean.finAddTwoArrowEquiv (α : Type*) (N : ℕ) :
    (Fin (N + 2) → α) ≃ (α × α) × (Fin N → α) :=
  (finSuccArrowEquiv α (N + 1)).trans
    ((Equiv.prodCongr (Equiv.refl α) (finSuccArrowEquiv α N)).trans
      (Equiv.prodAssoc α α (Fin N → α)).symm)

/-- The forward identification extracts the first two coordinates and the remaining tuple.
@isnad1 id=eq.0h3v.s8.f07777aaf4e8 from=translated src=- shape=3dbf54c7 vocab=0ae7ad7b
-/
@[simp] theorem _root_.Tengoku.Tnlean.finAddTwoArrowEquiv_apply {α : Type*} (N : ℕ)
    (σ : Fin (N + 2) → α) :
    finAddTwoArrowEquiv α N σ = ((σ 0, σ 1), Fin.tail (Fin.tail σ)) :=
  rfl

/-- The inverse identification reconstructs a tuple from its first two coordinates and tail.
@isnad1 id=eq.0h3v.s8.ed0a4d6ac2b9 from=translated src=- shape=b6477376 vocab=307588d6
-/
@[simp] theorem _root_.Tengoku.Tnlean.finAddTwoArrowEquiv_symm_apply {α : Type*} (N : ℕ)
    (p : (α × α) × (Fin N → α)) :
    (finAddTwoArrowEquiv α N).symm p = Fin.cons p.1.1 (Fin.cons p.1.2 p.2) :=
  rfl
-- Tengoku: root names of this library moved to Tengoku.Tnlean so they do not collide with other libraries (generated)
