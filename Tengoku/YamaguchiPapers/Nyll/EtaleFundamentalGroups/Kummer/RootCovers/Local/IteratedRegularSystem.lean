/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.RegularSystem
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedRegularity
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedHeightOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular systems on full iterated local root covers

This file upgrades regular-locality of the finite diagonal root cover to the
stronger geometry needed branch by branch: its explicit root-and-parameter
list is a regular system generating the maximal ideal.  Hence the full cover
is a domain, every indexed root and every remaining parameter is prime, and
the quotient by any such divisor is a regular local domain.

All recursive typeclass structures remain local to proofs.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv

private theorem constructionList_cons
    {A : Type u} [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (x : A) (rs : List A) :
    iteratedLocalRootCoverConstructionList A n a (x :: rs) =
      algebraMap A (iteratedRadical A r n a) x ::
        iteratedLocalRootCoverConstructionList A n a rs := by
  induction r with
  | zero =>
      change x :: rs = algebraMap A A x :: rs
      rw [Algebra.algebraMap_self_apply]
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      change
        (iteratedLocalRootCoverConstructionList A
            (Fin.init n) (Fin.init a) (x :: rs)).map (AdjoinRoot.of f) ++
              [AdjoinRoot.root f] =
          algebraMap A (AdjoinRoot f) x ::
            (iteratedLocalRootCoverConstructionList A
              (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
                [AdjoinRoot.root f]
      rw [ih (Fin.init n) (Fin.init a), List.map_cons]
      congr 1

/-- Every indexed root occurs in the final regular parameter list.-/
theorem iteratedRadicalRoot_mem_parameterList
    {A : Type u} [CommRing A] {r : ℕ}
    (n : Fin r → ℕ) (a : Fin r → A) (rs : List A) (i : Fin r) :
    iteratedRadicalRoot A n a i ∈
      iteratedLocalRootCoverParameterList A n a rs := by
  rw [iteratedLocalRootCoverParameterList]
  simp only [List.mem_reverse]
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [iteratedRadicalRoot_last]
        change AdjoinRoot.root f ∈
          (iteratedLocalRootCoverConstructionList A
            (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
              [AdjoinRoot.root f]
        exact List.mem_append_right _
          (List.mem_singleton_self (AdjoinRoot.root f))
      · simp only [iteratedRadicalRoot_castSucc]
        change AdjoinRoot.of f
            (iteratedRadicalRoot A (Fin.init n) (Fin.init a) j) ∈
          (iteratedLocalRootCoverConstructionList A
            (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
              [AdjoinRoot.root f]
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨_, ih (Fin.init n) (Fin.init a) j, rfl⟩)

/-- Every remaining base parameter occurs, via the algebra map, in the final
regular parameter list.-/
theorem algebraMap_mem_iteratedLocalRootCoverParameterList
    {A : Type u} [CommRing A] {r : ℕ}
    (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    {x : A} (hx : x ∈ rs) :
    algebraMap A (iteratedRadical A r n a) x ∈
      iteratedLocalRootCoverParameterList A n a rs := by
  rw [iteratedLocalRootCoverParameterList]
  simp only [List.mem_reverse]
  induction rs with
  | nil => cases hx
  | cons y ys ih =>
      rw [constructionList_cons]
      simp only [List.mem_cons] at hx ⊢
      rcases hx with hxy | hx
      · left
        rw [hxy]
      · exact Or.inr (ih hx)

end EtaleFundamentalGroups.Kummer

end
