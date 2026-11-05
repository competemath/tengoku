/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Iterated
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Regularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regularity of finite iterated local Kummer root covers

This file treats a finite diagonal root cover all at once.  Starting from a
regular parameter list consisting of the radicands followed by the remaining
parameters, it tracks the images of all adjoined roots and remaining
parameters in the final ring.  That list generates the final maximal ideal
and has unchanged length.  Finite faithful integrality then supplies the
dimension lower bound needed for the embedding-dimension criterion for a
regular local ring.

The recursive local-ring and module structures are installed only inside
proofs.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing

universe u

/-- The roots adjoined so far, mapped into the final iterated radical.-/
def iteratedLocalRootCoverRoots
    (A : Type u) [CommRing A] :
    (r : ℕ) → (n : Fin r → ℕ) → (a : Fin r → A) →
      List (iteratedRadical A r n a)
  | 0, _, _ => []
  | r + 1, n, a =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      (iteratedLocalRootCoverRoots A r (Fin.init n) (Fin.init a)).map
          (AdjoinRoot.of f) ++
        [AdjoinRoot.root f]

/--
The construction-order list: remaining parameters first, followed by roots in
the order in which they were adjoined.-/
def iteratedLocalRootCoverConstructionList
    (A : Type u) [CommRing A] :
    {r : ℕ} → (n : Fin r → ℕ) → (a : Fin r → A) →
      List A → List (iteratedRadical A r n a)
  | 0, _, _, rs => rs
  | r + 1, n, a, rs =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      (iteratedLocalRootCoverConstructionList A (Fin.init n) (Fin.init a) rs).map
          (AdjoinRoot.of f) ++
        [AdjoinRoot.root f]

/--
The final parameter list.  Reversing construction order puts every adjoined
root first (newest to oldest), followed by the images of the remaining
parameters.-/
def iteratedLocalRootCoverParameterList
    (A : Type u) [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (rs : List A) : List (iteratedRadical A r n a) :=
  (iteratedLocalRootCoverConstructionList A n a rs).reverse

/--
@isnad1 id=eq.0h4v.s5.cf50b38aa79f from=translated src=- shape=d80b8fb1 vocab=428145f7
-/
@[simp]
theorem iteratedLocalRootCoverRoots_length
    (A : Type u) [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    (iteratedLocalRootCoverRoots A r n a).length = r := by
  induction r with
  | zero => simp [iteratedLocalRootCoverRoots]
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      change ((iteratedLocalRootCoverRoots A r (Fin.init n) (Fin.init a)).map
        (AdjoinRoot.of f) ++ [AdjoinRoot.root f]).length = r + 1
      rw [List.length_append, List.length_map,
        ih (Fin.init n) (Fin.init a)]
      rw [List.length_singleton]

/--
@isnad1 id=eq.0h5v.s5.acbbd8ef7e50 from=translated src=- shape=024447f0 vocab=3e14d842
-/
@[simp]
theorem iteratedLocalRootCoverParameterList_length
    (A : Type u) [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (rs : List A) :
    (iteratedLocalRootCoverParameterList A n a rs).length =
      (List.ofFn a ++ rs).length := by
  induction r with
  | zero =>
      rw [iteratedLocalRootCoverParameterList, List.length_reverse]
      rw [iteratedLocalRootCoverConstructionList]
      rfl
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      change (((iteratedLocalRootCoverConstructionList A
          (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
        [AdjoinRoot.root f]).reverse).length = (List.ofFn a ++ rs).length
      rw [List.length_reverse, List.length_append, List.length_map]
      have hlen := ih (Fin.init n) (Fin.init a)
      rw [iteratedLocalRootCoverParameterList, List.length_reverse] at hlen
      rw [hlen]
      simp only [List.length_append, List.length_ofFn, List.length_singleton]
      omega

end EtaleFundamentalGroups.Kummer

end
