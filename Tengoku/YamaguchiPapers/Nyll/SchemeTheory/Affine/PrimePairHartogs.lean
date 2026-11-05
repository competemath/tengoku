/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.Affine.RegularSection
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayTensorDetection
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hartogs extension after flat base change

A section on a quasi-compact, quasi-separated open containing a principal
open has a global numerator after multiplication by a power of its regular
defining section. Two prime parameters then give a global section uniquely.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry

universe u v

/-- Clearing the denominator on a principal open gives an equality on the
larger open, because the defining global section acts injectively there.
@isnad1 id=ex.4h4v.s13.d40e54de9975 from=translated src=- shape=3524f37f vocab=271bca53
-/
theorem exists_restrict_eq_pow_mul_of_basicOpen_le
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (r : Γ(X, ⊤)) (hr : r ∈ nonZeroDivisors Γ(X, ⊤))
    (hRU : X.basicOpen r ≤ U) (s : Γ(X, U)) :
    ∃ (a : Γ(X, ⊤)) (n : ℕ),
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a =
        (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) ^ n * s := by
  let f : Γ(X, ⊤) ⟶ Γ(X, U) := X.presheaf.map (homOfLE le_top).op
  let rU : Γ(X, U) := f r
  let D := X.basicOpen rU
  let j : Γ(X, U) ⟶ Γ(X, D) :=
    X.presheaf.map (homOfLE (X.basicOpen_le rU)).op
  let k : Γ(X, ⊤) ⟶ Γ(X, D) := X.presheaf.map (homOfLE le_top).op
  have hD : D = X.basicOpen r := by
    exact (X.basicOpen_res r (homOfLE (show U ≤ ⊤ from le_top)).op).trans
      (inf_eq_right.mpr hRU)
  let : Algebra Γ(X, ⊤) Γ(X, D) := k.hom.toAlgebra
  let : IsLocalization.Away r Γ(X, D) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen r (homOfLE le_top) hD
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r (j s)
  have hcomp : f ≫ j = k := by
    dsimp only [f, j, k]
    rw [← Functor.map_comp]
    rfl
  have hcomp_apply (a : Γ(X, ⊤)) : j (f a) = k a :=
    congrArg (fun t : Γ(X, ⊤) ⟶ Γ(X, D) => t a) hcomp
  refine ⟨a, n, ?_⟩
  apply restrict_basicOpen_injective_of_affine X U hU hU' r hr
  change j (f a) = j (rU ^ n * s)
  rw [map_mul, map_pow, hcomp_apply, show j rU = k r from hcomp_apply r]
  exact ha.symm.trans (mul_comm _ _)

end AlgebraicGeometry
