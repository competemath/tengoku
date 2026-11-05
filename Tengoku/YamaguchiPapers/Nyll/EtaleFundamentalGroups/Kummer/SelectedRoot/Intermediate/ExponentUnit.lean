/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.Localization.Module
import Tengoku.Seed.RingTheory.RingHom.Etale
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.Boundary.IteratedRadical
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.Descent.FormallyUnramifiedDescent
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Regularity
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.PureRadical.HeightOneRootsOfUnity
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.PureRadical.IntegralClosure
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.HeightTwo
import Tengoku.Seed.Algebra.Polynomial.Eval.Defs
import Tengoku.Seed.Algebra.Polynomial.Eval.Coeff
import Tengoku.Seed.RingTheory.TensorProduct.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Maps
import Tengoku.Seed.Algebra.Algebra.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The selected intermediate-root exponent is a boundary unit

Let `A` be a two-parameter regular local domain with selected boundary
parameter `t`, and let `K` be its fraction field.  In a pure radical field
extension `L / K`, every intermediate field `F` has a concrete generator
`β` satisfying `β ^ [F : K] = t`.  If the actual normalization of `A` in
`F` is etale away from `t`, then `[F : K]` is invertible modulo `t`.

The proof constructs the root algebra from `β`; neither its identification
with the normalization nor the desired unit assertion is assumed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing Polynomial
open scoped BigOperators TensorProduct

universe u v w z

/-- Base change of one pure root algebra, in the ordinary `AdjoinRoot`
presentation.-/
noncomputable def oneRootBaseChangeAlgEquiv
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (m : ℕ) (t : A) :
    S ⊗[A] AdjoinRoot (X ^ m - C t) ≃ₐ[S]
      AdjoinRoot (X ^ m - C (algebraMap A S t)) := by
  let p : A[X] := X ^ m - C t
  let pS : S[X] := X ^ m - C (algebraMap A S t)
  let ePrefix : S ⊗[A] A ≃ₐ[S] S :=
    AlgEquiv.ofAlgHom
      ((Algebra.ofId A S).liftEquiv A S A S)
      (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[A] A)
      (by ext)
      (by ext)
  let q : (S ⊗[A] A)[X] :=
    p.map Algebra.TensorProduct.includeRight.toRingHom
  have hcomm :
      ePrefix (algebraMap A S t ⊗ₜ[A] (1 : A)) =
        algebraMap S S (algebraMap A S t) := by
    simpa only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      using ePrefix.commutes (algebraMap A S t)
  exact
    (AdjoinRoot.tensorAlgEquiv p q rfl).trans
      (AdjoinRoot.mapAlgEquiv ePrefix q pS <| by
        apply Associated.of_eq
        dsimp only [q, p, pS]
        rw [Polynomial.map_map, Polynomial.map_sub, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_C]
        change (X : S[X]) ^ m - C (ePrefix ((1 : S) ⊗ₜ[A] t)) =
          (X : S[X]) ^ m - C (algebraMap A S t)
        have htensor : (1 : S) ⊗ₜ[A] t =
            algebraMap A S t ⊗ₜ[A] (1 : A) := by
          simpa only [Algebra.algebraMap_self_apply] using
            (Algebra.TensorProduct.tmul_one_eq_one_tmul
              (A := S) (B := A) t).symm
        rw [htensor, hcomm]
        rfl)

/-- The one-stage recursive radical is the ordinary one-root algebra.-/
noncomputable def oneIteratedRadicalAlgEquiv
    (A : Type u) [CommRing A] (m : ℕ) (t : A) :
    iteratedRadical A 1 (fun _ : Fin 1 ↦ m) (fun _ : Fin 1 ↦ t) ≃ₐ[A]
      AdjoinRoot (X ^ m - C t) := by
  let n₁ : Fin 1 → ℕ := fun _ ↦ m
  let a₁ : Fin 1 → A := fun _ ↦ t
  let T : CommAlgCat.{u} A :=
    iteratedRadical A 0 (Fin.init n₁) (Fin.init a₁)
  let pT : T[X] :=
    X ^ n₁ (Fin.last 0) -
      C (algebraMap A T (a₁ (Fin.last 0)))
  let pA : A[X] := X ^ m - C t
  let ePrefix : T ≃ₐ[A] A := AlgEquiv.refl
  change AdjoinRoot pT ≃ₐ[A] AdjoinRoot pA
  exact AdjoinRoot.mapAlgEquiv ePrefix pT pA <| by
    apply Associated.of_eq
    dsimp only [pT, pA, n₁, a₁]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rfl

end EtaleFundamentalGroups.Kummer
