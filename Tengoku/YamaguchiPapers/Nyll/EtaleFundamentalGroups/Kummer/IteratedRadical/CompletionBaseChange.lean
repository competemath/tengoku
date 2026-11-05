/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ClosedPrime
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedCompletion
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Completion base change of an iterated radical

The iterated radical formed after completing the base is canonically the
base change of the original iterated radical.  This file fixes the induced
algebra structure in the right-factor direction and records the local,
residue, finite-etale, and chosen-closed-prime data needed by complete-local
factor consumers.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped TensorProduct

universe u

/-- The canonical base-change coordinates for an iterated radical after
maximal-adic completion.-/
noncomputable def iteratedRadicalCompletionBaseChangeAlgEquiv
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
  iteratedRadicalBaseChangeAlgEquiv n a

/-- The original iterated radical acts on the completed iterated radical
through the right tensor factor of the canonical base-change equivalence.
This named definition avoids a global competing algebra instance.-/
@[reducible]
noncomputable def iteratedRadicalCompletionAlgebra
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    Algebra B Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let e : Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
    iteratedRadicalCompletionBaseChangeAlgEquiv n a
  exact
    (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] Ahat ⊗[A] B).toRingHom).toAlgebra

/-- The canonical base-change equivalence, now read as an equivalence of
algebras over the original iterated radical.-/
noncomputable def iteratedRadicalCompletionRightAlgEquiv
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    letI : Algebra B (Ahat ⊗[A] B) :=
      Algebra.TensorProduct.rightAlgebra
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    (Ahat ⊗[A] B) ≃ₐ[B] Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let e : Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
    iteratedRadicalCompletionBaseChangeAlgEquiv n a
  letI : Algebra B (Ahat ⊗[A] B) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  refine
    { toRingEquiv := e.toRingEquiv
      commutes' := ?_ }
  intro b
  change e ((Algebra.TensorProduct.includeRight :
    B →ₐ[A] Ahat ⊗[A] B) b) =
      e ((Algebra.TensorProduct.includeRight :
        B →ₐ[A] Ahat ⊗[A] B) b)
  rfl

/-- Completion base change is faithfully flat over the original iterated
radical.  This is ordinary faithful-flat base change, transported through
the canonical radical coordinates.
@isnad1 id=other.0h4v.s8.2a85f114c533 from=translated src=- shape=ad8aaf0f vocab=f476c089
-/
theorem faithfullyFlat_iteratedRadicalCompletion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    Module.FaithfullyFlat B Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let : Module.FaithfullyFlat A Ahat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra B (Ahat ⊗[A] B) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let eComm : (B ⊗[A] Ahat) ≃ₐ[B] (Ahat ⊗[A] B) :=
    { toRingEquiv := (Algebra.TensorProduct.comm A B Ahat).toRingEquiv
      commutes' := by
        intro b
        change Algebra.TensorProduct.comm A B Ahat
            (b ⊗ₜ[A] (1 : Ahat)) =
          ((1 : Ahat) ⊗ₜ[A] b)
        rw [Algebra.TensorProduct.comm_tmul] }
  let e : (B ⊗[A] Ahat) ≃ₐ[B] Bhat :=
    eComm.trans (iteratedRadicalCompletionRightAlgEquiv n a)
  exact Module.FaithfullyFlat.of_linearEquiv
    (R := B) (M := B ⊗[A] Ahat) e.symm.toLinearEquiv

/-- The two coefficient maps into the completed iterated radical agree.
@isnad1 id=other.0h5v.s12.1f79d4fb6072 from=translated src=- shape=57263757 vocab=1d9095e8
-/
theorem iteratedRadicalCompletion_algebraMap_comp_apply
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (x : A) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    algebraMap B Bhat (algebraMap A B x) =
      algebraMap Ahat Bhat (algebraMap A Ahat x) := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let e : Ahat ⊗[A] B ≃ₐ[Ahat] Bhat :=
    iteratedRadicalCompletionBaseChangeAlgEquiv n a
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  change e (1 ⊗ₜ[A] algebraMap A B x) =
    algebraMap Ahat Bhat (algebraMap A Ahat x)
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  exact e.commutes (algebraMap A Ahat x)

end EtaleFundamentalGroups.Kummer

end
