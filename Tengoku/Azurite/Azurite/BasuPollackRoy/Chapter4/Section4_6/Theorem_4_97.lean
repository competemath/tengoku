/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.MultiplicationMap
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Theorem_4_94
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Theorem_4_86
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Tengoku.Seed.LinearAlgebra.Charpoly.ToMatrix
import Tengoku.Seed.LinearAlgebra.Eigenspace.Zero
import Tengoku.Seed.Algebra.CharP.Algebra
import Tengoku.Seed.RingTheory.Artinian.Ring
import Tengoku.Seed.RingTheory.KrullDimension.Zero
import Tengoku.Seed.RingTheory.HopkinsLevitzki

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.6, Theorem 4.97: the characteristic polynomial of `L_f`

The characteristic polynomial of the multiplication map `L_f` on `Ā` factors as
`∏_{x ∈ Zer} (X − f(x))^{μ(x)}`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

section PiCharpoly

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The block-diagonal endomorphism `(z i) ↦ (g i (z i))` of a finite product of modules.-/
noncomputable def blockEnd {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (g : ∀ i, Module.End R (M i)) :
    Module.End R (∀ i, M i) :=
  LinearMap.pi (fun i => (g i).comp (LinearMap.proj i))

omit [IsDomain R] in
/--
@isnad1 id=eq.0h6v.s8.93a6e2223ce8 from=translated src=- shape=89e1748b vocab=48146ab8
-/
theorem blockEnd_apply {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (g : ∀ i, Module.End R (M i))
    (z : ∀ i, M i) (i : ι) : blockEnd M g z i = g i (z i) := rfl

/-- Characteristic polynomial of a block-diagonal endomorphism of a finite product of
finite free modules equals the product of the characteristic polynomials of the blocks.
@isnad1 id=eq.0h4v.s7.142a519af40e from=translated src=- shape=29dbadc4 vocab=56ce039f
-/
theorem charpoly_pi_eq_prod {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)]
    [∀ i, Module.Free R (M i)] (g : ∀ i, Module.End R (M i)) :
    (blockEnd M g).charpoly = ∏ i, (g i).charpoly := by
  classical
  -- Property over the index type, quantified over all module families.
  let P : (ι : Type _) → [Fintype ι] → Prop := fun ι _ =>
    ∀ (M : ι → Type _) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Finite R (M i)] [∀ i, Module.Free R (M i)] (g : ∀ i, Module.End R (M i)),
      (blockEnd M g).charpoly = ∏ i, (g i).charpoly
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι M g
  · -- transport along an equivalence `α ≃ β`
    intro α β _ e hα M _ _ _ _ g
    have : Fintype α := Fintype.ofEquiv β e.symm
    -- reindex the family along `e`
    set φ : ((i' : α) → M (e i')) ≃ₗ[R] ((i : β) → M i) := LinearEquiv.piCongrLeft R M e with hφ
    have happ : ∀ (f : (i' : α) → M (e i')) (a : α), φ f (e a) = f a := by
      intro f a
      exact Equiv.piCongrLeft_apply_apply M e f a
    have hsymm : ∀ (f : (i : β) → M i) (a : α), φ.symm f a = f (e a) := by
      intro f a
      have : φ (φ.symm f) (e a) = f (e a) := by rw [LinearEquiv.apply_symm_apply]
      rw [happ] at this
      exact this
    -- conjugating the reindexed block map by `φ` recovers `blockEnd M g`
    have hconj : φ.conj (blockEnd (fun i' => M (e i')) (fun i' => g (e i')))
        = blockEnd M g := by
      apply LinearMap.ext
      intro f
      apply funext
      intro i
      obtain ⟨a, rfl⟩ := e.surjective i
      rw [LinearEquiv.conj_apply]
      show φ (blockEnd (fun i' => M (e i')) (fun i' => g (e i')) (φ.symm f)) (e a)
          = blockEnd M g f (e a)
      rw [happ, blockEnd_apply, blockEnd_apply, hsymm]
    have hαspec := hα (fun i' => M (e i')) (fun i' => g (e i'))
    rw [← hconj, LinearEquiv.charpoly_conj, hαspec]
    -- `∏ i':α, charpoly (g (e i')) = ∏ i:β, charpoly (g i)`
    exact Finset.prod_equiv e (by simp) (fun i _ => rfl)
  · -- empty
    intro M _ _ _ _ g
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact (LinearMap.charpoly_monic _).natDegree_eq_zero.mp
      (by rw [LinearMap.charpoly_natDegree]; exact Module.finrank_zero_of_subsingleton)
  · -- option
    intro α _ hα M _ _ _ _ g
    set e : ((i : Option α) → M i) ≃ₗ[R] M none × ((i : α) → M (some i)) :=
      LinearEquiv.piOptionEquivProd R with he
    -- conjugating the block map by `e` gives the binary `prodMap`.
    have hconj : e.conj (blockEnd M g)
        = (g none).prodMap (blockEnd (fun i => M (some i)) (fun i => g (some i))) := by
      apply LinearMap.ext
      rintro ⟨a, z⟩
      rw [LinearEquiv.conj_apply]
      have hsymm : e.symm (a, z) = fun o => Option.casesOn o a z := rfl
      apply Prod.ext
      · show (blockEnd M g (e.symm (a, z))) none = g none a
        rw [hsymm]; rfl
      · show (fun i => (blockEnd M g (e.symm (a, z))) (some i))
            = blockEnd (fun i => M (some i)) (fun i => g (some i)) z
        funext i
        rw [hsymm]; rfl
    rw [← LinearEquiv.charpoly_conj e (blockEnd M g), hconj,
      LinearMap.charpoly_prodMap, hα, Fintype.prod_option]

end PiCharpoly

section Factor

variable [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
  (Ps : Finset (MvPolynomial (Fin k) K)) (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)

attribute [local instance] algebraLocalizationAtPoint

omit [CharZero K] [IsAlgClosed C] in
/-- `Ā` is an Artinian ring (being a finite-dimensional `C`-algebra over the field `C`).
@isnad1 id=isartini.0h4v.s8.f370a8181093 from=translated src=- shape=0993e124 vocab=a15ea33e
-/
theorem isArtinianRing_quotPolysExt [Module.Finite C (quotPolysExt C Ps)] :
    IsArtinianRing (quotPolysExt C Ps) :=
  IsArtinianRing.of_finite C (quotPolysExt C Ps)

end Factor

section Main

variable [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

attribute [local instance] algebraLocalizationAtPoint

end Main

end Azurite.BPR.Chapter4
