/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.Germs.Basic
public import Tengoku

/-!
# Constant germs and the residue field

This file packages the constant inclusion, identifies the residue field with
`ℂ`, and supplies the zero-dimensional base case used by Rückert induction.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LocalComplexGeometry

noncomputable section

/-- Embed a complex number as a constant holomorphic germ. -/
def constantGermHom (n : ℕ) : ℂ →+* HolomorphicGerm n where
  toFun c := HolomorphicGerm.ofFunction (fun _ ↦ c) analyticAt_const
  map_zero' := by
    apply Subtype.ext
    rfl
  map_one' := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    rfl

/--
@isnad1 id=eq.0h2v.s11.b382d96bcbd1 from=translated src=- shape=203c88f1 vocab=7b6beb6e
-/
@[simp]
theorem evalAtOrigin_constantGerm (n : ℕ) (c : ℂ) :
    evalAtOriginHom n (constantGermHom n c) = c :=
  rfl

/-- Evaluation at the origin is onto, with the constant-germ map as a section.
@isnad1 id=surjecti.0h1v.s10.74d10be61fa6 from=translated src=- shape=904b06c4 vocab=1edbdd3e
-/
theorem evalAtOrigin_surjective (n : ℕ) :
    Function.Surjective (evalAtOriginHom n) := by
  intro c
  exact ⟨constantGermHom n c, by simp⟩

/-- The maximal ideal is the kernel of evaluation at the origin.
@isnad1 id=eq.0h1v.s11.2bc741496b6b from=translated src=- shape=1f68db06 vocab=8f8e5638
-/
theorem holomorphicGerm_maximalIdeal_eq_ker (n : ℕ) :
    IsLocalRing.maximalIdeal (HolomorphicGerm n) =
      RingHom.ker (evalAtOriginHom n) := by
  simpa [RingHom.ker] using holomorphicGerm_maximalIdeal n

/-- The residue field of the holomorphic local ring is canonically `ℂ`. -/
def holomorphicGermResidueFieldEquiv (n : ℕ) :
    (HolomorphicGerm n ⧸ IsLocalRing.maximalIdeal (HolomorphicGerm n)) ≃+* ℂ :=
  (Ideal.quotEquivOfEq (holomorphicGerm_maximalIdeal_eq_ker n)).trans
    (RingHom.quotientKerEquivOfSurjective (evalAtOrigin_surjective n))

/--
@isnad1 id=eq.0h2v.s15.bcb97b493497 from=translated src=- shape=ae8dd4bc vocab=a48a0081
-/
@[simp]
theorem holomorphicGerm_residueFieldEquiv_mk (n : ℕ) (f : HolomorphicGerm n) :
    holomorphicGermResidueFieldEquiv n
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolomorphicGerm n)) f) =
        evalAtOrigin f := by
  simp [holomorphicGermResidueFieldEquiv]

/-- In complex dimension zero, evaluation is injective.
@isnad1 id=injectiv.0h0v.s11.022692c19c70 from=translated src=- shape=ac73653f vocab=e9853650
-/
theorem evalAtOrigin_injective_zero :
    Function.Injective (evalAtOriginHom 0) := by
  intro φ ψ h
  obtain ⟨f, hf, hφ⟩ := φ.property
  obtain ⟨g, hg, hψ⟩ := ψ.property
  have hfg0 : f 0 = g 0 := by
    change Filter.Germ.value (φ : FunctionGerm 0) =
      Filter.Germ.value (ψ : FunctionGerm 0) at h
    rw [← hφ, ← hψ] at h
    simpa using h
  apply Subtype.ext
  rw [← hφ, ← hψ]
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro x
  have hx : x = (0 : ComplexEuclidean 0) := Subsingleton.elim _ _
  subst x
  exact hfg0

/-- The zero-dimensional holomorphic germ ring is canonically `ℂ`. -/
def holomorphicGermZeroEquiv : HolomorphicGerm 0 ≃+* ℂ :=
  RingEquiv.ofBijective (evalAtOriginHom 0)
    ⟨evalAtOrigin_injective_zero, evalAtOrigin_surjective 0⟩

/--
@isnad1 id=eq.0h1v.s13.a6a1968c3357 from=translated src=- shape=b45572ce vocab=08e5d240
-/
@[simp]
theorem holomorphicGermZeroEquiv_apply (f : HolomorphicGerm 0) :
    holomorphicGermZeroEquiv f = evalAtOrigin f :=
  rfl

/-- The zero-dimensional case of Rückert's basis theorem.
@isnad1 id=isnoethe.0h0v.s9.da4fe836c89c from=translated src=- shape=17e2345c vocab=45a6acab
-/
theorem holomorphicGerm_isNoetherian_zero :
    IsNoetherianRing (HolomorphicGerm 0) :=
  isNoetherianRing_of_ringEquiv ℂ holomorphicGermZeroEquiv.symm

end

end LocalComplexGeometry
