/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RiPuiseux
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.Theorem_2_91
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RatFuncEmbedding
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_31
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_a_b

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 Theorem 2.92 — `C⟨⟨ε⟩⟩` is algebraically closed

For an algebraically closed field `C` of characteristic 0, the field of Puiseux series
`PuiseuxSeries C` is algebraically closed. Following BPR: `C = R[i]` for a real closed field `R`
(Theorem 2.31, using that `C` is algebraic over the *maximal* semireal subfield `R`), and
`R[i]⟨⟨ε⟩⟩ ≅ R⟨⟨ε⟩⟩[i]` (`riPuiseuxEquiv`), which is algebraically closed since `R⟨⟨ε⟩⟩` is real
closed (Theorem 2.91) and Theorem 2.11 (`isAlgClosed_Ri`). -/

namespace Azurite.BPR

open Polynomial

/-- **Semireal pulls back along any ring hom.** A ring hom into a semireal ring has semireal
domain (a sum of squares equal to `−1` would map to one).
@isnad1 id=issemire.0h3v.s6.3b7ebd2bfb18 from=translated src=- shape=a724b963 vocab=aae0e8d1
-/
theorem isSemireal_of_ringHom {A B : Type*} [CommRing A] [CommRing B] [IsSemireal B]
    (f : A →+* B) : IsSemireal A := by
  apply IsSemireal.of_not_isSumSq_neg_one
  intro h
  have hmap : ∀ {x : A}, IsSumSq x → IsSumSq (f x) := by
    intro x hx
    induction hx with
    | zero => simp
    | sq_add a _ ih => rw [map_add, map_mul]; exact IsSumSq.sq_add (f a) ih
  have hb : IsSumSq (-1 : B) := by have h2 := hmap h; rwa [map_neg, map_one] at h2
  exact absurd hb (IsSemireal.not_isSumSq_neg_one B)

/-- **`C` is algebraic over a maximal semireal real closed subfield.** If `t ∈ C` were
transcendental over `R`, then `R(t) ≅ RatFunc R` embeds into the ordered (hence semireal) field
`PuiseuxSeries R`, so `R(t)` is a semireal proper extension of `R`, contradicting maximality.
@isnad1 id=isalgebr.1h2v.s9.f002f1355190 from=translated src=- shape=28505b7f vocab=69ed33b6
-/
theorem algebraicOfMaximal {C : Type*} [Field C] [CharZero C] (R : IntermediateField ℚ C) [IsRealClosed ↥R]
    (hmax : ∀ S : IntermediateField ℚ C, IsSemireal ↥S → R ≤ S → S = R) :
    Algebra.IsAlgebraic ↥R C := by
  let : LinearOrder ↥R := IsRealClosed.toLinearOrder
  let : IsOrderedRing ↥R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing ↥R := IsOrderedRing.toIsStrictOrderedRing _
  rw [Algebra.isAlgebraic_def]
  intro c
  by_contra hc
  -- `hc : Transcendental ↥R c` (= `¬ IsAlgebraic`)
  -- the field `R(c)` is semireal, via `R(c) ≅ RatFunc R ↪ PuiseuxSeries R`
  have hsemiRc : IsSemireal ↥(IntermediateField.adjoin (↥R) {c}) :=
    isSemireal_of_ringHom ((ratFuncToPuiseuxHom ↥R).comp
      ((RatFunc.algEquivOfTranscendental c hc).symm : IntermediateField.adjoin (↥R) {c} →+* RatFunc ↥R))
  -- view `R(c)` as an intermediate field over `ℚ`
  set S : IntermediateField ℚ C := (IntermediateField.adjoin (↥R) {c}).restrictScalars ℚ with hS
  have hsemiS : IsSemireal ↥S := hsemiRc
  have hRS : R ≤ S := by
    intro x hx
    rw [hS, IntermediateField.mem_restrictScalars]
    exact (IntermediateField.adjoin (↥R) {c}).algebraMap_mem ⟨x, hx⟩
  have hcS : c ∈ S := by
    rw [hS, IntermediateField.mem_restrictScalars]
    exact IntermediateField.subset_adjoin (↥R) {c} rfl
  rw [hmax S hsemiS hRS] at hcS
  -- `c ∈ R`, hence `c` is algebraic over `R`
  exact hc (isAlgebraic_algebraMap (⟨c, hcS⟩ : ↥R))

/-- **`C ≅ R[i]`** for the maximal real closed subfield `R` (since `C` is its algebraic closure).-/
noncomputable def cEquivRi {C : Type*} [Field C] [IsAlgClosed C] [CharZero C] (R : IntermediateField ℚ C)
    [IsRealClosed ↥R]
    (hmax : ∀ S : IntermediateField ℚ C, IsSemireal ↥S → R ≤ S → S = R) :
    C ≃ₐ[↥R] Ri ↥R := by
  haveI : Algebra.IsAlgebraic ↥R C := algebraicOfMaximal R hmax
  haveI : IsAlgClosed (Ri ↥R) := Theorem2_11.isAlgClosed_Ri
  haveI : Module.Finite ↥R (Ri ↥R) := riMonic.finite_adjoinRoot
  haveI : IsAlgClosure ↥R C := ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosure ↥R (Ri ↥R) := ⟨inferInstance, inferInstance⟩
  exact IsAlgClosure.equiv ↥R C (Ri ↥R)

end Azurite.BPR
