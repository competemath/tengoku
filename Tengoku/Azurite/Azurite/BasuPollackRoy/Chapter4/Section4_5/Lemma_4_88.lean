/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Tengoku.Seed.RingTheory.TensorProduct.Quotient
import Tengoku.Seed.RingTheory.TensorProduct.MvPolynomial
import Tengoku.Seed.RingTheory.TensorProduct.Free
import Tengoku.Seed.RingTheory.TensorProduct.Finite
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5, Lemma 4.88: `dim_K A = dim_C Ā`

Let `K` be a field, `C` an algebraically closed field containing `K`, and `𝒫` a finite set of
polynomials in `K[X₁, …, X_k]`. Then `A = K[X]/Ideal(𝒫,K)` is a finite-dimensional vector space
of dimension `m` over `K` if and only if `Ā = C[X]/Ideal(𝒫,C)` is a finite-dimensional vector
space of dimension `m` over `C`.

This is the base-change statement: `Ā ≅ C ⊗_K A` as `C`-algebras (`algEquivExt`), built from
`Algebra.TensorProduct.tensorQuotientEquiv` (tensor commutes with the quotient by an extended
ideal) and `MvPolynomial.algebraTensorAlgEquiv` (`C ⊗_K K[X] ≅ C[X]`). Dimension and finiteness
then transfer through `Module.finrank_baseChange` and `Algebra.TensorProduct.basis`. (BPR's
elementary proof — descent of a linear dependence from `C` to `K` — is the same fact specialized
to the rank of the relevant linear system; cf. the descent in Lemma 4.87.)
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical TensorProduct

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]

/-- **`Ā ≅ C ⊗_K A` as `C`-algebras.** Tensoring `A = K[X]/Ideal(𝒫,K)` up to `C` and identifying
`C ⊗_K K[X]` with `C[X]` (under which the extended ideal becomes `Ideal(𝒫,C)`) yields `Ā`.
@isnad1 id=eq.0h4v.s11.520f9a2ce099 from=translated src=- shape=bd139883 vocab=dac04f11
-/
theorem algebraTensorAlgEquiv_includeRight (P : MvPolynomial (Fin k) K) :
    (algebraTensorAlgEquiv K C) (Algebra.TensorProduct.includeRight P)
      = MvPolynomial.map (algebraMap K C) P := by
  rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- The extended ideal is the image of the base-changed ideal under `C ⊗_K K[X] ≅ C[X]`.
@isnad1 id=eq.0h4v.s11.d78af66f60f7 from=translated src=- shape=8fae2f3d vocab=2ebbadd0
-/
theorem idealOfPolysExt_eq_map_tensor (Ps : Finset (MvPolynomial (Fin k) K)) :
    idealOfPolysExt C Ps
      = Ideal.map (algebraTensorAlgEquiv K C)
          (Ideal.map (Algebra.TensorProduct.includeRight) (idealOfPolys Ps)) := by
  rw [idealOfPolysExt, idealOfPolys, idealOfPolys, Ideal.map_span, Ideal.map_span,
    ← Set.image_comp, Finset.coe_image]
  congr 1
  exact Set.image_congr fun P _ => (algebraTensorAlgEquiv_includeRight C P).symm

noncomputable def algEquivExt (Ps : Finset (MvPolynomial (Fin k) K)) :
    C ⊗[K] quotPolys Ps ≃ₐ[C] quotPolysExt C Ps :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) C (MvPolynomial (Fin k) K) C
      (idealOfPolys Ps)).trans
    (Ideal.quotientEquivAlg (Ideal.map (Algebra.TensorProduct.includeRight) (idealOfPolys Ps))
      (idealOfPolysExt C Ps) (algebraTensorAlgEquiv K C) (idealOfPolysExt_eq_map_tensor C Ps))

/-- **BPR Lemma 4.88.** `A = K[X]/Ideal(𝒫,K)` is finite-dimensional of dimension `m` over `K` if
and only if `Ā = C[X]/Ideal(𝒫,C)` is finite-dimensional of dimension `m` over `C`: the dimensions
agree, and one is finite-dimensional exactly when the other is.
@isnad1 id=and.0h4v.s10.88b0ed147ae1 from=translated src=- shape=d62258c7 vocab=f14a9e85
-/
theorem lemma_4_88 (Ps : Finset (MvPolynomial (Fin k) K)) :
    Module.finrank K (quotPolys Ps) = Module.finrank C (quotPolysExt C Ps) ∧
      (FiniteDimensional K (quotPolys Ps) ↔ FiniteDimensional C (quotPolysExt C Ps)) := by
  have e : quotPolysExt C Ps ≃ₗ[C] C ⊗[K] quotPolys Ps :=
    (algEquivExt C Ps).symm.toLinearEquiv
  refine ⟨?_, ?_, ?_⟩
  · rw [e.finrank_eq, Module.finrank_baseChange]
  · intro hA
    have := hA
    have : Module.Finite C (C ⊗[K] quotPolys Ps) := inferInstance
    exact Module.Finite.equiv (algEquivExt C Ps).toLinearEquiv
  · intro hAbar
    have := hAbar
    have : Module.Finite C (C ⊗[K] quotPolys Ps) := Module.Finite.equiv e
    let b := Module.Free.chooseBasis K (quotPolys Ps)
    have : Fintype (Module.Free.ChooseBasisIndex K (quotPolys Ps)) :=
      FiniteDimensional.fintypeBasisIndex (Algebra.TensorProduct.basis C b)
    exact Module.Finite.of_basis b

end Azurite.BPR.Chapter4
