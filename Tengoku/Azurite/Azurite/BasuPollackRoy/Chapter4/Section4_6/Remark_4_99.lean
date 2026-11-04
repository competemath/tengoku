/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.MultiplicationMap
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_88
import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.LinearAlgebra.Charpoly.BaseChange
import Tengoku.Seed.LinearAlgebra.Charpoly.ToMatrix
import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.LinearAlgebra.Basis.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.6, Remark 4.99: field of definition of `tr`, `det`, `χ` of `L_f`

For `f ∈ A`, the multiplication map `L_f` on `A` is `K`-linear, so its trace, determinant and
characteristic polynomial lie in `K`, `K`, `K[T]`. Concretely they are the base-changes of the
corresponding quantities for `L_f` on `Ā` (Part 1). Moreover, in a basis `ℬ` of `A` whose
multiplication table has entries in a subring `D ⊆ K`, if `f`'s coordinates are in `D`, then trace,
det are in `D` and `χ ∈ D[T]` (Part 2).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical TensorProduct

variable {k : ℕ} {K : Type*} [Field K]

section Part1

variable (C : Type*) [Field C] [Algebra K C]

/-- Bridge A: the `C`-algebra equivalence `C ⊗_K A ≅ Ā` sends `1 ⊗ a` to the image of `a` in `Ā`.
@isnad1 id=eq.0h5v.s11.adf9d9e39605 from=translated src=- shape=14ed18c6 vocab=d7579426
-/
theorem algEquivExt_one_tmul (Ps : Finset (MvPolynomial (Fin k) K)) (a : quotPolys Ps) :
    algEquivExt C Ps (1 ⊗ₜ[K] a) = inclExt C Ps a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [inclExt_mk, algEquivExt, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  refine (Ideal.quotientEquivAlg_mk _ _ _ _).trans ?_
  congr 1
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

end Part1

section Part2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every entry of the matrix of `L_f` in the basis `B` lies in `D`, given the multiplication
table and the coordinates of `f` lie in `D`.
@isnad1 id=mem.2h9v.s13.4ce1963f8ab9 from=translated src=- shape=87abb12a vocab=49cb13e2
-/
theorem toMatrix_mulMap_mem (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps)
    (B : Module.Basis ι K (quotPolys Ps)) (D : Subring K)
    (hmul : ∀ i j l, B.repr (B i * B j) l ∈ D) (hf : ∀ i, B.repr f i ∈ D) (l j : ι) :
    (LinearMap.toMatrix B B (mulMap Ps f)) l j ∈ D := by
  rw [LinearMap.toMatrix_apply, mulMap_apply]
  have hfj : f * B j = ∑ i, B.repr f i • (B i * B j) := by
    conv_lhs => rw [← B.sum_repr f, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _)
  rw [hfj, map_sum, Finsupp.finsetSum_apply]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ (hf i) (hmul i j l)

/--
@isnad1 id=mem.2h7v.s13.ec11acb8b996 from=translated src=- shape=faa9cf4d vocab=88ff48d9
-/
theorem remark_4_99_trace_mem (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps)
    (B : Module.Basis ι K (quotPolys Ps)) (D : Subring K)
    (hmul : ∀ i j l, B.repr (B i * B j) l ∈ D) (hf : ∀ i, B.repr f i ∈ D) :
    LinearMap.trace K (quotPolys Ps) (mulMap Ps f) ∈ D := by
  rw [LinearMap.trace_eq_matrix_trace K B, Matrix.trace]
  refine Subring.sum_mem _ fun i _ => ?_
  exact toMatrix_mulMap_mem Ps f B D hmul hf i i

/--
@isnad1 id=mem.2h7v.s13.d8cf887cc9ec from=translated src=- shape=d6fb625c vocab=ec2e6841
-/
theorem remark_4_99_det_mem (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps)
    (B : Module.Basis ι K (quotPolys Ps)) (D : Subring K)
    (hmul : ∀ i j l, B.repr (B i * B j) l ∈ D) (hf : ∀ i, B.repr f i ∈ D) :
    LinearMap.det (mulMap Ps f) ∈ D := by
  set M := LinearMap.toMatrix B B (mulMap Ps f) with hMdef
  have hM : ∀ l j, M l j ∈ D := fun l j => toMatrix_mulMap_mem Ps f B D hmul hf l j
  set MD : Matrix ι ι D := fun l j => ⟨M l j, hM l j⟩ with hMD
  have hmap : M = MD.map (D.subtype) := by
    ext l j; rfl
  rw [← LinearMap.det_toMatrix B (mulMap Ps f), ← hMdef, hmap,
    show MD.map (D.subtype) = D.subtype.mapMatrix MD from rfl, ← RingHom.map_det]
  exact (MD.det).2

end Part2

end Azurite.BPR.Chapter4
