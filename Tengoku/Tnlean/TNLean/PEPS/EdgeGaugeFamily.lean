/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Tnlean.TNLean.PEPS.InsertionAlgebra
import Tengoku.Tnlean.TNLean.PEPS.EdgeGaugeExtraction
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Per-edge gauge family for injective PEPS

This file records the per-edge content of the injective PEPS Fundamental
Theorem (arXiv:1804.04964, Section 3) into one global gauge family.

For each edge `e`, blocking a vertex-injective PEPS around `e` gives a three-site
injective chain. Comparing two PEPS that generate the same state then yields, via
`isEdgeBlockedInsertionAlgebraIsomorphism` (#1367), an algebra isomorphism `Φ_e`
between the two bond matrix algebras whose inserted edge coefficients agree.
Skolem--Noether (`edgeGaugeFromInsertionAlgebraIsomorphism`) realizes each `Φ_e`
as conjugation by an invertible bond matrix. Transporting these matrices back to
the first tensor's bonds across the bond-dimension equality gives a single
gauge family `X` and records, edgewise, both the inserted-coefficient identity
and the conjugation form of `Φ_e`.

This is the construction used in the gauge-consistency theorem; the remaining
cross-edge passage to the per-vertex gauge formula is recorded in
the fundamental-theorem module and in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Transport an invertible matrix across an equality of finite index sizes.-/
noncomputable def glReindex {m n : ℕ} (h : m = n) :
    GL (Fin m) ℂ ≃* GL (Fin n) ℂ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ (finCongr h)).toRingEquiv.toMulEquiv

/-- The matrix of a transported invertible matrix is the reindexed matrix.
@isnad1 id=eq.1h3v.s8.8a46a828d899 from=translated src=- shape=12c4dc0e vocab=e5209bf7
-/
theorem glReindex_coe {m n : ℕ} (h : m = n) (Z : GL (Fin m) ℂ) :
    (↑(glReindex h Z) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) (↑Z : Matrix (Fin m) (Fin m) ℂ) :=
  rfl

/-- Transporting an invertible matrix across two successive index-size equalities is transporting
across their composite.
@isnad1 id=eq.2h4v.s9.dbfa021e8cad from=translated src=- shape=d299736f vocab=e0a0d5bd
-/
theorem glReindex_glReindex {m n k : ℕ} (h₁ : m = n) (h₂ : n = k) (Z : GL (Fin m) ℂ) :
    glReindex h₂ (glReindex h₁ Z) = glReindex (h₁.trans h₂) Z := by
  subst h₁
  subst h₂
  rfl

/-- The transpose of an invertible matrix, packaged as an invertible matrix. The
inverse is the transpose of the inverse, since transposition is an
anti-homomorphism.-/
def glTranspose {m : ℕ} (X : GL (Fin m) ℂ) : GL (Fin m) ℂ where
  val := (↑X : Matrix (Fin m) (Fin m) ℂ)ᵀ
  inv := (↑X⁻¹ : Matrix (Fin m) (Fin m) ℂ)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

/-- The matrix of `glTranspose X` is the transpose of the matrix of `X`.
@isnad1 id=eq.0h2v.s6.0cd8c759d64f from=translated src=- shape=83a201e3 vocab=c5aec39e
-/
theorem glTranspose_coe {m : ℕ} (X : GL (Fin m) ℂ) :
    (↑(glTranspose X) : Matrix (Fin m) (Fin m) ℂ) =
      (↑X : Matrix (Fin m) (Fin m) ℂ)ᵀ :=
  rfl

/-- The matrix of `(glTranspose X)⁻¹` is the transpose of the inverse of `X`.
@isnad1 id=eq.0h2v.s7.99cf557861ef from=translated src=- shape=a0a401bd vocab=4d24111b
-/
theorem glTranspose_inv_coe {m : ℕ} (X : GL (Fin m) ℂ) :
    (↑(glTranspose X)⁻¹ : Matrix (Fin m) (Fin m) ℂ) =
      (↑X⁻¹ : Matrix (Fin m) (Fin m) ℂ)ᵀ := by
  rw [Matrix.GeneralLinearGroup.coe_inv, glTranspose_coe,
    ← Matrix.transpose_nonsing_inv, Matrix.GeneralLinearGroup.coe_inv]

end PEPS
end TNLean
