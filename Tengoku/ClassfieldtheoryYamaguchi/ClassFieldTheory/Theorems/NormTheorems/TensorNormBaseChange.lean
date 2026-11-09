/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Norm.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Determinant norm and scalar extension

For a finite field extension `L / K`, the norm of `y : L` is unchanged by
base change, in the sense that the determinant norm of `1 ⊗ y` over a
commutative `K`-algebra `A` is the image of its field norm over `K`.
This applies to the whole tensor algebra, whether or not it is a field.
-/

open scoped TensorProduct

namespace ClassFieldTheory

universe u v w

/-- The determinant norm on `A ⊗[K] L` of a globally defined element is the
base change of its field norm. In particular, no Galois assumption or choice
of a factor of the tensor algebra is required.
@isnad1 id=eq.0h4v.s10.5f1f9f32ad5a from=translated src=- shape=911a2678 vocab=119d8f20
-/
theorem tensorNorm_includeRight
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [Nontrivial A]
    (y : L) :
    Algebra.norm A
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := L) y) =
      algebraMap K A (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange A
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b, (algebraMap K A).map_det]
  congr 1
  ext i j
  simp [bA, b, Algebra.TensorProduct.includeRight,
    Algebra.smul_def, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

end ClassFieldTheory
