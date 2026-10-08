/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Algebra.Exponential
public import Tengoku.Seed.Analysis.Matrix.Normed
public import Tengoku.Seed.LinearAlgebra.Matrix.ZPow
public import Tengoku.Seed.LinearAlgebra.Matrix.Hermitian
public import Tengoku.Seed.LinearAlgebra.Matrix.Symmetric
public import Tengoku.Seed.LinearAlgebra.Matrix.Block
public import Tengoku.Seed.Topology.UniformSpace.Matrix
public import Tengoku.Seed.Topology.Instances.Matrix

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `NormedSpace.exp` on `Matrix`s
over a topological or normed algebra.
Note that generic results over all topological spaces such as `NormedSpace.exp_zero`
can be used on matrices without issue, so are not repeated here.
The topological results specific to matrices are:

* `Matrix.exp_transpose`
* `Matrix.exp_conjTranspose`
* `Matrix.exp_diagonal`
* `Matrix.exp_blockDiagonal`
* `Matrix.exp_blockDiagonal'`

Lemmas like `NormedSpace.exp_add_of_commute` require a canonical norm on the type;
while there are multiple sensible choices for the norm of a `Matrix` (`Matrix.normedAddCommGroup`,
`Matrix.frobeniusNormedAddCommGroup`, `Matrix.linftyOpNormedAddCommGroup`), none of them
are canonical. In an application where a particular norm is chosen using
`attribute [local instance]`, then the usual lemmas about `NormedSpace.exp` are fine.
When choosing a norm is undesirable, the results in this file can be used.

In this file, we copy across the lemmas about `NormedSpace.exp`,
but hide the requirement for a norm inside the proof.

* `Matrix.exp_add_of_commute`
* `Matrix.exp_sum_of_commute`
* `Matrix.exp_nsmul`
* `Matrix.isUnit_exp`
* `Matrix.exp_units_conj`
* `Matrix.exp_units_conj'`

Additionally, we prove some results about `matrix.has_inv` and `matrix.div_inv_monoid`, as the
results for general rings are instead stated about `Ring.inverse`:

* `Matrix.exp_neg`
* `Matrix.exp_zsmul`
* `Matrix.exp_conj`
* `Matrix.exp_conj'`

## TODO

* Show that `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`

## References

* https://en.wikipedia.org/wiki/Matrix_exponential
-/

public section

open scoped Matrix

open NormedSpace -- For `exp`.

variable {m n : Type*} {n' : m → Type*} {α 𝔸 : Type*}

namespace Matrix

section Topological

section Ring

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]
  [T2Space 𝔸]

/--
@isnad1 id=eq.0h3v.s6.6159d29f37d2 from=seed src=0 shape=5953db77 vocab=c0cefea3
-/
theorem exp_diagonal [Algebra ℚ 𝔸] (v : m → 𝔸) : exp (diagonal v) = diagonal (exp v) := by
  simp_rw [exp_eq_tsum_rat, diagonal_pow, ← diagonal_smul, ← diagonal_tsum]

/--
@isnad1 id=eq.0h4v.s7.7eeaadb7ca9e from=seed src=0 shape=02f1269b vocab=cd7ddb6c
-/
theorem exp_blockDiagonal [Algebra ℚ 𝔸] (v : m → Matrix n n 𝔸) :
    exp (blockDiagonal v) = blockDiagonal (exp v) := by
  simp_rw [exp_eq_tsum_rat, ← blockDiagonal_pow, ← blockDiagonal_smul, ← blockDiagonal_tsum]

/--
@isnad1 id=eq.0h4v.s7.ae6ffc86d309 from=seed src=0 shape=8a23307c vocab=1f75d1e9
-/
theorem exp_blockDiagonal' [Algebra ℚ 𝔸] (v : ∀ i, Matrix (n' i) (n' i) 𝔸) :
    exp (blockDiagonal' v) = blockDiagonal' (exp v) := by
  simp_rw [exp_eq_tsum_rat, ← blockDiagonal'_pow, ← blockDiagonal'_smul, ← blockDiagonal'_tsum]

/--
@isnad1 id=eq.0h3v.s7.a4017489411e from=seed src=0 shape=9a4c5194 vocab=7bcabcd9
-/
theorem exp_conjTranspose [StarRing 𝔸] [ContinuousStar 𝔸] (A : Matrix m m 𝔸) :
    exp Aᴴ = (exp A)ᴴ :=
  (star_exp A).symm

/--
@isnad1 id=ishermit.1h3v.s7.611eaa4178d1 from=seed src=0 shape=6ca86993 vocab=5981e443
-/
theorem IsHermitian.exp [StarRing 𝔸] [ContinuousStar 𝔸] {A : Matrix m m 𝔸} (h : A.IsHermitian) :
    (exp A).IsHermitian :=
  (exp_conjTranspose _).symm.trans <| congr_arg _ h

/--
@isnad1 id=blocktri.1h5v.s6.40cc389358f4 from=seed src=0 shape=200e89d4 vocab=81b29270
-/
theorem BlockTriangular.exp [LinearOrder α] [Algebra ℚ 𝔸] {M : Matrix m m 𝔸} {b : m → α}
    (hM : BlockTriangular M b) :
    (exp M).BlockTriangular b :=
  exp_mem (s := blockTriangularSubalgebra ℚ _ b) isClosed_setOfPred_blockTriangular hM

end Ring

section CommRing

variable [Fintype m] [DecidableEq m] [CommRing 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸] [Algebra ℚ 𝔸] [T2Space 𝔸]

/--
@isnad1 id=eq.0h3v.s6.35de43c5f463 from=seed src=0 shape=47514142 vocab=d84a0ec0
-/
theorem exp_transpose (A : Matrix m m 𝔸) : exp Aᵀ = (exp A)ᵀ := by
  simp_rw [exp_eq_tsum_rat, transpose_tsum, transpose_smul, transpose_pow]

/--
@isnad1 id=issymm.1h3v.s6.fc3d026bd0f0 from=seed src=0 shape=88067a4a vocab=e05f7960
-/
theorem IsSymm.exp {A : Matrix m m 𝔸} (h : A.IsSymm) : (exp A).IsSymm :=
  (exp_transpose _).symm.trans <| congr_arg _ h

end CommRing

end Topological

section Normed

variable [Fintype m] [DecidableEq m] [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h4v.s7.6f41a2f5e0c5 from=seed src=0 shape=5ca1d0fe vocab=02be9f92
-/
nonrec theorem exp_add_of_commute (A B : Matrix m m 𝔸) (h : Commute A B) :
    exp (A + B) = exp A * exp B :=
  open scoped Norms.Operator in exp_add_of_commute h

set_option backward.isDefEq.respectTransparency false in
open scoped Function in -- required for scoped `on` notation
/--
@isnad1 id=eq.1h5v.s7.b46087ff75a5 from=seed src=0 shape=d93252b4 vocab=02e70fa3
-/
nonrec theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → Matrix m m 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp (f i)) fun _ hi _ hj _ => (h.forall₂ hi hj).exp :=
  open scoped Norms.Operator in exp_sum_of_commute s f h

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s7.03c0287f54b8 from=seed src=0 shape=0eb2d723 vocab=71cdb229
-/
nonrec theorem exp_nsmul (n : ℕ) (A : Matrix m m 𝔸) : exp (n • A) = exp A ^ n :=
  open scoped Norms.Operator in exp_nsmul n A

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isunit.0h3v.s6.3612058d24ae from=seed src=0 shape=fecc4654 vocab=f0254261
-/
nonrec theorem isUnit_exp (A : Matrix m m 𝔸) : IsUnit (exp A) :=
  open scoped Norms.Operator in isUnit_exp A

set_option backward.isDefEq.respectTransparency false in
-- TODO: without disabling this instance we get a timeout, see lean4#10414:
-- https://github.com/leanprover/lean4/issues/10414
-- and zulip discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Coercion.20instance.20problems.20with.20matrix.20exponential/with/539770030
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/--
@isnad1 id=eq.0h4v.s8.ab4bd5c7bfc2 from=seed src=0 shape=6e9bb9af vocab=8befe329
-/
nonrec theorem exp_units_conj (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp (U * A * U⁻¹) = U * exp A * U⁻¹ :=
  open scoped Norms.Operator in exp_units_conj U A

-- TODO: without disabling this instance we get a timeout, see lean4#10414:
-- https://github.com/leanprover/lean4/issues/10414
-- and zulip discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Coercion.20instance.20problems.20with.20matrix.20exponential/with/539770030
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/--
@isnad1 id=eq.0h4v.s8.5ac5fc4153e4 from=seed src=0 shape=35ec13d9 vocab=8befe329
-/
theorem exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp (U⁻¹ * A * U) = U⁻¹ * exp A * U :=
  exp_units_conj U⁻¹ A

end Normed

section NormedComm

variable [Fintype m] [DecidableEq m]
  [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s7.6f06cacf9581 from=seed src=0 shape=df748f83 vocab=88fe0d25
-/
theorem exp_neg (A : Matrix m m 𝔸) : exp (-A) = (exp A)⁻¹ := by
  rw [nonsing_inv_eq_ringInverse]
  open scoped Norms.Operator in exact (Ring.inverse_exp A).symm

/--
@isnad1 id=eq.0h4v.s7.45340407a082 from=seed src=0 shape=0eb2d723 vocab=4925f2df
-/
theorem exp_zsmul (z : ℤ) (A : Matrix m m 𝔸) : exp (z • A) = exp A ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · have : IsUnit (exp A).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_exp _)
    rw [Matrix.zpow_neg this, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]

/--
@isnad1 id=eq.1h4v.s8.83bb7b166e5d from=seed src=0 shape=a4b601a3 vocab=29e08e04
-/
theorem exp_conj (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U * A * U⁻¹) = U * exp A * U⁻¹ :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj u A

/--
@isnad1 id=eq.1h4v.s8.87117dc3fd6f from=seed src=0 shape=5d6d8189 vocab=29e08e04
-/
theorem exp_conj' (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U⁻¹ * A * U) = U⁻¹ * exp A * U :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj' u A

end NormedComm

end Matrix
