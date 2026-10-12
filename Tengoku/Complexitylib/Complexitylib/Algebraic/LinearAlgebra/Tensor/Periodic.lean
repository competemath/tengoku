/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit
import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Periodic.Internal

/-!
# Explicit border-rank lower bounds with entries from a fixed finite set

The weighted Landsberg–Michałek tensors `Tensor3.weightedLMTensor k` of
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit` have border rank at least
`(7/3 - ε) m`, `m = 2k + 1`, for all large `k`, but their coefficients `2^{2^{a m + j}}` grow
with `m`: the labels `a m + j` are distinct on all positions. This file proves the same bounds
for the periodic tensors `Tensor3.periodicLMTensor k A M = T_k(periodicWeight k A M)`, with
coefficients `2^{2^{(a mod A) M + (j mod M)}}`, whose entries come from a finite set of integers
that does not depend on `m`.

* **Entries** (`Tensor3.periodicLMTensor_apply_mem`). For `A, M > 0` every entry of
  `periodicLMTensor k A M` lies in `{0} ∪ {2^{2^e} : e < A M}`, for every `k`.
* **Window labels.** The single-cluster and paired certificates only compare labels inside one
  single-cluster block: positions of one cluster, of diameter at most `L`, whose columns differ by
  at most the `p`-subset spread, at most `p L` (`Tensor3.subsetSumSpread_le`). The codes
  `(a mod A) M + (j mod M)` separate such positions when `A > L` and `M > p L`, so the combined
  paired-cluster bound for `T_k(γ)` with window labels
  (`Tensor3.div_mul_phi_sub_le_borderRank_restrictSlices_lmTensor`) gives
  `PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 (p + 1) L)`
  (`Tensor3.pairedKoszulBoundOn_periodicLMTensor`).
* **The bounds.** `periodicLMTensor k A M` is tight with nonzero slices, like every `T_k(γ)` with
  nonzero coefficients, so the deletion game with border substitution
  (`Tensor3.PairedKoszulBoundOn.le_borderRank`) gives, for `p ≥ 1`, `3^{2p} + 1 ≤ L ≤ k`,
  `A > L` and `M > p L`,
  `borderRank ≥ (7/3 - 2 / (3 (p + 1))) m - (16 (p + 1) L + (3^{2p} + 1) m / L + 2)`
  (`Tensor3.le_borderRank_periodicLMTensor`). Taking `L ≥ 2 (3^{2p} + 1) / δ` gives
  `(7/3 - 2 / (3 (p + 1)) - δ) m` for all large `k`
  (`Tensor3.eventually_sub_mul_le_borderRank_periodicLMTensor`); hence for every `ε > 0` there
  are `A`, `M` with border rank at least `(7/3 - ε) m` for all large `k`
  (`Tensor3.exists_eventually_seven_div_three_sub_mul_le_borderRank_periodicLMTensor`), and
  `A = 14761`, `M = 29521` give `(21/10) m` for all large `k`
  (`Tensor3.eventually_twentyOne_div_ten_mul_le_borderRank_periodicLMTensor`, with `p = 2`,
  `δ = 1/90`, `L = 14760`).

The constants are independent of `m` but astronomically large. The entries are `2^{2^e}` with
`e < A M ≈ p L^2`, where `L ≈ 2 (3^{2p} + 1) / δ`; for the `(21/10) m` bound, `e` ranges below
`14761 * 29521 = 435759481`. As `ε → 0`, `p ≈ 2 / (3 ε)` grows and `A M` grows exponentially
in `p`. For the same `A` and `M`, one family `k ↦ periodicLMTensor k A M` works for all large
`k`; different `ε` use different `A` and `M`.
-/

@[expose] public section

namespace Algebraic.Tensor3

open Finset Filter

variable {k p A M : ℕ}

/-! ### Entries -/

/-- The periodic coefficients are doubly exponential:
`periodicWeight k A M a j = 2^{2^{(a mod A) M + (j mod M)}}`.
@isnad1 id=eq.0h5v.s7.8a091cfcf764 from=translated src=- shape=1f0e8bde vocab=39758cdc
-/
theorem periodicWeight_eq (a j : Fin (2 * k + 1)) :
    periodicWeight k A M a j = 2 ^ 2 ^ ((a : ℕ) % A * M + (j : ℕ) % M) :=
  Internal.Periodic.periodicWeight_eq k A M a j

/-- **The entries come from a fixed finite set.** For `A, M > 0`, every entry of
`periodicLMTensor k A M` is `0` or `2^{2^e}` with `e < A M`. The set does not depend on `k`.
@isnad1 id=mem.2h6v.s7.2e7ae70af2c7 from=translated src=- shape=290c612d vocab=ad4c4a69
-/
theorem periodicLMTensor_apply_mem (hA : 0 < A) (hM : 0 < M) (k : ℕ)
    (a j l : Fin (2 * k + 1)) :
    periodicLMTensor k A M a j l ∈
      insert (0 : ℂ) ((range (A * M)).image fun e => ((2 ^ 2 ^ e : ℕ) : ℂ)) :=
  Internal.Periodic.periodicLMTensor_apply_mem hA hM a j l

/-! ### Tightness -/

/-- The periodic Landsberg–Michałek tensor is tight, with weights `τA a = a - k`, `τB j = j`,
and `τC ℓ = -ℓ`.
@isnad1 id=tight.0h3v.s6.7a804a31e6e1 from=translated src=- shape=954a9b44 vocab=dfd35a70
-/
theorem tight_periodicLMTensor (k A M : ℕ) : (periodicLMTensor k A M).Tight :=
  Internal.Periodic.tight_periodicLMTensor k A M

/-- Every slice of the periodic Landsberg–Michałek tensor is nonzero.
@isnad1 id=ne.0h4v.s8.257c608208d9 from=translated src=- shape=e32addca vocab=b2a6d4d5
-/
theorem periodicLMTensor_ne_zero (k A M : ℕ) (a : Fin (2 * k + 1)) :
    periodicLMTensor k A M a ≠ 0 :=
  Internal.Periodic.periodicLMTensor_ne_zero k A M a

/-! ### The paired-cluster Koszul bound -/

/-- **The paired-cluster Koszul bound for the periodic tensors.** If `L < A` and `p L < M`, then
`PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 (p + 1) L)` holds, for every `k`: the
periodic labels separate any two positions whose slices differ by at most `L` and whose columns
differ by at most `p L`, which is all that the paired-cluster certificate compares.
@isnad1 id=pairedko.2h5v.s7.10e4898ef03c from=translated src=- shape=8d02ff8d vocab=fe29c1ad
-/
theorem pairedKoszulBoundOn_periodicLMTensor {L : ℕ} (hA : L < A) (hM : p * L < M) :
    PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 * (p + 1) * L) :=
  Internal.Periodic.pairedKoszulBoundOn_periodicLMTensor hA hM

/-! ### The border-rank bounds -/

end Algebraic.Tensor3
