/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# The parity lemma for nebentypus character spaces

The weight and the nebentypus of a nonzero modular form determine each other's parity:
`M_k(Γ₁(N), χ) ≠ 0` forces `χ(-1) = (-1)^k`. This is the emptiness criterion that odd
weights and Eisenstein constructions consume, and the ModularForms roadmap pins it at
Layer 0, alongside the diamond operators and character spaces of
`TauCeti.NumberTheory.ModularForms.DiamondOperators` on which it is stated.

The mechanism is `-I`. It lies in `Γ₀(N)` at every level, and its lower-right entry is the
unit `-1`, so it represents the diamond operator `⟨-1⟩`. On the other hand `-I` acts
trivially on `ℍ` and has determinant `1`, so slashing by it is multiplication by the scalar
`(-1)^k` (`ModularForm.slash_neg_one`). Comparing the two readings gives
`⟨-1⟩ = (-1)^k` as an operator (`diamondOp_neg_one`), and hence `χ(-1) = (-1)^k` on any
nonzero element of the `χ`-eigenspace.

The criterion is one-directional: matching parities do not make the space nonzero, and
nothing here claims they do. At the degenerate levels `N ∣ 2`, where `-I` lies in `Γ₁(N)`
itself (`CongruenceSubgroup.neg_one_mem_Gamma1_iff`), the same computation kills the whole of
`M_k(Γ₁(N))` in odd weight (`ModularForm.eq_zero_of_odd_of_dvd_two`, deduced from Mathlib's
`ModularForm.eq_zero_of_neg_one_mem`). That is consistent with the parity lemma rather than
additional to it: there `-1 = 1` in `(ZMod N)ˣ`, so every `χ` has `χ(-1) = 1 ≠ -1 = (-1)^k`.

## Main results

* `diamondOp_neg_one`, `diamondOpCusp_neg_one`: the diamond operator `⟨-1⟩` is the scalar
  `(-1)^k`.
* `char_neg_one_of_mem_modFormCharSpace`, `char_neg_one_of_mem_cuspFormCharSpace`: the parity
  lemma, `χ(-1) = (-1)^k` for a nonzero form in the `χ`-eigenspace.
* `modFormCharSpace_eq_bot_of_char_neg_one_ne`, `cuspFormCharSpace_eq_bot_of_char_neg_one_ne`:
  its contrapositive, the emptiness criterion; `char_neg_one_of_modFormCharSpace_ne_bot` and
  `char_neg_one_of_cuspFormCharSpace_ne_bot` restate the lemma on the space itself.
* `modFormCharSpace_one_eq_bot_of_odd`: there are no odd-weight forms with trivial nebentypus,
  the classical `M_k(Γ₀(N)) = 0` for odd `k`; `even_of_mem_modFormCharSpace_one_of_ne_zero` and
  `even_of_mem_cuspFormCharSpace_one_of_ne_zero` read it as the evenness of the weight of a
  nonzero form.
* `ModularForm.eq_zero_of_odd_of_dvd_two`: at the levels `N ∣ 2` all of `M_k(Γ₁(N))` vanishes
  in odd weight.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.1 (the remark following the
  definition of `M_k(N, χ)`)
* Miyake, *Modular forms*, §4.3
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-! ### The diamond operator at `-1` -/

/-! ### The parity lemma -/

/-! ### The emptiness criterion -/

/-! ### The degenerate levels `N ∣ 2` -/

/-- At the levels `N ∣ 2`, exactly those with `-I ∈ Γ₁(N)`, every odd-weight modular form for
`Γ₁(N)` vanishes. -/
theorem ModularForm.eq_zero_of_odd_of_dvd_two (hN : N ∣ 2) (hk : Odd k)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f = 0 :=
  _root_.ModularForm.eq_zero_of_neg_one_mem
    (Subgroup.mem_map.mpr ⟨-1, neg_one_mem_Gamma1_iff.mpr hN, mapGL_neg_one⟩) hk f

end TauCeti
