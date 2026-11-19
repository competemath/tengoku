/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagRankedSequence
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagCoverDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cardinality of a ranked-flag prefix

Restricting the range of a saturated ranked flag to the lower interval at
its `i`th entry leaves exactly the first `i+1` entries.  This is the rank
bookkeeping needed by the Hansen portal switch.
-/

open Set

namespace HansenCograph
namespace RankedFlag

universe u

variable {P : Type u} [PartialOrder P] [BoundedOrder P]

private noncomputable def sourceIndex {n : ℕ} (f : RankedFlag P n)
    (x : P) (hx : x ∈ f.toFlag) : Fin (n + 1) :=
  Classical.choose ((f.mem_toFlag_iff x).mp hx)

private theorem sourceIndex_spec {n : ℕ} (f : RankedFlag P n)
    (x : P) (hx : x ∈ f.toFlag) :
    f (sourceIndex f x hx) = x :=
  Classical.choose_spec ((f.mem_toFlag_iff x).mp hx)

/-- The first `i+1` indices are exactly the members of the ranked flag lying
in the lower interval at its `i`th entry.-/
noncomputable def prefixEquiv {n : ℕ} (f : RankedFlag P n)
    (i : Fin (n + 1)) :
    Fin (i.1 + 1) ≃
      {x // x ∈ Flag.restrictIic f.toFlag (f i) ⟨i, rfl⟩} where
  toFun j := by
    let j' : Fin (n + 1) := ⟨j.1, by omega⟩
    have hji : j' ≤ i := Fin.mk_le_mk.mpr (by omega)
    exact ⟨⟨f j', f.strictMono.monotone hji⟩, ⟨j', rfl⟩⟩
  invFun x := by
    let j := sourceIndex f x.1.1 x.2
    have hj : f j = x.1.1 := sourceIndex_spec f x.1.1 x.2
    have hji : j.1 ≤ i.1 := by
      by_contra h
      have hij : i < j := Fin.mk_lt_mk.mpr (Nat.lt_of_not_ge h)
      have hlt : f i < f j := f.strictMono hij
      rw [hj] at hlt
      exact (not_lt_of_ge x.1.2) hlt
    exact ⟨j.1, Nat.lt_succ_iff.mpr hji⟩
  left_inv j := by
    apply Fin.ext
    dsimp
    let j' : Fin (n + 1) := ⟨j.1, by omega⟩
    let hmem : f j' ∈ f.toFlag := ⟨j', rfl⟩
    let k := sourceIndex f (f j') hmem
    have hk : f k = f j' := sourceIndex_spec f (f j') hmem
    have hkj : k = j' := f.injective hk
    exact congrArg Fin.val hkj
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact sourceIndex_spec f x.1.1 x.2

/-- A lower-interval restriction at index `i` has cardinality `i+1`.
@isnad1 id=eq.0h4v.s8.af81956b44c7 from=translated src=- shape=17704fb6 vocab=57673e86
-/
theorem card_restrictIic_apply {n : ℕ} (f : RankedFlag P n)
    (i : Fin (n + 1)) :
    Nat.card (Flag.restrictIic f.toFlag (f i) ⟨i, rfl⟩) = i.1 + 1 := by
  rw [← Nat.card_congr (prefixEquiv f i), Nat.card_fin]

/-- A member of a ranked flag is determined by the cardinality of the flag
prefix ending there.
@isnad1 id=eq.2h5v.s7.e231b33e7af0 from=translated src=- shape=550ce2dc vocab=e3fa70dc
-/
theorem apply_eq_of_mem_of_card_restrictIic {n : ℕ} (f : RankedFlag P n)
    (i : Fin (n + 1)) (x : P) (hx : x ∈ f.toFlag)
    (hcard : Nat.card (Flag.restrictIic f.toFlag x hx) = i.1 + 1) :
    f i = x := by
  rcases (f.mem_toFlag_iff x).mp hx with ⟨j, hj⟩
  subst x
  have hjcard := card_restrictIic_apply f j
  have heq : j.1 + 1 = i.1 + 1 := by
    exact hjcard.symm.trans hcard
  have hji : j = i := by
    apply Fin.ext
    omega
  rw [← hji]

end RankedFlag
end HansenCograph
