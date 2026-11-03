/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Pow2
import Tengoku.Azurite.Azurite.AzInt.Equiv.Basic
import Tengoku.Azurite.Azurite.AzNat.Equiv.Pow2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite.AzInt

/--
@isnad1 id=eq.0h1v.s4.34665ac14056 from=translated src=- shape=b2d260a1 vocab=8238cc71
-/
theorem toInt_pow2 (k : Nat) : (AzInt.pow2 k).toInt = 2 ^ k := by
  unfold AzInt.pow2 toInt
  simp [AzNat.toNat_pow2]

/--
@isnad1 id=eq.0h1v.s4.256c117928d3 from=translated src=- shape=0f5dd7ca vocab=76501710
-/
theorem pow2_eq_ofInt (k : Nat) : AzInt.pow2 k = ofInt (2 ^ k) := by
  have h : (AzInt.pow2 k).toInt = (ofInt (2 ^ k)).toInt := by
    rw [toInt_pow2, toInt_ofInt]
  exact ofInt_toInt (AzInt.pow2 k) ▸ ofInt_toInt (ofInt (2 ^ k)) ▸ congrArg ofInt h

/--
@isnad1 id=iff.0h1v.s5.6fb75582d0aa from=translated src=- shape=e291a371 vocab=4a21d639
-/
theorem isPowerOfTwo_iff (z : AzInt) :
    z.isPowerOfTwo = true ↔ ∃ k : Nat, z.toInt = 2 ^ k := by
  unfold AzInt.isPowerOfTwo
  simp only [Bool.and_eq_true]
  rw [AzNat.isPowerOfTwo_iff]
  have hpow_pos : ∀ k : Nat, (0 : Int) < 2 ^ k := fun k => by
    have := Nat.two_pow_pos k; exact_mod_cast this
  constructor
  · rintro ⟨hsign, k, hk⟩
    refine ⟨k, ?_⟩
    unfold toInt
    rw [ite_eq_left hsign, hk]
    push_cast
    rfl
  · rintro ⟨k, hk⟩
    have hsign : z.sign = true := by
      by_contra h
      have h' : z.sign = false := by
        match hb : z.sign with
        | true => exact absurd hb h
        | false => rfl
      unfold toInt at hk
      rw [ite_eq_right (by rw [h']; decide)] at hk
      have hnn : (0 : Int) ≤ z.abs.toNat := Int.natCast_nonneg _
      have := hpow_pos k
      omega
    refine ⟨hsign, k, ?_⟩
    unfold toInt at hk
    rw [ite_eq_left hsign] at hk
    have h2 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
    rw [← h2] at hk
    exact_mod_cast hk

/--
@isnad1 id=iff.0h1v.s5.10db72771919 from=translated src=- shape=69551d3f vocab=956d3982
-/
theorem isPowerOfTwo_ofInt (i : Int) :
    (ofInt i).isPowerOfTwo = true ↔ ∃ k : Nat, i = 2 ^ k := by
  rw [isPowerOfTwo_iff, toInt_ofInt]

end Azurite.AzInt
