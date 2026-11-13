/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complex characters of integers modulo a natural number
-/

namespace RepresentationTheory.GroupTheory.ZMod.ComplexCharacters

variable (N : ℕ) [NeZero N]

/-- The cast of the exponent of the multiplicative form of integers modulo a nonzero natural number is nonzero.
@isnad1 id=nezero.0h1v.s5.598c4086889f from=translated src=- shape=52690cb9 vocab=11f92605
-/
instance exponent_cast_neZero :
    NeZero ((Monoid.exponent (Multiplicative (ZMod N)) : ℕ) : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩

/-- The complex character group of the multiplicative form of integers modulo a nonzero natural number is multiplicatively equivalent to that cyclic group.-/
noncomputable def complex_characters_mulEquiv :
    (Multiplicative (ZMod N) →* ℂˣ) ≃* Multiplicative (ZMod N) :=
  (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Multiplicative (ZMod N)) ℂ).some

/-- The complex character group of the multiplicative form of integers modulo a nonzero natural number is finite.
@isnad1 id=finite.0h1v.s5.d9811fb0c345 from=translated src=- shape=55897bc1 vocab=a2a3de91
-/
instance finite_complex_characters : Finite (Multiplicative (ZMod N) →* ℂˣ) :=
  Finite.of_equiv _ (complex_characters_mulEquiv N).symm.toEquiv

/-- The complex character group of the multiplicative form of integers modulo a nonzero natural number is cyclic.
@isnad1 id=iscyclic.0h1v.s6.bdbd740b489b from=translated src=- shape=55897bc1 vocab=8f62bf22
-/
instance isCyclic_complex_characters : IsCyclic (Multiplicative (ZMod N) →* ℂˣ) :=
  isCyclic_of_surjective (complex_characters_mulEquiv N).symm
    (complex_characters_mulEquiv N).symm.surjective

/-- The character group from the multiplicative form of integers modulo a nonzero natural number to the complex units has cardinality that natural number.
@isnad1 id=eq.0h1v.s5.1afa1e51e897 from=translated src=- shape=76308885 vocab=92ad28a9
-/
theorem card_complex_characters : Nat.card (Multiplicative (ZMod N) →* ℂˣ) = N := by
  rw [Nat.card_congr (complex_characters_mulEquiv N).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

/-- The number of complex characters fixed by inversion is the greatest common divisor of the modulus and two.
@isnad1 id=eq.0h1v.s7.ef81a9a2a214 from=translated src=- shape=b9b51396 vocab=751babeb
-/
theorem card_self_inverse_complex_characters :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} = Nat.gcd 2 N := by
  have hEquiv :
      {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} ≃
        (powMonoidHom 2 : (Multiplicative (ZMod N) →* ℂˣ) →* _).ker :=
    Equiv.subtypeEquivRight fun χ => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply, pow_two]
      constructor
      · intro h
        calc
          χ * χ = χ * χ⁻¹ := congrArg (fun z => χ * z) h
          _ = 1 := mul_inv_cancel χ
      · intro h
        exact (mul_eq_one_iff_eq_inv (a := χ) (b := χ)).mp h
  rw [Nat.card_congr hEquiv,
    IsCyclic.card_powMonoidHom_ker (Multiplicative (ZMod N) →* ℂˣ) 2,
    card_complex_characters, Nat.gcd_comm]

/-- The number of complex characters not fixed by inversion is the modulus minus its greatest common divisor with two.
@isnad1 id=eq.0h1v.s7.9e615e6b432b from=translated src=- shape=eb907993 vocab=8d7d2692
-/
theorem card_non_self_inverse_complex_characters :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} = N - Nat.gcd 2 N := by
  classical
  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  have hsplit :
      Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹}
        = Fintype.card (Multiplicative (ZMod N) →* ℂˣ)
          - Fintype.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ = χ⁻¹} :=
    Fintype.card_subtype_compl (fun χ => χ = χ⁻¹)
  rw [Nat.card_eq_fintype_card, hsplit, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_complex_characters, card_self_inverse_complex_characters]

/-- For an involution of a finite type, two divides the number of elements that are not fixed.
@isnad1 id=dvd.1h2v.s5.2fab2768b13f from=translated src=- shape=c0d1ce62 vocab=57aeb0b3
-/
theorem two_dvd_card_ne_fixed_of_involutive {α : Type*} [Fintype α] [DecidableEq α]
    {f : α → α} (hf : Function.Involutive f) :
    2 ∣ Fintype.card {a // f a ≠ a} := by
  set e : Equiv.Perm α := Function.Involutive.toPerm f hf with he
  have he2 : e ^ 2 = 1 := by ext a; simp [he, pow_two, Equiv.Perm.mul_apply, hf a]
  have hcard : Fintype.card {a // f a ≠ a} = e.support.card := by
    rw [Fintype.card_subtype]; congr 1
  rw [hcard, ← Equiv.Perm.sum_cycleType]
  apply Multiset.dvd_sum
  intro n hn
  have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hd : n ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one he2)
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  omega

/-- Two divides the number of complex characters that are not fixed by inversion.
@isnad1 id=dvd.0h1v.s7.78134c8b28f4 from=translated src=- shape=d43047a4 vocab=05512635
-/
theorem two_dvd_card_non_self_inverse_complex_characters :
    2 ∣ Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} := by
  classical
  haveI : Fintype (Multiplicative (ZMod N) →* ℂˣ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have h := two_dvd_card_ne_fixed_of_involutive
    (f := fun χ : (Multiplicative (ZMod N) →* ℂˣ) => χ⁻¹) (by
      intro χ
      exact inv_inv χ)
  rwa [Fintype.card_congr (Equiv.subtypeEquivRight (fun χ => ne_comm))] at h

/-- Half the number of complex characters not fixed by inversion equals half the difference between the modulus and its greatest common divisor with two.
@isnad1 id=eq.0h1v.s8.f5fb3208f9f8 from=translated src=- shape=ff65e6b7 vocab=231b1420
-/
theorem card_non_self_inverse_complex_characters_div_two :
    Nat.card {χ : Multiplicative (ZMod N) →* ℂˣ // χ ≠ χ⁻¹} / 2 =
      (N - Nat.gcd 2 N) / 2 := by
  rw [card_non_self_inverse_complex_characters]

end RepresentationTheory.GroupTheory.ZMod.ComplexCharacters
