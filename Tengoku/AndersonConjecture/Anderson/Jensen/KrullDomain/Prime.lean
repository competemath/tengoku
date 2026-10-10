/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.AndersonConjecture.Anderson.Jensen.KrullDomain.AdjoinLocSet
import Tengoku

/-!
# Primality in R[x, y^{-1}] and coprime height bound

If x is transcendental over R and r is prime in R with r not
dividing y, then r remains prime in R[x, y^{-1}]. As a
consequence, if y_1 and y_2 are coprime in R, no height-one
prime of T contracting to a nonzero ideal of R can contain
both y_1 and y_2.
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

section AdjoinLocPrime

end AdjoinLocPrime

/-!
## Coprime height bound

Key lemma: if y₁, y₂ ∈ R are coprime (no prime divides both), then no
height-1 prime P of T (that contracts to a nonzero ideal of R) can contain
both y₁ and y₂. This is what makes the intersection approach work.
-/

section CoprimeHeight

/-- In a UFD, every nonzero prime ideal contains a prime element. -/
lemma exists_prime_mem_of_ne_bot {S : Type*} [CommRing S] [IsDomain S]
    [UniqueFactorizationMonoid S]
    (Q : Ideal S) [hQ : Q.IsPrime] (hQ_ne_bot : Q ≠ ⊥) :
    ∃ q : S, Prime q ∧ q ∈ Q := by
  obtain ⟨a, haQ, ha_ne⟩ : ∃ a ∈ Q, a ≠ (0 : S) := by
    by_contra h
    push_neg at h
    exact hQ_ne_bot (le_antisymm (fun x hx => (Submodule.mem_bot _).mpr (h x hx)) bot_le)
  have ha_nu : ¬IsUnit a := fun hu => hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q haQ hu)
  suffices ∀ x : S, x ≠ 0 → ¬IsUnit x → x ∈ Q → ∃ q : S, Prime q ∧ q ∈ Q from
    this a ha_ne ha_nu haQ
  intro x
  apply wellFounded_dvdNotUnit.induction x
  intro x ih hx_ne hx_nu hxQ
  obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hx_nu hx_ne
  obtain ⟨b, hxpb⟩ := hp_dvd
  rcases hQ.mem_or_mem (show p * b ∈ Q from hxpb ▸ hxQ) with hp_Q | hb_Q
  · exact ⟨p, hp_irr.prime, hp_Q⟩
  · exact ih b ⟨right_ne_zero_of_mul (hxpb ▸ hx_ne), p, hp_irr.prime.not_isUnit,
      by rw [hxpb, mul_comm]⟩ (right_ne_zero_of_mul (hxpb ▸ hx_ne))
      (fun hu => hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hb_Q hu)) hb_Q

end CoprimeHeight

end
