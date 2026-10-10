/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.AndersonConjecture.Anderson.Jensen.CloseUp.Base
import Tengoku

/-!
# GCD complexity measure

Defines the GCD complexity of a finite set of elements in a UFD:
the sum of the lengths of their factorisations. This serves as
the well-founded measure for the inductive step of the close-up
construction when n >= 3 generators. Dividing all generators by
a common prime strictly decreases the complexity.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

lemma span_eq_mul_span_image_div {R₀ : Type*} [CommRing R₀]
    [DecidableEq R₀]
    (p : R₀) (s : Finset R₀)
    (_hp_dvd : ∀ x ∈ s, p ∣ x)
    (div_f : R₀ → R₀)
    (hdiv_spec : ∀ x ∈ s, x = p * div_f x) :
    Ideal.span (↑s : Set R₀) =
      Ideal.span {p} * Ideal.span (↑(s.image div_f) : Set R₀) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    rw [SetLike.mem_coe, hdiv_spec x (Finset.mem_coe.mp hx)]
    exact Ideal.mul_mem_mul (Ideal.subset_span rfl)
      (Ideal.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, rfl⟩)))
  · apply Ideal.mul_le.mpr
    intro a ha b hb
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ha
    suffices hpb : p * b ∈ Ideal.span (↑s : Set R₀) by
      rw [mul_comm p r, mul_assoc]
      exact Ideal.mul_mem_left _ r hpb
    exact Submodule.span_induction
      (p := fun b _ => p * b ∈ Ideal.span (↑s : Set R₀))
      (fun z hz => by
        rw [Finset.mem_coe, Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        rw [(hdiv_spec x hx).symm]
        exact Ideal.subset_span (Finset.mem_coe.mpr hx))
      (by
         change p * 0 ∈ _
         rw [mul_zero]
         exact zero_mem _)
      (fun x y _ _ hx hy => by
        change p * (x + y) ∈ _
        rw [mul_add]
        exact add_mem hx hy)
      (fun r x _ hx => by
        change p * (r • x) ∈ _
        rw [smul_eq_mul, ← mul_assoc, mul_comm p r, mul_assoc]
        exact Ideal.mul_mem_left _ r hx)
      hb

lemma prime_mul_span_insert_le {R₀ : Type*} [CommRing R₀]
    [DecidableEq R₀]
    (q' a : R₀) (rest : Finset R₀)
    (div_f : R₀ → R₀)
    (hdiv : ∀ x ∈ rest, x = q' * div_f x) :
    Ideal.span {q'} * Ideal.span (↑(insert a (rest.image div_f)) : Set R₀) ≤
      Ideal.span (↑(insert a rest) : Set R₀) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
  suffices hq'y : q' * y ∈ Ideal.span (↑(insert a rest) : Set R₀) by
    rw [mul_comm q' r, mul_assoc]
    exact Ideal.mul_mem_left _ r hq'y
  exact Submodule.span_induction
    (p := fun y _ => q' * y ∈ Ideal.span (↑(insert a rest) : Set R₀))
    (fun z hz => by
      rw [Finset.coe_insert, Set.mem_insert_iff] at hz
      rcases hz with rfl | hz'
      · exact Ideal.mul_mem_left _ q' (Ideal.subset_span
          (Finset.mem_coe.mpr (Finset.mem_insert.mpr (Or.inl rfl))))
      · rw [Finset.mem_coe, Finset.mem_image] at hz'
        obtain ⟨xo, hxo, rfl⟩ := hz'
        rw [(hdiv xo hxo).symm]
        exact Ideal.subset_span (Finset.mem_coe.mpr
          (Finset.mem_insert_of_mem hxo)))
    (by
       change q' * 0 ∈ _
       rw [mul_zero]
       exact zero_mem _)
    (fun x y _ _ hx hy => by
      change q' * (x + y) ∈ _
      rw [mul_add]
      exact add_mem hx hy)
    (fun r x _ hx => by
      change q' * (r • x) ∈ _
      rw [smul_eq_mul, ← mul_assoc, mul_comm q' r, mul_assoc]
      exact Ideal.mul_mem_left _ r hx)
    hy

-- Regularity: q prime, q ∤ a implies a is regular on T/qT, so a*t ∈ span{q} forces t ∈ span{q}.

end
