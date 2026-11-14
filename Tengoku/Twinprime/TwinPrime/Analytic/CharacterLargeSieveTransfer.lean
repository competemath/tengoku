import Tengoku.Twinprime.TwinPrime.Analytic.PrimitiveGauss
import Tengoku.Seed.NumberTheory.DirichletCharacter.Orthogonality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite transfer from additive sums to primitive character sums

Parseval on the unit group and the primitive Gauss-sum norm identity give
the multiplicative large-sieve transfer at each positive modulus. This
finite inequality does not assume an additive large-sieve estimate.
-/

noncomputable section

open Finset Classical
open scoped ComplexConjugate

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.0h3v.s8.59e2fe0f98e0 from=translated src=- shape=0ee3cb25 vocab=e205bd6c
-/
theorem unit_character_orthogonality {q : ℕ} [NeZero q]
    (u v : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, χ u * conj (χ v)) =
      if u = v then (Nat.totient q : ℂ) else 0 := by
  have hinv (χ : DirichletCharacter ℂ q) : conj (χ v) = χ (↑v⁻¹ : ZMod q) := by
    rw [← character_inv_apply_eq_conj, MulChar.inv_apply, Ring.inverse_unit]
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, χ ((v : ZMod q)⁻¹) * χ u := by
      apply sum_congr rfl
      intro χ _
      rw [hinv, ZMod.inv_coe_unit, mul_comm]
    _ = if (v : ZMod q) = (u : ZMod q) then (Nat.totient q : ℂ) else 0 :=
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit u
    _ = _ := by simp only [Units.val_inj, eq_comm]

/-- Unnormalized character Parseval for a function on the unit group.
@isnad1 id=eq.0h2v.s8.50926e6e5e75 from=translated src=- shape=7fb3b30e vocab=f0e0eea4
-/
theorem unit_character_parseval {q : ℕ} [NeZero q]
    (f : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2) =
      (Nat.totient q : ℝ) * ∑ u : (ZMod q)ˣ, ‖f u‖ ^ 2 := by
  classical
  have hexpand (χ : DirichletCharacter ℂ q) :
      (∑ u : (ZMod q)ˣ, χ u * f u) * conj (∑ u : (ZMod q)ˣ, χ u * f u) =
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          (f u * conj (f v)) * (χ u * conj (χ v)) := by
    simp only [map_sum, map_mul, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  have hcomplex :
      (∑ χ : DirichletCharacter ℂ q,
        (∑ u : (ZMod q)ˣ, χ u * f u) * conj (∑ u : (ZMod q)ˣ, χ u * f u)) =
        (Nat.totient q : ℂ) * ∑ u : (ZMod q)ˣ, f u * conj (f u) := by
    simp_rw [hexpand]
    rw [sum_comm]
    calc
      _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          (f u * conj (f v)) *
            ∑ χ : DirichletCharacter ℂ q, χ u * conj (χ v) := by
        apply sum_congr rfl
        intro u _
        rw [sum_comm]
        apply sum_congr rfl
        intro v _
        rw [mul_sum]
      _ = ∑ u : (ZMod q)ˣ, (f u * conj (f u)) * (Nat.totient q : ℂ) := by
        simp_rw [unit_character_orthogonality, mul_ite, mul_zero]
        simp
      _ = _ := by rw [← sum_mul, mul_comm]
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at hcomplex
  exact Complex.ofReal_injective hcomplex

/-- The zero values of a character outside the unit group allow the unit
sum to be identified with the Gauss sum over the whole residue ring.
@isnad1 id=eq.0h3v.s7.e1fae045b546 from=translated src=- shape=b8dd6bcd vocab=ec27baf1
-/
theorem sum_units_character_mul_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, χ u * f u) = ∑ a : ZMod q, χ a * f a := by
  classical
  calc
    _ = ∑ a ∈ univ.filter IsUnit, χ a * f a := by
      apply sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q))
      · intro u _
        exact mem_filter.mpr ⟨mem_univ _, u.isUnit⟩
      · intro u _ v _ h
        exact Units.val_injective h
      · intro a ha
        exact ⟨(mem_filter.mp ha).2.unit, mem_univ _, (mem_filter.mp ha).2.unit_spec⟩
      · intro u _
        rfl
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro a _ ha
      have hna : ¬ IsUnit a := by simpa only [mem_filter, mem_univ, true_and] using ha
      rw [χ.map_nonunit hna, zero_mul]

/-- Exact Gauss-sum factorization. The inverse character convention matches
the standard additive character with a positive sign in its argument.
@isnad1 id=eq.1h4v.s8.231a99d61343 from=translated src=- shape=61c1e823 vocab=66db6f3e
-/
theorem primitive_character_additive_factorization {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : Finset ℕ) (a : ℕ → ℂ) :
    gaussSum χ ZMod.stdAddChar * (∑ n ∈ s, a n * χ⁻¹ n) =
      ∑ u : (ZMod q)ˣ, χ u * ∑ n ∈ s, a n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) := by
  classical
  symm
  calc
    _ = ∑ n ∈ s, a n * ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro u _
      ring
    _ = ∑ n ∈ s, a n * (χ⁻¹ n * gaussSum χ ZMod.stdAddChar) := by
      apply sum_congr rfl
      intro n _
      congr 1
      rw [sum_units_character_mul_eq χ
        (fun u : ZMod q => ZMod.stdAddChar (u * (n : ZMod q)))]
      have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (n : ZMod q)
      simpa only [gaussSum, AddChar.mulShift_apply, mul_comm] using h
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro n _; ring

/-- Finite transfer at one positive modulus. Restriction to primitive
characters is the only inequality; the unrestricted unit transform obeys Parseval.
@isnad1 id=le.0h3v.s8.f1fe13b79466 from=translated src=- shape=67b9710f vocab=8923b2d0
-/
theorem primitive_character_largeSieve_transfer {q : ℕ} [NeZero q]
    (s : Finset ℕ) (a : ℕ → ℂ) :
    (q : ℝ) / Nat.totient q *
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ s, a n * χ⁻¹ n‖ ^ 2) ≤
      ∑ u : (ZMod q)ˣ, ‖∑ n ∈ s, a n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))‖ ^ 2 := by
  classical
  let f : (ZMod q)ˣ → ℂ := fun u => ∑ n ∈ s, a n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))
  have hprimitive : (q : ℝ) *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ⁻¹ n‖ ^ 2) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro χ hχ
    have hp := (mem_filter.mp hχ).2
    rw [← primitive_character_additive_factorization χ hp s a, norm_mul, mul_pow,
      norm_primitive_gaussSum_sq χ hp]
  have hrestrict :
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2) ≤
      ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro χ _ _
    positivity
  rw [unit_character_parseval] at hrestrict
  rw [← hprimitive] at hrestrict
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hφ).mpr
  simpa only [f, mul_comm] using hrestrict

end TwinPrime.Analytic
