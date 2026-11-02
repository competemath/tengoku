/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveBundleFormulaAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral powers of a root of a projective-bundle relation

If a unit `z` of an `A`-algebra `B` satisfies the monic projective-bundle relation
`z^r + ∑ i < r, aᵢ zⁱ = 0` and the constant coefficient `a₀` is a unit of `A`, then every
integral power `z^n`, `n : ℤ`, lies in the `A`-span of `1, z, …, z^{r-1}`
(`SchemeProjectiveBundle.zpow_mem_span_of_relation`). This is the spanning half of the
`K₀` projective-bundle formula, where `z = [𝒪(1)]`.
-/

set_option autoImplicit false

noncomputable section

namespace SchemeProjectiveBundle

/-- Left multiplication by `w` preserves `span A s` as soon as it maps generators into it.-/
private theorem mul_mem_span_of_mul_mem_span {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (s : Set B) (w : B) (h : ∀ x ∈ s, w * x ∈ Submodule.span A s) :
    ∀ x ∈ Submodule.span A s, w * x ∈ Submodule.span A s := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- If a unit `z` of an `A`-algebra satisfies a monic degree-`r`
relation whose constant coefficient is a unit of `A`, then every integral power `z^n`, `n : ℤ`,
lies in the `A`-span of `1, z, …, z^{r-1}`.-/
theorem zpow_mem_span_of_relation {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (r : ℕ) (hr : 0 < r) (a : Fin r → A) (z : Bˣ)
    (hz : Polynomial.aeval (z : B)
      (projectiveBundleRelationPolynomial A r a) = 0)
    (ha : IsUnit (a ⟨0, hr⟩)) (n : ℤ) :
    ((z ^ n : Bˣ) : B) ∈
      Submodule.span A (Set.range fun i : Fin r ↦ (z : B) ^ (i : ℕ)) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have ha0 : IsUnit (a 0) := ha
  set M := Submodule.span A (Set.range fun i : Fin (s + 1) ↦ (z : B) ^ (i : ℕ)) with hM
  have hpow : ∀ i ≤ s, (z : B) ^ i ∈ M := fun i hi ↦
    Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
  have hrel : (z : B) ^ (s + 1) + ∑ i : Fin (s + 1), a i • (z : B) ^ (i : ℕ) = 0 := by
    have h := hz
    simp only [projectiveBundleRelationPolynomial,
      projectiveBundleRelationLower, map_add, map_pow,
      Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C] at h
    simpa only [Algebra.smul_def] using h
  -- `z^r ∈ M`
  have hzr : (z : B) ^ (s + 1) ∈ M := by
    rw [eq_neg_of_add_eq_zero_left hrel]
    exact neg_mem (sum_mem fun i _ ↦ Submodule.smul_mem _ _ (hpow i (by omega)))
  -- stability under `z`
  have hmulz : ∀ x ∈ M, (z : B) * x ∈ M := by
    refine mul_mem_span_of_mul_mem_span _ _ ?_
    rintro _ ⟨i, rfl⟩
    rw [← pow_succ']
    by_cases hi : (i : ℕ) + 1 ≤ s
    · exact hpow _ hi
    · have : (i : ℕ) + 1 = s + 1 := by omega
      rw [this]; exact hzr
  -- `z⁻¹ ∈ M`
  have hinv : ((z⁻¹ : Bˣ) : B) ∈ M := by
    rw [Fin.sum_univ_succ] at hrel
    have e : (z : B) ^ s + (a 0 • ((z⁻¹ : Bˣ) : B) +
        ∑ i : Fin s, a i.succ • (z : B) ^ (i : ℕ)) =
        ((z⁻¹ : Bˣ) : B) * ((z : B) ^ (s + 1) + (a 0 • (z : B) ^ ((0 : Fin (s + 1)) : ℕ) +
          ∑ i : Fin s, a i.succ • (z : B) ^ ((i.succ : Fin (s + 1)) : ℕ))) := by
      rw [mul_add, mul_add, Finset.mul_sum, pow_succ', Units.inv_mul_cancel_left,
        Fin.val_zero, pow_zero, mul_smul_comm, mul_one]
      congr 2
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Fin.val_succ, pow_succ', mul_smul_comm, Units.inv_mul_cancel_left]
    rw [hrel, mul_zero] at e
    have h0 : a 0 • ((z⁻¹ : Bˣ) : B) ∈ M := by
      have : a 0 • ((z⁻¹ : Bˣ) : B) =
          -((z : B) ^ s + ∑ i : Fin s, a i.succ • (z : B) ^ (i : ℕ)) := by
        linear_combination e
      rw [this]
      exact neg_mem (add_mem (hpow s le_rfl)
        (sum_mem fun i _ ↦ Submodule.smul_mem _ _ (hpow i (by omega))))
    have := Submodule.smul_mem M (↑ha0.unit⁻¹ : A) h0
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  -- stability under `z⁻¹`
  have hmulzi : ∀ x ∈ M, ((z⁻¹ : Bˣ) : B) * x ∈ M := by
    refine mul_mem_span_of_mul_mem_span _ _ ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => simpa using hinv
    | succ k =>
      change ((z⁻¹ : Bˣ) : B) * (z : B) ^ (k + 1) ∈ M
      rw [pow_succ', Units.inv_mul_cancel_left]
      exact hpow k (by omega)
  refine Int.induction_on n ?_ ?_ ?_
  · simpa using hpow 0 (Nat.zero_le _)
  · intro k hk
    rw [zpow_add_one, Units.val_mul, mul_comm]
    exact hmulz _ hk
  · intro k hk
    rw [zpow_sub_one, Units.val_mul, mul_comm]
    exact hmulzi _ hk

end SchemeProjectiveBundle
