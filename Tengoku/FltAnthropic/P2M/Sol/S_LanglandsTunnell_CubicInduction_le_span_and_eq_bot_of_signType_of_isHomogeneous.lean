import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_le_span_and_eq_bot_of_signType_of_isHomogeneous.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_le_span_and_eq_bot_of_signType_of_isHomogeneous

set_option autoImplicit false

namespace WsC
namespace SC

open MvPolynomial

noncomputable section

abbrev R3 := MvPolynomial (Fin 3) ℂ

/--
@isnad1 id=ne.0h0v.s5.a12388f0aca2 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
/--
@isnad1 id=ne.0h0v.s5.9556c64377c8 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
/--
@isnad1 id=ne.0h0v.s5.93abf1c8e128 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
/--
@isnad1 id=ne.0h0v.s5.d0ddbab9dc92 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
/--
@isnad1 id=ne.0h0v.s5.1e882522a86f from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
/--
@isnad1 id=ne.0h0v.s5.7b05c920c4d2 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide

/--
@isnad1 id=eq.0h3v.s10.e0d4160868f6 from=translated src=- shape=c02e5602 vocab=6f4f03d0
-/
theorem aeval_scale_monomial (s : Fin 3 → ℂ) (d : Fin 3 →₀ ℕ) (r : ℂ) :
    aeval (fun a : Fin 3 => C (s a) * X a) (monomial d r) =
      monomial d ((∏ a, s a ^ d a) * r) := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), monomial_eq,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), MvPolynomial.algebraMap_eq]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow]
  ring

/--
@isnad1 id=eq.0h3v.s9.2fe307a84321 from=translated src=- shape=4849929a vocab=4ac8754b
-/
theorem coeff_aeval_scale (s : Fin 3 → ℂ) (p : R3) (m : Fin 3 →₀ ℕ) :
    coeff m (aeval (fun a : Fin 3 => C (s a) * X a) p) = (∏ a, s a ^ m a) * coeff m p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  simp only [aeval_scale_monomial, coeff_sum, coeff_monomial]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  split_ifs with h
  · rw [h, mul_zero]
  · rfl

/--
@isnad1 id=even.3h6v.s10.a66c548b844e from=translated src=- shape=9b39d3b2 vocab=6f5b524d
-/
theorem parity (ε : Fin 3 → Fin 2) (S : ℕ → Submodule ℂ R3)
    (hsign : ∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        aeval (fun a : Fin 3 => C ((-1 : ℂ) ^ (σ a : ℕ)) * X a) p =
          C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p)
    (ℓ : ℕ) (p : R3) (hp : p ∈ S ℓ) (m : Fin 3 →₀ ℕ) (hm : coeff m p ≠ 0) (a : Fin 3) :
    Even (m a + ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ))) := by
  classical
  set σ : Fin 3 → Fin 2 := fun b => if b = a then 1 else 0 with hσ
  have h := congrArg (coeff m) (hsign ℓ p hp σ)
  rw [coeff_aeval_scale, coeff_C_mul] at h
  have h2 := mul_right_cancel₀ hm h
  have hL : (∏ b : Fin 3, ((-1 : ℂ) ^ ((σ b : Fin 2) : ℕ)) ^ m b) = (-1) ^ (m a) := by
    rw [Finset.prod_eq_single_of_mem a (Finset.mem_univ a)]
    · simp [hσ]
    · intro b _ hb
      simp [hσ, hb]
  have hR : (∑ b : Fin 3, ((ε b : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * ((σ b : Fin 2) : ℕ)) =
      (ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ) := by
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
    · simp [hσ]
    · intro b _ hb
      simp [hσ, hb]
  rw [hL, hR] at h2
  have h3 : (-1 : ℂ) ^ (m a + ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ))) = 1 := by
    rw [pow_add, h2, ← pow_add, ← two_mul, pow_mul]
    norm_num
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h3

/--
@isnad1 id=eq.2h3v.s7.7e1723b3ee32 from=translated src=- shape=51268d77 vocab=1679c246
-/
theorem degsum {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) {m : Fin 3 →₀ ℕ} (hm : coeff m p ≠ 0) :
    m 0 + m 1 + m 2 = ℓ := by
  have h1 : Finsupp.weight (1 : Fin 3 → ℕ) m = ℓ := hp hm
  have h2 : m.degree = ℓ := by
    rw [Finsupp.degree_eq_weight_one]
    exact h1
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at h2
  exact h2

/--
@isnad1 id=and.4h5v.s11.ecd39761927b from=translated src=- shape=2a9fd45c vocab=5453bc67
-/
theorem facts (ε : Fin 3 → Fin 2) (S : ℕ → Submodule ℂ R3)
    (hS : ∀ ℓ, ∀ p : R3, p ∈ S ℓ →
      p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, pderiv i (pderiv i p)) = 0)
    (hsign : ∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        aeval (fun a : Fin 3 => C ((-1 : ℂ) ^ (σ a : ℕ)) * X a) p =
          C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p)
    (ℓ : ℕ) (p : R3) (hp : p ∈ S ℓ) (m : Fin 3 →₀ ℕ) (hm : coeff m p ≠ 0) :
    m 0 + m 1 + m 2 = ℓ ∧
    (m 0 + ((ε 0 : ℕ) + ℓ + ((ε 0 : ℕ) + (ε 1 : ℕ) + (ε 2 : ℕ)))) % 2 = 0 ∧
    (m 1 + ((ε 1 : ℕ) + ℓ + ((ε 0 : ℕ) + (ε 1 : ℕ) + (ε 2 : ℕ)))) % 2 = 0 ∧
    (m 2 + ((ε 2 : ℕ) + ℓ + ((ε 0 : ℕ) + (ε 1 : ℕ) + (ε 2 : ℕ)))) % 2 = 0 := by
  have hE : ∑ b : Fin 3, (ε b : ℕ) = (ε 0 : ℕ) + (ε 1 : ℕ) + (ε 2 : ℕ) := Fin.sum_univ_three _
  refine ⟨degsum (hS ℓ p hp).1 hm, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.even_iff, ← hE]
    exact parity ε S hsign ℓ p hp m hm _

/--
@isnad1 id=eq.1h2v.s7.28f0a1aa7815 from=translated src=- shape=4fb526a9 vocab=b37106dc
-/
theorem expand1 (p : R3) (m₁ : Fin 3 →₀ ℕ) (H : ∀ m, coeff m p ≠ 0 → m = m₁) :
    p = monomial m₁ (coeff m₁ p) := by
  classical
  refine MvPolynomial.ext _ _ (fun m => ?_)
  simp only [coeff_monomial]
  by_cases h0 : coeff m p = 0
  · rw [h0]
    split_ifs with h
    · rw [h, h0]
    · rfl
  · rcases H m h0 with rfl
    rw [ite_eq_left rfl]

/--
@isnad1 id=eq.4h4v.s9.d2e037a1d5de from=translated src=- shape=86d9ec98 vocab=703568af
-/
theorem expand3 (p : R3) (m₁ m₂ m₃ : Fin 3 →₀ ℕ) (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃)
    (H : ∀ m, coeff m p ≠ 0 → m = m₁ ∨ m = m₂ ∨ m = m₃) :
    p = monomial m₁ (coeff m₁ p) + monomial m₂ (coeff m₂ p) + monomial m₃ (coeff m₃ p) := by
  classical
  refine MvPolynomial.ext _ _ (fun m => ?_)
  simp only [coeff_add, coeff_monomial]
  by_cases h0 : coeff m p = 0
  · rw [h0]
    have hz : ∀ m' : Fin 3 →₀ ℕ, (if m' = m then coeff m' p else 0) = 0 := by
      intro m'
      split_ifs with h
      · rw [h, h0]
      · rfl
    rw [hz, hz, hz, add_zero, add_zero]
  · rcases H m h0 with rfl | rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_right (Ne.symm h12), ite_eq_right (Ne.symm h13), add_zero, add_zero]
    · rw [ite_eq_right h12, ite_eq_left rfl, ite_eq_right (Ne.symm h23), zero_add, add_zero]
    · rw [ite_eq_right h13, ite_eq_right h23, ite_eq_left rfl, zero_add, zero_add]

theorem eq_zero_of_coeff (p : R3) (H : ∀ m, coeff m p ≠ 0 → False) : p = 0 :=
  MvPolynomial.ext _ _ (fun m => by
    rw [coeff_zero]
    by_contra h
    exact H m h)

/--
@isnad1 id=eq.0h1v.s7.0d2b67548390 from=translated src=- shape=3544940b vocab=f9edec06
-/
theorem X_eq_monomial (i : Fin 3) : (X i : R3) = monomial (Finsupp.single i 1) 1 := by
  rw [← pow_one (X i), X_pow_eq_monomial]

/--
@isnad1 id=eq.0h2v.s8.4fd302651297 from=translated src=- shape=9fd5e0a9 vocab=c0d456a4
-/
theorem monomial_single_one (i : Fin 3) (c : ℂ) :
    monomial (Finsupp.single i 1) c = c • (X i : R3) := by
  rw [X_eq_monomial, smul_monomial, smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h2v.s8.6c2e00a29634 from=translated src=- shape=ee230233 vocab=67e9b4a8
-/
theorem monomial_single_two (i : Fin 3) (c : ℂ) :
    monomial (Finsupp.single i 2) c = C c * (X i : R3) ^ 2 := by
  rw [C_mul_X_pow_eq_monomial]

/--
@isnad1 id=eq.0h3v.s8.9e5eb6df9a3c from=translated src=- shape=40639fe8 vocab=e872a433
-/
theorem monomial_pair (i j : Fin 3) (c : ℂ) :
    monomial (Finsupp.single i 1 + Finsupp.single j 1) c = c • ((X i : R3) * X j) := by
  rw [X_eq_monomial, X_eq_monomial, monomial_mul_monomial, one_mul, smul_monomial, smul_eq_mul, mul_one]

/--
@isnad1 id=iff.0h2v.s8.e9a2f31c51fa from=translated src=- shape=65d35c57 vocab=38b32e33
-/
theorem finsupp_eq_iff (m n : Fin 3 →₀ ℕ) : m = n ↔ m 0 = n 0 ∧ m 1 = n 1 ∧ m 2 = n 2 := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    ext a
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
    rcases ha with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2

/--
@isnad1 id=eq.0h0v.s6.73073e467474 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s02_0 : (Finsupp.single (0 : Fin 3) 2 : Fin 3 →₀ ℕ) 0 = 2 := by simp
/--
@isnad1 id=eq.0h0v.s6.864cb6f6b536 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s02_1 : (Finsupp.single (0 : Fin 3) 2 : Fin 3 →₀ ℕ) 1 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.e2633d50170f from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s02_2 : (Finsupp.single (0 : Fin 3) 2 : Fin 3 →₀ ℕ) 2 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.072dca5254ff from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s12_0 : (Finsupp.single (1 : Fin 3) 2 : Fin 3 →₀ ℕ) 0 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.6b0ae8b81b78 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s12_1 : (Finsupp.single (1 : Fin 3) 2 : Fin 3 →₀ ℕ) 1 = 2 := by simp
/--
@isnad1 id=eq.0h0v.s6.05f884704a49 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s12_2 : (Finsupp.single (1 : Fin 3) 2 : Fin 3 →₀ ℕ) 2 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.b45297983427 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s22_0 : (Finsupp.single (2 : Fin 3) 2 : Fin 3 →₀ ℕ) 0 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.1fabd6c6612a from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s22_1 : (Finsupp.single (2 : Fin 3) 2 : Fin 3 →₀ ℕ) 1 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.3b0a5f77678a from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s22_2 : (Finsupp.single (2 : Fin 3) 2 : Fin 3 →₀ ℕ) 2 = 2 := by simp
/--
@isnad1 id=eq.0h0v.s6.6881450f7949 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s11_0 : (Finsupp.single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.45b0c4f25e62 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s11_1 : (Finsupp.single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 = 1 := by simp
/--
@isnad1 id=eq.0h0v.s6.d48b33e1ac40 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s11_2 : (Finsupp.single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 2 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.2424a1b34311 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s21_0 : (Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.d56094ceda84 from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s21_1 : (Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s6.fed8404e672e from=translated src=- shape=b5a1db64 vocab=14fe0282
-/
theorem s21_2 : (Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 2 = 1 := by simp
/--
@isnad1 id=eq.0h0v.s7.96ba4ce014e9 from=translated src=- shape=a383854d vocab=c7c9b90e
-/
theorem p01_0 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 1 := by simp
/--
@isnad1 id=eq.0h0v.s7.c78f8ae4c93b from=translated src=- shape=a383854d vocab=c7c9b90e
-/
theorem p01_1 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 = 1 := by simp
/--
@isnad1 id=eq.0h0v.s7.2f9e4e39b75a from=translated src=- shape=a383854d vocab=c7c9b90e
-/
theorem p01_2 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (1 : Fin 3) 1 : Fin 3 →₀ ℕ) 2 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s7.4c605c4dde06 from=translated src=- shape=a383854d vocab=c7c9b90e
-/
theorem p02_0 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 = 1 := by simp
/--
@isnad1 id=eq.0h0v.s7.7b290d312b65 from=translated src=- shape=a383854d vocab=c7c9b90e
-/
theorem p02_1 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 1 = 0 := by simp
/--
@isnad1 id=eq.0h0v.s7.65e01932a900 from=translated src=- shape=a383854d vocab=c7c9b90e
-/
theorem p02_2 : (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1 : Fin 3 →₀ ℕ) 2 = 1 := by simp

/--
@isnad1 id=eq.0h2v.s10.9e7a8053de7c from=translated src=- shape=9e22126e vocab=0eb9097a
-/
theorem lap_sq (c : ℂ) (i : Fin 3) :
    (∑ j : Fin 3, pderiv j (pderiv j (C c * (X i : R3) ^ 2))) = C (2 * c) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl <;>
  · simp only [Fin.sum_univ_three, pow_two, pderiv_mul, pderiv_C, pderiv_X_self,
      pderiv_X_of_ne ne01, pderiv_X_of_ne ne10, pderiv_X_of_ne ne02, pderiv_X_of_ne ne20,
      pderiv_X_of_ne ne12, pderiv_X_of_ne ne21, map_add, map_zero, Derivation.map_one_eq_zero,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    simp only [map_mul, map_ofNat]
    ring

/--
@isnad1 id=and.5h4v.s12.0377969c91dc from=translated src=- shape=633a9750 vocab=ba8622e3
-/
theorem main
    (ε : Fin 3 → Fin 2) (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hS : (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0))
    (hsign : (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p))
    (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀) :
    ((ε 0 = ε b₀ ∧ ε 0 = ε c₀) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2}) ∧
    ((ε 0 = ε b₀ ∧ ε 0 ≠ ε c₀) →
      S 0 = ⊥ ∧
          S 1 ≤ Submodule.span ℂ {(MvPolynomial.X c₀ : MvPolynomial (Fin 3) ℂ)} ∧
          S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X b₀ : MvPolynomial (Fin 3) ℂ)}) := by
  have F := facts ε S hS hsign
  have e0 : (ε 0 : ℕ) < 2 := (ε 0).isLt
  have e1 : (ε 1 : ℕ) < 2 := (ε 1).isLt
  have e2 : (ε 2 : ℕ) < 2 := (ε 2).isLt
  have hcases : (b₀ = 1 ∧ c₀ = 2) ∨ (b₀ = 2 ∧ c₀ = 1) := by
    revert hb₀ hc₀ hbc
    fin_cases b₀ <;> fin_cases c₀ <;> decide
  refine ⟨fun hI => ?_, fun hII => ?_⟩
  ·
    have hε : (ε 0 : ℕ) = (ε 1 : ℕ) ∧ (ε 0 : ℕ) = (ε 2 : ℕ) := by
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨congrArg Fin.val hI.1, congrArg Fin.val hI.2⟩
      · exact ⟨congrArg Fin.val hI.2, congrArg Fin.val hI.1⟩
    refine ⟨fun p hp => ?_, ?_, fun p hp => ?_⟩
    ·
      have h0 := (hS 0 p hp).1
      rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h0
      rw [Submodule.mem_span_singleton]
      refine ⟨p.coeff 0, ?_⟩
      rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]
      exact h0.symm
    ·
      rw [Submodule.eq_bot_iff]
      intro p hp
      refine eq_zero_of_coeff p (fun m hm => ?_)
      obtain ⟨hd, h0, h1, h2⟩ := F 1 p hp m hm
      omega
    ·
      have H : ∀ m, coeff m p ≠ 0 →
          m = Finsupp.single 0 2 ∨ m = Finsupp.single 1 2 ∨ m = Finsupp.single 2 2 := by
        intro m hm
        obtain ⟨hd, h0, h1, h2⟩ := F 2 p hp m hm
        rw [finsupp_eq_iff, finsupp_eq_iff, finsupp_eq_iff, s02_0, s02_1, s02_2, s12_0, s12_1,
          s12_2, s22_0, s22_1, s22_2]
        omega
      have h12 : Finsupp.single (0 : Fin 3) 2 ≠ Finsupp.single 1 2 := by
        rw [Ne, Finsupp.single_left_inj two_ne_zero]; decide
      have h13 : Finsupp.single (0 : Fin 3) 2 ≠ Finsupp.single 2 2 := by
        rw [Ne, Finsupp.single_left_inj two_ne_zero]; decide
      have h23 : Finsupp.single (1 : Fin 3) 2 ≠ Finsupp.single 2 2 := by
        rw [Ne, Finsupp.single_left_inj two_ne_zero]; decide
      have hexp := expand3 p _ _ _ h12 h13 h23 H
      set α := coeff (Finsupp.single (0 : Fin 3) 2) p with hα
      set β := coeff (Finsupp.single (1 : Fin 3) 2) p with hβ
      set γ := coeff (Finsupp.single (2 : Fin 3) 2) p with hγ
      rw [monomial_single_two, monomial_single_two, monomial_single_two] at hexp
      have hharm := (hS 2 p hp).2
      rw [hexp] at hharm
      simp only [map_add] at hharm
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, lap_sq, lap_sq, lap_sq, ← map_add,
        ← map_add, C_eq_zero] at hharm
      have hγ' : γ = -α - β := by linear_combination (1 / 2 : ℂ) * hharm
      rw [Submodule.mem_span_pair]
      refine ⟨α, β, ?_⟩
      rw [hexp, hγ', smul_eq_C_mul, smul_eq_C_mul, map_sub, map_neg]
      ring
  ·
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·
      have hε : (ε 0 : ℕ) = (ε 1 : ℕ) ∧ (ε 0 : ℕ) ≠ (ε 2 : ℕ) :=
        ⟨congrArg Fin.val hII.1, fun h => hII.2 (Fin.ext h)⟩
      refine ⟨?_, fun p hp => ?_, fun p hp => ?_⟩
      · rw [Submodule.eq_bot_iff]
        intro p hp
        refine eq_zero_of_coeff p (fun m hm => ?_)
        obtain ⟨hd, h0, h1, h2⟩ := F 0 p hp m hm
        omega
      · have H : ∀ m, coeff m p ≠ 0 → m = Finsupp.single 2 1 := by
          intro m hm
          obtain ⟨hd, h0, h1, h2⟩ := F 1 p hp m hm
          rw [finsupp_eq_iff, s21_0, s21_1, s21_2]
          omega
        rw [Submodule.mem_span_singleton]
        exact ⟨_, ((expand1 p _ H).trans (monomial_single_one _ _)).symm⟩
      · have H : ∀ m, coeff m p ≠ 0 → m = Finsupp.single 0 1 + Finsupp.single 1 1 := by
          intro m hm
          obtain ⟨hd, h0, h1, h2⟩ := F 2 p hp m hm
          rw [finsupp_eq_iff, p01_0, p01_1, p01_2]
          omega
        rw [Submodule.mem_span_singleton]
        exact ⟨_, ((expand1 p _ H).trans (monomial_pair _ _ _)).symm⟩
    ·
      have hε : (ε 0 : ℕ) = (ε 2 : ℕ) ∧ (ε 0 : ℕ) ≠ (ε 1 : ℕ) :=
        ⟨congrArg Fin.val hII.1, fun h => hII.2 (Fin.ext h)⟩
      refine ⟨?_, fun p hp => ?_, fun p hp => ?_⟩
      · rw [Submodule.eq_bot_iff]
        intro p hp
        refine eq_zero_of_coeff p (fun m hm => ?_)
        obtain ⟨hd, h0, h1, h2⟩ := F 0 p hp m hm
        omega
      · have H : ∀ m, coeff m p ≠ 0 → m = Finsupp.single 1 1 := by
          intro m hm
          obtain ⟨hd, h0, h1, h2⟩ := F 1 p hp m hm
          rw [finsupp_eq_iff, s11_0, s11_1, s11_2]
          omega
        rw [Submodule.mem_span_singleton]
        exact ⟨_, ((expand1 p _ H).trans (monomial_single_one _ _)).symm⟩
      · have H : ∀ m, coeff m p ≠ 0 → m = Finsupp.single 0 1 + Finsupp.single 2 1 := by
          intro m hm
          obtain ⟨hd, h0, h1, h2⟩ := F 2 p hp m hm
          rw [finsupp_eq_iff, p02_0, p02_1, p02_2]
          omega
        rw [Submodule.mem_span_singleton]
        exact ⟨_, ((expand1 p _ H).trans (monomial_pair _ _ _)).symm⟩

end

end WsC.SC

/--
@isnad1 id=and.5h4v.s12.0377969c91dc from=translated src=- shape=633a9750 vocab=ba8622e3
-/
theorem solution
    (ε : Fin 3 → Fin 2) (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hS : (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0))
    (hsign : (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p))
    (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀) :
    ((ε 0 = ε b₀ ∧ ε 0 = ε c₀) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} ∧
          S 1 = ⊥ ∧
          S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
            MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2}) ∧
    ((ε 0 = ε b₀ ∧ ε 0 ≠ ε c₀) →
      S 0 = ⊥ ∧
          S 1 ≤ Submodule.span ℂ {(MvPolynomial.X c₀ : MvPolynomial (Fin 3) ℂ)} ∧
          S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X b₀ : MvPolynomial (Fin 3) ℂ)}) := by
  exact WsC.SC.main ε S hS hsign b₀ c₀ hb₀ hc₀ hbc
