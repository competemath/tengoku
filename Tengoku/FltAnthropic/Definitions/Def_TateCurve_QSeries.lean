import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section Ultrametric

/--
@isnad1 id=eq.1h2v.s7.f9fe4aa24526 from=translated src=- shape=a441f58b vocab=4f4bd60c
-/
theorem nnnorm_one_sub_of_lt_one {x : K} (hx : ‖x‖₊ < 1) : ‖1 - x‖₊ = 1 := by
  have h : ‖(1 : K)‖₊ ≠ ‖-x‖₊ := by
    rw [nnnorm_neg, nnnorm_one]
    exact (ne_of_lt hx).symm
  rw [sub_eq_add_neg, nnnorm_add_eq_max_of_nnnorm_ne_nnnorm h, nnnorm_neg, nnnorm_one]
  exact max_eq_left hx.le

/--
@isnad1 id=ne.1h2v.s6.8d261845bd41 from=translated src=- shape=f6f1be3f vocab=4f4bd60c
-/
theorem one_sub_ne_zero_of_lt_one {x : K} (hx : ‖x‖₊ < 1) : (1 : K) - x ≠ 0 := by
  intro h
  have := nnnorm_one_sub_of_lt_one hx
  rw [h, nnnorm_zero] at this
  exact zero_ne_one this

/--
@isnad1 id=eq.1h3v.s7.c7b090522eac from=translated src=- shape=a58e18d0 vocab=4f4bd60c
-/
theorem nnnorm_eq_of_nnnorm_sub_lt {a b : K} (h : ‖a - b‖₊ < ‖b‖₊) : ‖a‖₊ = ‖b‖₊ := by
  have hne : ‖a - b‖₊ ≠ ‖b‖₊ := ne_of_lt h
  calc ‖a‖₊ = ‖a - b + b‖₊ := by rw [sub_add_cancel]
    _ = max ‖a - b‖₊ ‖b‖₊ := nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hne
    _ = ‖b‖₊ := max_eq_right h.le

/--
@isnad1 id=le.2h4v.s7.ce0d4858064f from=translated src=- shape=12fbd50d vocab=028e0e38
-/
theorem nnnorm_add_le_of_le {a b : K} {C : ℝ≥0} (ha : ‖a‖₊ ≤ C) (hb : ‖b‖₊ ≤ C) :
    ‖a + b‖₊ ≤ C :=
  (nnnorm_add_le_max a b).trans (max_le ha hb)

end Ultrametric

section CoeffSum

variable (c : ℕ → ℕ) (q : K)

def term (n : ℕ) : K := (c n : K) * (q ^ n / (1 - q ^ n))

/--
@isnad1 id=eq.0h3v.s5.fae38db901c4 from=translated src=- shape=109a0bff vocab=d9ddbe02
-/
@[simp] theorem term_zero : term c q 0 = 0 := by simp [term]

/--
@isnad1 id=eq.0h3v.s7.2dd0e5e472e2 from=translated src=- shape=d6084ea7 vocab=b0e52c26
-/
theorem term_one : term c q 1 = (c 1 : K) * (q / (1 - q)) := by simp [term]

variable {q}

/--
@isnad1 id=le.1h4v.s7.5762df7bc404 from=translated src=- shape=cdef26e7 vocab=27f8e142
-/
theorem nnnorm_term_le (hq : ‖q‖₊ < 1) (n : ℕ) : ‖term c q n‖₊ ≤ ‖q‖₊ ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hqn : ‖q ^ n‖₊ < 1 := by
    rw [nnnorm_pow]
    exact pow_lt_one₀ zero_le hq hn.ne'
  calc ‖term c q n‖₊ = ‖(c n : K)‖₊ * (‖q ^ n‖₊ / ‖1 - q ^ n‖₊) := by
        rw [term, nnnorm_mul, nnnorm_div]
    _ = ‖(c n : K)‖₊ * ‖q‖₊ ^ n := by rw [nnnorm_one_sub_of_lt_one hqn, div_one, nnnorm_pow]
    _ ≤ 1 * ‖q‖₊ ^ n := by
        gcongr
        exact nnnorm_natCast_le_one K (c n)
    _ = ‖q‖₊ ^ n := one_mul _

/--
@isnad1 id=le.1h4v.s6.539bf235f009 from=translated src=- shape=96878e4b vocab=6c65cbb8
-/
theorem nnnorm_term_le_nnnorm (hq : ‖q‖₊ < 1) (n : ℕ) : ‖term c q n‖₊ ≤ ‖q‖₊ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc ‖term c q n‖₊ ≤ ‖q‖₊ ^ n := nnnorm_term_le c hq n
    _ ≤ ‖q‖₊ ^ 1 := pow_le_pow_of_le_one zero_le hq.le hn
    _ = ‖q‖₊ := pow_one _

variable [CompleteSpace K]

/--
@isnad1 id=tendsto.1h3v.s6.643894d01391 from=translated src=- shape=08c76871 vocab=ade81a41
-/
theorem tendsto_term (hq : ‖q‖₊ < 1) :
    Tendsto (term c q) cofinite (nhds 0) := by
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) ?_)
  · exact_mod_cast nnnorm_term_le c hq n
  · exact_mod_cast hq

/--
@isnad1 id=summable.1h3v.s6.d0d4bf18e79f from=translated src=- shape=2527e633 vocab=330eb1ee
-/
theorem summable_term (hq : ‖q‖₊ < 1) : Summable (term c q) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_term c hq)

variable (q) in

noncomputable def coeffSum : K := ∑' n, term c q n

/--
@isnad1 id=le.1h3v.s7.749e16460f59 from=translated src=- shape=465f06dd vocab=4e6a2585
-/
theorem nnnorm_coeffSum_le (hq : ‖q‖₊ < 1) : ‖coeffSum c q‖₊ ≤ ‖q‖₊ :=
  nnnorm_tsum_le_of_forall_le (nnnorm_term_le_nnnorm c hq)

/--
@isnad1 id=le.1h3v.s7.ef4cbeddd549 from=translated src=- shape=e1899a38 vocab=35e3afc7
-/
theorem nnnorm_coeffSum_sub_le (hq : ‖q‖₊ < 1) :
    ‖coeffSum c q - (c 1 : K) * q‖₊ ≤ ‖q‖₊ ^ 2 := by
  have hq1 : (1 : K) - q ≠ 0 := one_sub_ne_zero_of_lt_one hq

  have hsplit : coeffSum c q = term c q 1 + ∑' n, ite (n = 1) 0 (term c q n) :=
    (summable_term c hq).tsum_eq_add_tsum_ite 1

  have htail : ‖∑' n, ite (n = 1) 0 (term c q n)‖₊ ≤ ‖q‖₊ ^ 2 := by
    refine nnnorm_tsum_le_of_forall_le fun n => ?_
    rcases eq_or_ne n 1 with rfl | hn
    · simp
    rw [ite_eq_right hn]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp

    have h2n : 2 ≤ n := by omega
    calc ‖term c q n‖₊ ≤ ‖q‖₊ ^ n := nnnorm_term_le c hq n
      _ ≤ ‖q‖₊ ^ 2 := pow_le_pow_of_le_one zero_le hq.le h2n

  have hlead : ‖term c q 1 - (c 1 : K) * q‖₊ ≤ ‖q‖₊ ^ 2 := by
    have hkey : term c q 1 - (c 1 : K) * q = (c 1 : K) * (q ^ 2 / (1 - q)) := by
      rw [term_one]
      field_simp
      ring
    rw [hkey, nnnorm_mul, nnnorm_div, nnnorm_one_sub_of_lt_one hq, div_one, nnnorm_pow]
    calc ‖(c 1 : K)‖₊ * ‖q‖₊ ^ 2 ≤ 1 * ‖q‖₊ ^ 2 := by
          gcongr
          exact nnnorm_natCast_le_one K (c 1)
      _ = ‖q‖₊ ^ 2 := one_mul _

  calc ‖coeffSum c q - (c 1 : K) * q‖₊
      = ‖(term c q 1 - (c 1 : K) * q) + ∑' n, ite (n = 1) 0 (term c q n)‖₊ := by
        rw [hsplit]; ring_nf
    _ ≤ ‖q‖₊ ^ 2 := nnnorm_add_le_of_le hlead htail

end CoeffSum

section Coefficients

variable [CompleteSpace K]

def b (n : ℕ) : ℕ := (5 * n ^ 3 + 7 * n ^ 5) / 12

/--
@isnad1 id=dvd.0h1v.s6.17f9b3c47b47 from=translated src=- shape=dc10f5a2 vocab=0eadfadb
-/
theorem twelve_dvd (n : ℕ) : 12 ∣ 5 * n ^ 3 + 7 * n ^ 5 := by
  have : ((5 * n ^ 3 + 7 * n ^ 5 : ℕ) : ZMod 12) = 0 := by
    push_cast
    generalize (n : ZMod 12) = x
    revert x
    decide
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/--
@isnad1 id=eq.0h1v.s6.2876b59cd2a6 from=translated src=- shape=a20f6009 vocab=7b659423
-/
theorem b_mul_twelve (n : ℕ) : b n * 12 = 5 * n ^ 3 + 7 * n ^ 5 :=
  Nat.div_mul_cancel (twelve_dvd n)

/--
@isnad1 id=eq.0h0v.s3.0efdba83a6b0 from=translated src=- shape=3c26ae4f vocab=6f198b74
-/
@[simp] theorem b_one : b 1 = 1 := by norm_num [b]

variable (q : K)

noncomputable def a₄ : K := -(coeffSum (fun n => 5 * n ^ 3) q)

noncomputable def a₆ : K := -(coeffSum b q)

variable {q}

/--
@isnad1 id=le.1h2v.s6.73f0c59e0f27 from=translated src=- shape=449e3791 vocab=644c90bc
-/
theorem nnnorm_a₄_le (hq : ‖q‖₊ < 1) : ‖a₄ q‖₊ ≤ ‖q‖₊ := by
  rw [a₄, nnnorm_neg]
  exact nnnorm_coeffSum_le _ hq

/--
@isnad1 id=le.1h2v.s6.fc14081dce8e from=translated src=- shape=449e3791 vocab=43b21d6a
-/
theorem nnnorm_a₆_le (hq : ‖q‖₊ < 1) : ‖a₆ q‖₊ ≤ ‖q‖₊ := by
  rw [a₆, nnnorm_neg]
  exact nnnorm_coeffSum_le _ hq

/--
@isnad1 id=le.1h2v.s7.0abc3be6a7ed from=translated src=- shape=42fbb0b3 vocab=e81ee0c9
-/
theorem nnnorm_a₆_add_le (hq : ‖q‖₊ < 1) : ‖a₆ q + q‖₊ ≤ ‖q‖₊ ^ 2 := by
  have h := nnnorm_coeffSum_sub_le (K := K) b hq
  rw [b_one, Nat.cast_one, one_mul] at h
  calc ‖a₆ q + q‖₊ = ‖-(coeffSum b q - q)‖₊ := by congr 1; rw [a₆]; ring
    _ = ‖coeffSum b q - q‖₊ := nnnorm_neg _
    _ ≤ ‖q‖₊ ^ 2 := h

end Coefficients

section Curve

variable (q : K)

noncomputable def curve : WeierstrassCurve K := ⟨1, 0, 0, a₄ q, a₆ q⟩

/--
@isnad1 id=eq.0h2v.s5.bddd23bbc25f from=translated src=- shape=e224aef9 vocab=47bcc711
-/
@[simp] theorem curve_a₁ : (curve q).a₁ = 1 := rfl
/--
@isnad1 id=eq.0h2v.s5.fd23838287d9 from=translated src=- shape=e224aef9 vocab=939e7bfa
-/
@[simp] theorem curve_a₂ : (curve q).a₂ = 0 := rfl
/--
@isnad1 id=eq.0h2v.s5.49ec61566cd7 from=translated src=- shape=e224aef9 vocab=2660406d
-/
@[simp] theorem curve_a₃ : (curve q).a₃ = 0 := rfl
/--
@isnad1 id=eq.0h2v.s5.b45313c71fac from=translated src=- shape=9df816d8 vocab=bda4447e
-/
@[simp] theorem curve_a₄ : (curve q).a₄ = a₄ q := rfl
/--
@isnad1 id=eq.0h2v.s5.b6e9c51b1ebb from=translated src=- shape=9df816d8 vocab=8450b2d3
-/
@[simp] theorem curve_a₆ : (curve q).a₆ = a₆ q := rfl

/--
@isnad1 id=eq.0h2v.s8.1d7edff3a3e9 from=translated src=- shape=e00c621e vocab=13272413
-/
theorem curve_Δ :
    (curve q).Δ = -a₆ q + a₄ q ^ 2 - 64 * a₄ q ^ 3 - 432 * a₆ q ^ 2 + 72 * a₄ q * a₆ q := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  ring

/--
@isnad1 id=eq.0h2v.s7.d24b88e40ae0 from=translated src=- shape=80eb1243 vocab=15923799
-/
theorem curve_c₄ : (curve q).c₄ = 1 - 48 * a₄ q := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curve_a₁, curve_a₂,
    curve_a₃, curve_a₄]
  ring

variable {q} [CompleteSpace K]

end Curve

end TateCurve
