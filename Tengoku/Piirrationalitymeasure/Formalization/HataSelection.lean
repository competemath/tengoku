import Tengoku.Piirrationalitymeasure.Formalization.Hata

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The nonvanishing-index step in Hata's argument.  Exponential upper and lower
bounds are stated in their eventual form; this is the exact form used after
passing from the two asymptotic rate statements.
-/

namespace PiIrrationality

open Filter
open scoped Topology

theorem exists_first_nonzero_after
    {A : ℕ → ℤ} {N : ℕ}
    (hinf : ∀ n : ℕ, ∃ m : ℕ, n < m ∧ A m ≠ 0)
    (hN : A N = 0) :
    ∃ M : ℕ, N < M ∧ A M ≠ 0 ∧ A (M - 1) = 0 := by
  obtain ⟨m, hmN, hmne⟩ := hinf N
  let P : ℕ → Prop := fun m => N < m ∧ A m ≠ 0
  have hP : ∃ m, P m := ⟨m, hmN, hmne⟩
  let M : ℕ := Nat.find hP
  have hMspec : P M := Nat.find_spec hP
  have hMpos : 0 < M := by omega
  have hpredlt : M - 1 < M := Nat.sub_lt hMpos (by decide)
  have hpred : ¬ P (M - 1) := Nat.find_min hP hpredlt
  have hMgt : N < M := hMspec.1
  have hMne : A M ≠ 0 := hMspec.2
  have hpredzero : A (M - 1) = 0 := by
    by_cases hNp : N < M - 1
    · by_contra hne
      exact hpred ⟨hNp, hne⟩
    · have heq : M - 1 = N := by omega
      simpa [heq] using hN
  exact ⟨M, hMgt, hMne, hpredzero⟩

theorem hata_integer_not_eventually_zero
    {theta : ℝ} {U V : ℕ → ℤ} {p : ℤ} {q : ℕ}
    {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau)
    (hVlower : ∀ᶠ n : ℕ in atTop,
      Real.exp (sigma * (n : ℝ)) ≤ |(V n : ℝ)|)
    (hLupper : ∀ᶠ n : ℕ in atTop,
      |linearForm theta (U n) (V n)| ≤ Real.exp (-tau * (n : ℝ)))
    (hdelta : hataDelta theta p q ≠ 0) :
    ¬ (∀ᶠ n : ℕ in atTop, hataInteger (U n) (V n) p q = 0) := by
  intro hzero
  have hgamma : 0 < sigma + tau := by linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlin : Tendsto (fun n : ℕ => (sigma + tau) * (n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hgamma).2 hnat
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(sigma + tau) * (n : ℝ)))
      atTop (𝓝 0) := by
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    change Tendsto (fun n : ℕ => Real.exp (-((sigma + tau) * (n : ℝ))))
      atTop (𝓝 0) at hcomp
    convert hcomp using 1
    funext n
    congr 1
    ring
  have htail : Tendsto (fun n : ℕ =>
      (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ))) atTop (𝓝 0) :=
    by simpa using hexp.const_mul (q : ℝ)
  have hdelta_pos : 0 < |hataDelta theta p q| := abs_pos.mpr hdelta
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ)) <
        |hataDelta theta p q| :=
    htail.eventually (Iio_mem_nhds hdelta_pos)
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hzero, hVlower, hLupper, hsmall] with n hn hVn hLn hsn
    have hVpos : 0 < |(V n : ℝ)| := by
      have hexppos : 0 < Real.exp (sigma * (n : ℝ)) := Real.exp_pos _
      exact lt_of_lt_of_le hexppos hVn
    have hVne : V n ≠ 0 := by
      intro hz
      have : (V n : ℝ) = 0 := by simp [hz]
      simp [this] at hVpos
    have hratio :
        (q : ℝ) * |linearForm theta (U n) (V n)| / |(V n : ℝ)| ≤
          (q : ℝ) * Real.exp (-tau * (n : ℝ)) /
            Real.exp (sigma * (n : ℝ)) := by
      apply (div_le_div_iff₀ hVpos (Real.exp_pos _)).2
      have hq : 0 ≤ (q : ℝ) := by positivity
      have hLn0 : 0 ≤ |linearForm theta (U n) (V n)| := abs_nonneg _
      have hVn0 : 0 ≤ |(V n : ℝ)| := abs_nonneg _
      have hexp0 : 0 ≤ Real.exp (-tau * (n : ℝ)) := (Real.exp_pos _).le
      calc
        (q : ℝ) * |linearForm theta (U n) (V n)| *
            Real.exp (sigma * (n : ℝ)) ≤
            (q : ℝ) * Real.exp (-tau * (n : ℝ)) *
              Real.exp (sigma * (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLn hq) (Real.exp_pos _).le
        _ ≤ (q : ℝ) * Real.exp (-tau * (n : ℝ)) * |(V n : ℝ)| := by
          exact mul_le_mul_of_nonneg_left hVn
            (mul_nonneg hq hexp0)
    have hratio' : |hataDelta theta p q| ≤
        (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ)) := by
      have hdeltaEq := hata_delta_abs_eq_of_integer_zero theta (U n) (V n) p q hVne hn
      have hexp : Real.exp (-tau * (n : ℝ)) /
          Real.exp (sigma * (n : ℝ)) =
          Real.exp (-(sigma + tau) * (n : ℝ)) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      calc
        |hataDelta theta p q| =
            |(q : ℝ) * linearForm theta (U n) (V n)| / |(V n : ℝ)| := hdeltaEq
        _ = (q : ℝ) * |linearForm theta (U n) (V n)| / |(V n : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ))]
        _ ≤ (q : ℝ) * Real.exp (-tau * (n : ℝ)) /
            Real.exp (sigma * (n : ℝ)) := hratio
        _ = (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ)) := by
          calc
            (q : ℝ) * Real.exp (-tau * (n : ℝ)) /
                Real.exp (sigma * (n : ℝ)) =
                (q : ℝ) * (Real.exp (-tau * (n : ℝ)) /
                  Real.exp (sigma * (n : ℝ))) := by ring
            _ = (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ)) := by rw [hexp]
    exact (not_lt_of_ge hratio') hsn
  obtain ⟨n, hn⟩ := hfalse.exists
  exact hn

theorem hata_exists_first_nonzero_after
    {theta : ℝ} {U V : ℕ → ℤ} {p : ℤ} {q : ℕ}
    {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau)
    (hVlower : ∀ᶠ n : ℕ in atTop,
      Real.exp (sigma * (n : ℝ)) ≤ |(V n : ℝ)|)
    (hLupper : ∀ᶠ n : ℕ in atTop,
      |linearForm theta (U n) (V n)| ≤ Real.exp (-tau * (n : ℝ)))
    (hdelta : hataDelta theta p q ≠ 0)
    {N : ℕ} (hN : hataInteger (U N) (V N) p q = 0) :
    ∃ M : ℕ, N < M ∧
      hataInteger (U M) (V M) p q ≠ 0 ∧
      hataInteger (U (M - 1)) (V (M - 1)) p q = 0 := by
  have hnot := hata_integer_not_eventually_zero hsigma htau hVlower hLupper hdelta
  have hfreq : ∃ᶠ n : ℕ in atTop,
      hataInteger (U n) (V n) p q ≠ 0 := by
    exact Filter.not_eventually.mp hnot
  have hinf : ∀ n : ℕ, ∃ m : ℕ, n < m ∧
      hataInteger (U m) (V m) p q ≠ 0 := by
    intro n
    obtain ⟨m, hnm, hm⟩ := frequently_atTop.mp hfreq (n + 1)
    exact ⟨m, by omega, hm⟩
  exact exists_first_nonzero_after hinf hN

theorem hata_zero_index_upper_bound
    {theta : ℝ} {U V : ℤ} {p : ℤ} {q : ℕ} {n : ℕ}
    {sigma tau : ℝ}
    (hA : hataInteger U V p q = 0)
    (hVlower : Real.exp (sigma * (n : ℝ)) ≤ |(V : ℝ)|)
    (hLupper : |linearForm theta U V| ≤ Real.exp (-tau * (n : ℝ))) :
    |hataDelta theta p q| ≤
      (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ)) := by
  have hVpos : 0 < |(V : ℝ)| := by
    have hexppos : 0 < Real.exp (sigma * (n : ℝ)) := Real.exp_pos _
    exact lt_of_lt_of_le hexppos hVlower
  have hVne : V ≠ 0 := by
    intro hz
    have : (V : ℝ) = 0 := by simp [hz]
    simp [this] at hVpos
  have hratio :
      (q : ℝ) * |linearForm theta U V| / |(V : ℝ)| ≤
        (q : ℝ) * Real.exp (-tau * (n : ℝ)) /
          Real.exp (sigma * (n : ℝ)) := by
    apply (div_le_div_iff₀ hVpos (Real.exp_pos _)).2
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hLn0 : 0 ≤ |linearForm theta U V| := abs_nonneg _
    have hexp0 : 0 ≤ Real.exp (-tau * (n : ℝ)) := (Real.exp_pos _).le
    calc
      (q : ℝ) * |linearForm theta U V| * Real.exp (sigma * (n : ℝ)) ≤
          (q : ℝ) * Real.exp (-tau * (n : ℝ)) * Real.exp (sigma * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLupper hq) (Real.exp_pos _).le
      _ ≤ (q : ℝ) * Real.exp (-tau * (n : ℝ)) * |(V : ℝ)| := by
        exact mul_le_mul_of_nonneg_left hVlower
          (mul_nonneg hq hexp0)
  have hdeltaEq := hata_delta_abs_eq_of_integer_zero theta U V p q hVne hA
  calc
    |hataDelta theta p q| =
        |(q : ℝ) * linearForm theta U V| / |(V : ℝ)| := hdeltaEq
    _ = (q : ℝ) * |linearForm theta U V| / |(V : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ))]
    _ ≤ (q : ℝ) * Real.exp (-tau * (n : ℝ)) /
        Real.exp (sigma * (n : ℝ)) := hratio
    _ = (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ)) := by
      calc
        (q : ℝ) * Real.exp (-tau * (n : ℝ)) /
            Real.exp (sigma * (n : ℝ)) =
            (q : ℝ) * (Real.exp (-tau * (n : ℝ)) /
              Real.exp (sigma * (n : ℝ))) := by ring
        _ = (q : ℝ) * Real.exp (-(sigma + tau) * (n : ℝ)) := by
          rw [← Real.exp_sub]
          congr 1
          ring

theorem hata_zero_predecessor_exp_bound
    {D q gamma : ℝ} {m : ℕ} (hq : 0 < q) (hD : 0 < D)
    (hgamma : 0 < gamma)
    (hzero : D ≤ q * Real.exp (-gamma * ((m : ℝ) - 1))) :
    Real.exp (m : ℝ) ≤
      Real.exp 1 * (q / D) ^ (1 / gamma) := by
  have hright : 0 < q * Real.exp (-gamma * ((m : ℝ) - 1)) :=
    mul_pos hq (Real.exp_pos _)
  have hlogzero : Real.log D ≤
      Real.log q + (-gamma * ((m : ℝ) - 1)) := by
    have hlog := Real.log_le_log hD hzero
    rw [Real.log_mul hq.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    exact hlog
  have hlogdiv : Real.log (q / D) = Real.log q - Real.log D :=
    Real.log_div hq.ne' hD.ne'
  have hm : (m : ℝ) ≤ 1 + Real.log (q / D) / gamma := by
    rw [hlogdiv]
    rw [show 1 + (Real.log q - Real.log D) / gamma =
      (gamma + (Real.log q - Real.log D)) / gamma by field_simp]
    apply (le_div_iff₀ hgamma).2
    nlinarith [hlogzero]
  calc
    Real.exp (m : ℝ) ≤ Real.exp (1 + Real.log (q / D) / gamma) :=
      Real.exp_le_exp.mpr hm
    _ = Real.exp 1 * (q / D) ^ (1 / gamma) := by
      rw [Real.exp_add, Real.rpow_def_of_pos (div_pos hq hD)]
      congr 1
      ring

end PiIrrationality
