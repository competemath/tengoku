import Tengoku.EocLeanVerification.EOC.PeriodicCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# BoundedDriftCore — Mathlib-free core of the bounded-drift realizer escape theorem

Pure ℕ arithmetic, Lean core only. Main theorem `no_injective_orbit_of_lower_drift`:
an injective positive sequence `m` obeying the exact accelerated step
`2^(d i) * m (i+1) = 3 * m i + 1` cannot satisfy an integer lower drift bound
`3^j ≤ 2^G * 2^(s_j)` for all `j`.

Mechanism: the exact product identity `2^{s_j} m_j ∏_{i<j} 3m_i = 3^j m_0 ∏_{i<j}(3m_i+1)`,
the lower drift bound, and a dyadic-level packing bound
`2^{L+1} ∏_{i<N}(3m_i+1) ≤ 3^{L+1} ∏_{i<N} 3m_i` (for `N ≤ 2^L`, using injectivity) give
`m_j ≤ 2^G m_0 (3/2)^{L+1}` for all `j < N`; pigeonhole on `N` distinct values then bounds `N`.
-/

namespace EOC.BoundedDriftCore
open EOC.PeriodicCore

/-! ### Range products, filtered products, filtered counts -/

def pr (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => pr f n * f n

def prf (p : Nat → Bool) (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => prf p f n * (if p n then f n else 1)

def cnt (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt p n + (if p n then 1 else 0)

/--
@isnad1 id=eq.0h1v.s4.f3ade80b778e from=translated src=- shape=b298c1f9 vocab=8c96c508
-/
@[simp] theorem pr_zero (f : Nat → Nat) : pr f 0 = 1 := rfl
/--
@isnad1 id=eq.0h2v.s5.36e6afae111f from=translated src=- shape=915b512a vocab=e6bac8ca
-/
theorem pr_succ (f : Nat → Nat) (n : Nat) : pr f (n + 1) = pr f n * f n := rfl
/--
@isnad1 id=eq.0h2v.s4.04498d3a9eab from=translated src=- shape=d8ee755c vocab=11b26540
-/
@[simp] theorem prf_zero (p : Nat → Bool) (f : Nat → Nat) : prf p f 0 = 1 := rfl
/--
@isnad1 id=eq.0h3v.s5.0986b7bf0dee from=translated src=- shape=426eb46a vocab=34ba43bd
-/
theorem prf_succ (p : Nat → Bool) (f : Nat → Nat) (n : Nat) :
    prf p f (n + 1) = prf p f n * (if p n then f n else 1) := rfl
/--
@isnad1 id=eq.0h1v.s4.14cef4414732 from=translated src=- shape=70127e46 vocab=e7a76fce
-/
@[simp] theorem cnt_zero (p : Nat → Bool) : cnt p 0 = 0 := rfl
/--
@isnad1 id=eq.0h2v.s5.b1a76cf8e1e3 from=translated src=- shape=72396c03 vocab=efd959e8
-/
theorem cnt_succ (p : Nat → Bool) (n : Nat) : cnt p (n + 1) = cnt p n + (if p n then 1 else 0) := rfl

/--
@isnad1 id=le.1h2v.s4.e61a9dd8bffe from=translated src=- shape=8c2ee0a1 vocab=a74fab7d
-/
theorem pr_pos (f : Nat → Nat) (hf : ∀ i, 1 ≤ f i) : ∀ n, 1 ≤ pr f n := by
  intro n; induction n with
  | zero => simp
  | succ n ih => rw [pr_succ]; exact Nat.mul_le_mul ih (hf n)

/--
@isnad1 id=le.1h3v.s5.8a364fb36864 from=translated src=- shape=e787352e vocab=6c78686c
-/
theorem prf_pos (p : Nat → Bool) (f : Nat → Nat) (hf : ∀ i, 1 ≤ f i) : ∀ n, 1 ≤ prf p f n := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    rw [prf_succ]
    cases hp : p n
    · simpa using ih
    · simp only [ite_true]; exact Nat.mul_le_mul ih (hf n)

/--
@isnad1 id=eq.0h2v.s4.f5d6a36d5e24 from=translated src=- shape=ead31cbe vocab=9177f18c
-/
theorem pr_eq_prf_true (f : Nat → Nat) : ∀ n, pr f n = prf (fun _ => true) f n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => rw [pr_succ, prf_succ, ih]; simp

/-- Splitting a range product at `j`.
@isnad1 id=eq.0h3v.s5.81cf43cbe52c from=translated src=- shape=2833a28c vocab=e6bac8ca
-/
theorem pr_add (f : Nat → Nat) (j : Nat) : ∀ t, pr f (j + t) = pr f j * pr (fun i => f (j + i)) t := by
  intro t; induction t with
  | zero => simp
  | succ t ih =>
    rw [show j + (t + 1) = (j + t) + 1 from by omega, pr_succ, ih, pr_succ, Nat.mul_assoc]

/-- Termwise comparison of range products.
@isnad1 id=le.1h3v.s5.d0d0e12ade9e from=translated src=- shape=f6826cbd vocab=85308d1b
-/
theorem pr_le_pr (f g : Nat → Nat) (n : Nat) (h : ∀ i, i < n → f i ≤ g i) : pr f n ≤ pr g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pr_succ, pr_succ]
    exact Nat.mul_le_mul (ih (fun i hi => h i (by omega))) (h n (by omega))

/--
@isnad1 id=eq.1h3v.s6.845cc8c7764b from=translated src=- shape=a916873a vocab=e19c8fa9
-/
theorem ite_or_split (b c : Bool) (x : Nat) (h : ¬ (b = true ∧ c = true)) :
    (if (b || c) then x else 1) = (if b then x else 1) * (if c then x else 1) := by
  cases b <;> cases c
  · simp
  · simp
  · simp
  · exact absurd ⟨rfl, rfl⟩ h

/--
@isnad1 id=eq.1h2v.s6.43bbfc4d5a7a from=translated src=- shape=162bf0f0 vocab=d33150ef
-/
theorem ite_or_add (b c : Bool) (h : ¬ (b = true ∧ c = true)) :
    (if (b || c) then 1 else 0) = (if b then 1 else 0) + (if c then 1 else 0) := by
  cases b <;> cases c
  · simp
  · simp
  · simp
  · exact absurd ⟨rfl, rfl⟩ h

/--
@isnad1 id=eq.1h3v.s5.4626fbd6b21c from=translated src=- shape=df050d20 vocab=6c04ea4c
-/
theorem decide_split (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] (h : P ↔ Q ∨ R) :
    decide P = (decide Q || decide R) := by
  by_cases hq : Q <;> by_cases hr : R <;> simp [hq, hr, h]

/--
@isnad1 id=eq.1h3v.s5.fc00d0a3c4d7 from=translated src=- shape=0462fbcc vocab=e3dbe8e6
-/
theorem prf_of_false (p : Nat → Bool) (f : Nat → Nat) :
    ∀ n, (∀ i, i < n → p i = false) → prf p f n = 1 := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [prf_succ, ih (fun i hi => h i (by omega)), h n (by omega)]
    simp

/-- Splitting a filtered product along a disjoint decomposition of the predicate.
@isnad1 id=eq.2h5v.s6.d4670b7e13e2 from=translated src=- shape=0f7e5842 vocab=43ba65e3
-/
theorem prf_split (p q r : Nat → Bool) (f : Nat → Nat)
    (hpqr : ∀ i, p i = (q i || r i)) (hdisj : ∀ i, ¬ (q i = true ∧ r i = true)) :
    ∀ n, prf p f n = prf q f n * prf r f n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    rw [prf_succ, prf_succ, prf_succ, ih, hpqr n, ite_or_split _ _ _ (hdisj n)]
    ac_rfl

/--
@isnad1 id=eq.2h4v.s6.c79861e88450 from=translated src=- shape=273ed597 vocab=49396f78
-/
theorem cnt_split (p q r : Nat → Bool)
    (hpqr : ∀ i, p i = (q i || r i)) (hdisj : ∀ i, ¬ (q i = true ∧ r i = true)) :
    ∀ n, cnt p n = cnt q n + cnt r n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt_succ, cnt_succ, cnt_succ, ih, hpqr n, ite_or_add _ _ (hdisj n)]
    omega

/--
@isnad1 id=le.0h2v.s3.70bac0efbfd0 from=translated src=- shape=5ba77e19 vocab=5a0de110
-/
theorem cnt_le (p : Nat → Bool) : ∀ n, cnt p n ≤ n := by
  intro n; induction n with
  | zero => simp
  | succ n ih => rw [cnt_succ]; cases p n <;> simp <;> omega

/--
@isnad1 id=eq.1h2v.s4.ccffbacb845f from=translated src=- shape=783da709 vocab=1c49e3ab
-/
theorem cnt_of_false (p : Nat → Bool) : ∀ n, (∀ i, i < n → p i = false) → cnt p n = 0 := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [cnt_succ, ih (fun i hi => h i (by omega)), h n (by omega)]
    simp

/--
@isnad1 id=eq.1h2v.s4.2d31a5efd0d5 from=translated src=- shape=ad3a32b1 vocab=ba47f00c
-/
theorem cnt_of_true (p : Nat → Bool) : ∀ n, (∀ i, i < n → p i = true) → cnt p n = n := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [cnt_succ, ih (fun i hi => h i (by omega)), h n (by omega)]
    simp

/-! ### Injectivity ⇒ counting -/

/-- An injective sequence takes the value `b` at most once among indices `< n`.
@isnad1 id=le.1h3v.s5.3425292259c0 from=translated src=- shape=eb7b1948 vocab=3a0af4d4
-/
theorem cnt_eq_le_one (m : Nat → Nat) (hinj : ∀ i j, m i = m j → i = j) (b : Nat) :
    ∀ n, cnt (fun i => decide (m i = b)) n ≤ 1 := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    rw [cnt_succ]
    by_cases hb : m n = b
    · have hzero : cnt (fun i => decide (m i = b)) n = 0 := by
        apply cnt_of_false
        intro i hi
        have : m i ≠ b := fun h => by
          have := hinj i n (h.trans hb.symm); omega
        simp [this]
      rw [hzero]; simp [hb]
    · simp [hb]; exact ih

/-- An injective sequence has at most `b - a` indices `< n` with value in `[a, b)`.
@isnad1 id=le.1h4v.s6.c45c23121350 from=translated src=- shape=196a911d vocab=86efb846
-/
theorem cnt_range_le (m : Nat → Nat) (hinj : ∀ i j, m i = m j → i = j) (a : Nat) :
    ∀ b n, cnt (fun i => decide (a ≤ m i ∧ m i < b)) n ≤ b - a := by
  intro b
  induction b with
  | zero =>
    intro n
    rw [cnt_of_false]
    · simp
    · intro i _; apply decide_eq_false; omega
  | succ b ih =>
    intro n
    rcases Nat.lt_or_ge b a with hab | hab
    · rw [cnt_of_false]
      · simp
      · intro i _; apply decide_eq_false; omega
    · have hsplit := cnt_split
        (fun i => decide (a ≤ m i ∧ m i < b + 1))
        (fun i => decide (a ≤ m i ∧ m i < b))
        (fun i => decide (m i = b))
        (fun i => decide_split _ _ _ (by omega))
        (fun i => by simp only [decide_eq_true_eq]; omega) n
      rw [hsplit]
      have h1 := ih n
      have h2 := cnt_eq_le_one m hinj b n
      omega

/-! ### The level bound `2 (3n+1)^t ≤ 3 (3n)^t` for `t ≤ n` -/

/-- Upper Bernoulli: `(A+1)^(k+1) ≤ A^(k+1) + (k+1) (A+1)^k`.
@isnad1 id=le.0h2v.s6.7001adfdd931 from=translated src=- shape=a6c554cb vocab=f96c6fce
-/
theorem bernoulli_upper (A : Nat) : ∀ k, (A + 1) ^ (k + 1) ≤ A ^ (k + 1) + (k + 1) * (A + 1) ^ k := by
  intro k; induction k with
  | zero => simp
  | succ k ih =>
    have hmul : (A + 1) ^ (k + 1) * (A + 1) ≤ (A ^ (k + 1) + (k + 1) * (A + 1) ^ k) * (A + 1) :=
      Nat.mul_le_mul_right _ ih
    have hAle : A ^ (k + 1) ≤ (A + 1) ^ (k + 1) := Nat.pow_le_pow_left (Nat.le_succ A) _
    have e : (A ^ (k + 1) + (k + 1) * (A + 1) ^ k) * (A + 1)
        = A ^ (k + 1 + 1) + A ^ (k + 1) + (k + 1) * (A + 1) ^ (k + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_succ]
    rw [Nat.pow_succ (A + 1) (k + 1)]
    calc (A + 1) ^ (k + 1) * (A + 1)
        ≤ A ^ (k + 1 + 1) + A ^ (k + 1) + (k + 1) * (A + 1) ^ (k + 1) := by rw [← e]; exact hmul
      _ ≤ A ^ (k + 1 + 1) + (A + 1) ^ (k + 1) + (k + 1) * (A + 1) ^ (k + 1) := by
          have := Nat.add_le_add_right (Nat.add_le_add_left hAle (A ^ (k + 1 + 1))) ((k + 1) * (A + 1) ^ (k + 1))
          exact this
      _ = A ^ (k + 1 + 1) + (k + 1 + 1) * (A + 1) ^ (k + 1) := by
          rw [Nat.succ_mul (k + 1)]; omega

/-- `2 (3n)^n ≤ 3 (3n-1)^n` for `n ≥ 1`, written with `A + 1 = 3n`.
@isnad1 id=le.1h1v.s6.d3055cd78ee7 from=translated src=- shape=d3bd1207 vocab=3e115a59
-/
theorem two_pow_le_three_pred_pow (n : Nat) (hn : 1 ≤ n) :
    2 * (3 * n) ^ n ≤ 3 * (3 * n - 1) ^ n := by
  obtain ⟨A, hA⟩ : ∃ A, 3 * n = A + 1 := ⟨3 * n - 1, by omega⟩
  have hA' : 3 * n - 1 = A := by omega
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hA', hA]
  have hb := bernoulli_upper A k
  -- (A+1)^(k+1) ≤ A^(k+1) + (k+1)(A+1)^k, and 3(k+1)(A+1)^k = (A+1)^(k+1) since A+1 = 3(k+1)
  have h3 : 3 * ((k + 1) * (A + 1) ^ k) = (A + 1) ^ (k + 1) := by
    rw [Nat.pow_succ, ← Nat.mul_assoc, show 3 * (k + 1) = A + 1 from by omega, Nat.mul_comm]
  rw [hk] at *
  -- 3 (A+1)^(k+1) ≤ 3 A^(k+1) + (A+1)^(k+1)  ⇒  2 (A+1)^(k+1) ≤ 3 A^(k+1)
  have := Nat.mul_le_mul_left 3 hb
  rw [Nat.mul_add, h3] at this
  omega

/-- `(3n+1)^n (3n-1)^n ≤ ((3n)^n)^2`.
@isnad1 id=le.1h1v.s7.b29e093fd5f2 from=translated src=- shape=40504207 vocab=cdb4433a
-/
theorem prod_pm_le (n : Nat) (hn : 1 ≤ n) :
    (3 * n + 1) ^ n * (3 * n - 1) ^ n ≤ (3 * n) ^ n * (3 * n) ^ n := by
  rw [← Nat.mul_pow, ← Nat.mul_pow]
  apply Nat.pow_le_pow_left
  -- (3n+1)(3n-1) = 9n² - 1 ≤ 9n²
  obtain ⟨A, hA⟩ : ∃ A, 3 * n = A + 1 := ⟨3 * n - 1, by omega⟩
  rw [show 3 * n - 1 = A from by omega, hA]
  -- (A+2) A ≤ (A+1)(A+1)
  have : (A + 1 + 1) * A = A * A + 2 * A := by rw [Nat.add_mul, Nat.add_mul]; omega
  rw [this]
  have : (A + 1) * (A + 1) = A * A + 2 * A + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [this]; omega

/--
@isnad1 id=le.1h1v.s6.eac88bfb463f from=translated src=- shape=e7d7e65b vocab=f96c6fce
-/
theorem two_pow_succ_le (n : Nat) (hn : 1 ≤ n) : 2 * (3 * n + 1) ^ n ≤ 3 * (3 * n) ^ n := by
  have hpos : 0 < 3 * (3 * n - 1) ^ n := by
    apply Nat.mul_pos (by decide)
    apply Nat.pow_pos; omega
  apply Nat.le_of_mul_le_mul_right _ hpos
  -- 2(3n+1)^n · 3(3n-1)^n ≤ 6 (3n)^n(3n)^n ≤ 3(3n)^n · 3(3n-1)^n
  calc 2 * (3 * n + 1) ^ n * (3 * (3 * n - 1) ^ n)
      = (2 * 3) * ((3 * n + 1) ^ n * (3 * n - 1) ^ n) := by ac_rfl
    _ ≤ (2 * 3) * ((3 * n) ^ n * (3 * n) ^ n) := Nat.mul_le_mul_left _ (prod_pm_le n hn)
    _ = 3 * (3 * n) ^ n * (2 * (3 * n) ^ n) := by ac_rfl
    _ ≤ 3 * (3 * n) ^ n * (3 * (3 * n - 1) ^ n) :=
        Nat.mul_le_mul_left _ (two_pow_le_three_pred_pow n hn)

/--
@isnad1 id=le.2h2v.s6.1057000fa1a1 from=translated src=- shape=2d46af43 vocab=f96c6fce
-/
theorem two_pow_le_of_le (n t : Nat) (hn : 1 ≤ n) (ht : t ≤ n) :
    2 * (3 * n + 1) ^ t ≤ 3 * (3 * n) ^ t := by
  obtain ⟨u, hu⟩ : ∃ u, n = t + u := ⟨n - t, by omega⟩
  have hpos : 0 < (3 * n) ^ u := Nat.pow_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hpos
  have h := two_pow_succ_le n hn
  calc 2 * (3 * n + 1) ^ t * (3 * n) ^ u
      ≤ 2 * (3 * n + 1) ^ t * (3 * n + 1) ^ u := by
        apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left; omega
    _ = 2 * (3 * n + 1) ^ n := by rw [Nat.mul_assoc, ← Nat.pow_add, ← hu]
    _ ≤ 3 * (3 * n) ^ n := h
    _ = 3 * (3 * n) ^ t * (3 * n) ^ u := by rw [Nat.mul_assoc, ← Nat.pow_add, ← hu]

/-! ### Level product bound -/

/-- Termwise: `(3 m_i + 1) · 3n ≤ 3 m_i · (3n+1)` when `n ≤ m_i`, aggregated over a filter.
@isnad1 id=le.1h4v.s7.e0d2153f5326 from=translated src=- shape=cd5d204a vocab=2a6bba0d
-/
theorem prf_level_termwise (m : Nat → Nat) (p : Nat → Bool) (n : Nat) :
    ∀ N, (∀ i, i < N → p i = true → n ≤ m i) →
      prf p (fun i => 3 * m i + 1) N * (3 * n) ^ cnt p N
        ≤ prf p (fun i => 3 * m i) N * (3 * n + 1) ^ cnt p N := by
  intro N; induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro h
    have ih' := ih (fun i hi hp => h i (by omega) hp)
    rw [prf_succ, prf_succ, cnt_succ]
    cases hp : p N
    · simpa using ih'
    · have hnm := h N (by omega) hp
      -- (P·(3m+1)) · ((3n)^c · 3n) ≤ (Q·3m) · ((3n+1)^c · (3n+1))
      have hterm : (3 * m N + 1) * (3 * n) ≤ 3 * m N * (3 * n + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_one]
        have : 3 * n ≤ 3 * m N := Nat.mul_le_mul_left 3 hnm
        omega
      calc prf p (fun i => 3 * m i + 1) N * (3 * m N + 1) * ((3 * n) ^ cnt p N * (3 * n))
          = (prf p (fun i => 3 * m i + 1) N * (3 * n) ^ cnt p N) * ((3 * m N + 1) * (3 * n)) := by ac_rfl
        _ ≤ (prf p (fun i => 3 * m i) N * (3 * n + 1) ^ cnt p N) * (3 * m N * (3 * n + 1)) :=
            Nat.mul_le_mul ih' hterm
        _ = prf p (fun i => 3 * m i) N * (3 * m N) * ((3 * n + 1) ^ cnt p N * (3 * n + 1)) := by ac_rfl

/-- **Level bound.** If every selected state is `≥ n ≥ 1` and at most `n` indices are selected,
then `2 ∏(3m_i+1) ≤ 3 ∏ 3m_i` over the selection.
@isnad1 id=le.3h4v.s7.c4c2da5c924a from=translated src=- shape=529f2ef1 vocab=1c261043
-/
theorem prf_level_bound (m : Nat → Nat) (p : Nat → Bool) (n N : Nat) (hn : 1 ≤ n)
    (hlow : ∀ i, i < N → p i = true → n ≤ m i) (hcnt : cnt p N ≤ n) :
    2 * prf p (fun i => 3 * m i + 1) N ≤ 3 * prf p (fun i => 3 * m i) N := by
  have hpos : 0 < (3 * n) ^ cnt p N := Nat.pow_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hpos
  have h1 := prf_level_termwise m p n N hlow
  have h2 := two_pow_le_of_le n (cnt p N) hn hcnt
  calc 2 * prf p (fun i => 3 * m i + 1) N * (3 * n) ^ cnt p N
      = 2 * (prf p (fun i => 3 * m i + 1) N * (3 * n) ^ cnt p N) := by ac_rfl
    _ ≤ 2 * (prf p (fun i => 3 * m i) N * (3 * n + 1) ^ cnt p N) := Nat.mul_le_mul_left 2 h1
    _ = prf p (fun i => 3 * m i) N * (2 * (3 * n + 1) ^ cnt p N) := by ac_rfl
    _ ≤ prf p (fun i => 3 * m i) N * (3 * (3 * n) ^ cnt p N) := Nat.mul_le_mul_left _ h2
    _ = 3 * prf p (fun i => 3 * m i) N * (3 * n) ^ cnt p N := by ac_rfl

/-! ### Dyadic chain: `2^k F(2^k) ≤ 3^k G(2^k)` -/

/--
@isnad1 id=le.2h3v.s7.814777256185 from=translated src=- shape=f5ece688 vocab=a689b512
-/
theorem dyadic_chain (m : Nat → Nat) (hm : ∀ i, 1 ≤ m i) (hinj : ∀ i j, m i = m j → i = j) (N : Nat) :
    ∀ k, 2 ^ k * prf (fun i => decide (m i < 2 ^ k)) (fun i => 3 * m i + 1) N
        ≤ 3 ^ k * prf (fun i => decide (m i < 2 ^ k)) (fun i => 3 * m i) N := by
  intro k; induction k with
  | zero =>
    have hf : ∀ i, i < N → decide (m i < 2 ^ 0) = false := by
      intro i _; have := hm i; apply decide_eq_false; omega
    have e1 : prf (fun i => decide (m i < 2 ^ 0)) (fun i => 3 * m i + 1) N = 1 :=
      prf_of_false _ _ N hf
    have e2 : prf (fun i => decide (m i < 2 ^ 0)) (fun i => 3 * m i) N = 1 :=
      prf_of_false _ _ N hf
    rw [e1, e2]; simp
  | succ k ih =>
    -- split the predicate m i < 2^(k+1) into m i < 2^k  ∨  2^k ≤ m i < 2^(k+1)
    have hsplitF := prf_split
      (fun i => decide (m i < 2 ^ (k + 1)))
      (fun i => decide (m i < 2 ^ k))
      (fun i => decide (2 ^ k ≤ m i ∧ m i < 2 ^ (k + 1)))
      (fun i => 3 * m i + 1)
      (fun i => decide_split _ _ _ (by omega))
      (fun i => by simp only [decide_eq_true_eq]; omega) N
    have hsplitG := prf_split
      (fun i => decide (m i < 2 ^ (k + 1)))
      (fun i => decide (m i < 2 ^ k))
      (fun i => decide (2 ^ k ≤ m i ∧ m i < 2 ^ (k + 1)))
      (fun i => 3 * m i)
      (fun i => decide_split _ _ _ (by omega))
      (fun i => by simp only [decide_eq_true_eq]; omega) N
    have hlevel := prf_level_bound m (fun i => decide (2 ^ k ≤ m i ∧ m i < 2 ^ (k + 1))) (2 ^ k) N
      (Nat.pow_pos (by decide))
      (by intro i _ hp; simp at hp; exact hp.1)
      (by
        have := cnt_range_le m hinj (2 ^ k) (2 ^ (k + 1)) N
        rw [Nat.pow_succ] at this ⊢
        omega)
    rw [hsplitF, hsplitG, Nat.pow_succ, Nat.pow_succ]
    calc 2 ^ k * 2 * (prf (fun i => decide (m i < 2 ^ k)) (fun i => 3 * m i + 1) N
              * prf (fun i => decide (2 ^ k ≤ m i ∧ m i < 2 ^ (k + 1))) (fun i => 3 * m i + 1) N)
        = (2 ^ k * prf (fun i => decide (m i < 2 ^ k)) (fun i => 3 * m i + 1) N)
            * (2 * prf (fun i => decide (2 ^ k ≤ m i ∧ m i < 2 ^ (k + 1))) (fun i => 3 * m i + 1) N) := by ac_rfl
      _ ≤ (3 ^ k * prf (fun i => decide (m i < 2 ^ k)) (fun i => 3 * m i) N)
            * (3 * prf (fun i => decide (2 ^ k ≤ m i ∧ m i < 2 ^ (k + 1))) (fun i => 3 * m i) N) :=
          Nat.mul_le_mul ih hlevel
      _ = 3 ^ k * 3 * (prf (fun i => decide (m i < 2 ^ k)) (fun i => 3 * m i) N
              * prf (fun i => decide (2 ^ k ≤ m i ∧ m i < 2 ^ (k + 1))) (fun i => 3 * m i) N) := by ac_rfl

/-- **Packing bound.** For an injective positive sequence and `N ≤ 2^L`:
`2^(L+1) ∏_{i<N}(3m_i+1) ≤ 3^(L+1) ∏_{i<N} 3m_i`.
@isnad1 id=le.3h3v.s7.138d4d075116 from=translated src=- shape=071cb608 vocab=ca2bfc9b
-/
theorem packing_bound (m : Nat → Nat) (hm : ∀ i, 1 ≤ m i) (hinj : ∀ i j, m i = m j → i = j)
    (N L : Nat) (hNL : N ≤ 2 ^ L) :
    2 ^ (L + 1) * pr (fun i => 3 * m i + 1) N ≤ 3 ^ (L + 1) * pr (fun i => 3 * m i) N := by
  rw [pr_eq_prf_true, pr_eq_prf_true]
  have hsplitF := prf_split (fun _ => true)
    (fun i => decide (m i < 2 ^ L)) (fun i => decide (2 ^ L ≤ m i))
    (fun i => 3 * m i + 1)
    (fun i => by rcases Nat.lt_or_ge (m i) (2 ^ L) with h | h <;> simp [h])
    (fun i => by simp only [decide_eq_true_eq]; omega) N
  have hsplitG := prf_split (fun _ => true)
    (fun i => decide (m i < 2 ^ L)) (fun i => decide (2 ^ L ≤ m i))
    (fun i => 3 * m i)
    (fun i => by rcases Nat.lt_or_ge (m i) (2 ^ L) with h | h <;> simp [h])
    (fun i => by simp only [decide_eq_true_eq]; omega) N
  have hchain := dyadic_chain m hm hinj N L
  have htail := prf_level_bound m (fun i => decide (2 ^ L ≤ m i)) (2 ^ L) N
    (Nat.pow_pos (by decide))
    (by intro i _ hp; simpa using hp)
    (Nat.le_trans (cnt_le _ N) hNL)
  rw [hsplitF, hsplitG, Nat.pow_succ, Nat.pow_succ]
  calc 2 ^ L * 2 * (prf (fun i => decide (m i < 2 ^ L)) (fun i => 3 * m i + 1) N
          * prf (fun i => decide (2 ^ L ≤ m i)) (fun i => 3 * m i + 1) N)
      = (2 ^ L * prf (fun i => decide (m i < 2 ^ L)) (fun i => 3 * m i + 1) N)
          * (2 * prf (fun i => decide (2 ^ L ≤ m i)) (fun i => 3 * m i + 1) N) := by ac_rfl
    _ ≤ (3 ^ L * prf (fun i => decide (m i < 2 ^ L)) (fun i => 3 * m i) N)
          * (3 * prf (fun i => decide (2 ^ L ≤ m i)) (fun i => 3 * m i) N) :=
        Nat.mul_le_mul hchain htail
    _ = 3 ^ L * 3 * (prf (fun i => decide (m i < 2 ^ L)) (fun i => 3 * m i) N
          * prf (fun i => decide (2 ^ L ≤ m i)) (fun i => 3 * m i) N) := by ac_rfl

/-! ### The exact orbit product identity -/

/-- `2^{s_j} m_j ∏_{i<j} 3m_i = 3^j m_0 ∏_{i<j}(3m_i+1)`, from the exact step law.
@isnad1 id=eq.1h3v.s7.21bc270acee4 from=translated src=- shape=ebed0f16 vocab=0a633cba
-/
theorem orbit_product_identity (m d : Nat → Nat)
    (hstep : ∀ i, 2 ^ d i * m (i + 1) = 3 * m i + 1) :
    ∀ j, 2 ^ sr d j * m j * pr (fun i => 3 * m i) j = 3 ^ j * m 0 * pr (fun i => 3 * m i + 1) j := by
  intro j; induction j with
  | zero => simp
  | succ j ih =>
    rw [sr_succ, pr_succ, pr_succ, Nat.pow_add, Nat.pow_succ]
    calc 2 ^ sr d j * 2 ^ d j * m (j + 1) * (pr (fun i => 3 * m i) j * (3 * m j))
        = (2 ^ sr d j * pr (fun i => 3 * m i) j) * (2 ^ d j * m (j + 1)) * (3 * m j) := by ac_rfl
      _ = (2 ^ sr d j * pr (fun i => 3 * m i) j) * (3 * m j + 1) * (3 * m j) := by rw [hstep j]
      _ = (2 ^ sr d j * m j * pr (fun i => 3 * m i) j) * (3 * (3 * m j + 1)) := by ac_rfl
      _ = (3 ^ j * m 0 * pr (fun i => 3 * m i + 1) j) * (3 * (3 * m j + 1)) := by rw [ih]
      _ = 3 ^ j * 3 * m 0 * (pr (fun i => 3 * m i + 1) j * (3 * m j + 1)) := by ac_rfl

/-! ### Uniform state bound and the injective contradiction -/

/-- For `j ≤ N`: `m_j · 2^(L+1) ≤ 2^G m_0 · 3^(L+1)` whenever `N ≤ 2^L` and the lower drift
bound `3^j ≤ 2^G 2^{s_j}` holds.
@isnad1 id=le.6h6v.s8.e0c89c50b733 from=translated src=- shape=869bc9b0 vocab=ef9940d3
-/
theorem state_bound (m d : Nat → Nat) (G : Nat)
    (hm : ∀ i, 1 ≤ m i) (hinj : ∀ i j, m i = m j → i = j)
    (hstep : ∀ i, 2 ^ d i * m (i + 1) = 3 * m i + 1)
    (hlow : ∀ j, 3 ^ j ≤ 2 ^ G * 2 ^ sr d j)
    (N L : Nat) (hNL : N ≤ 2 ^ L) :
    ∀ j, j ≤ N → m j * 2 ^ (L + 1) ≤ 2 ^ G * m 0 * 3 ^ (L + 1) := by
  intro j hj
  have hid := orbit_product_identity m d hstep j
  have hQj : 1 ≤ pr (fun i => 3 * m i) j := pr_pos _ (fun i => by have := hm i; omega) j
  have hQN : 1 ≤ pr (fun i => 3 * m i) N := pr_pos _ (fun i => by have := hm i; omega) N
  have h2S : 1 ≤ 2 ^ sr d j := Nat.pow_pos (by decide)
  -- step 1: m_j Q_j ≤ 2^G m_0 P_j
  have h1 : m j * pr (fun i => 3 * m i) j ≤ 2 ^ G * m 0 * pr (fun i => 3 * m i + 1) j := by
    apply Nat.le_of_mul_le_mul_left _ h2S
    calc 2 ^ sr d j * (m j * pr (fun i => 3 * m i) j)
        = 3 ^ j * m 0 * pr (fun i => 3 * m i + 1) j := by rw [← hid]; ac_rfl
      _ ≤ (2 ^ G * 2 ^ sr d j) * m 0 * pr (fun i => 3 * m i + 1) j :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hlow j))
      _ = 2 ^ sr d j * (2 ^ G * m 0 * pr (fun i => 3 * m i + 1) j) := by ac_rfl
  -- step 2: P_j Q_N ≤ Q_j P_N   (extend from j to N termwise)
  obtain ⟨t, ht⟩ : ∃ t, N = j + t := ⟨N - j, by omega⟩
  have h2 : pr (fun i => 3 * m i + 1) j * pr (fun i => 3 * m i) N
      ≤ pr (fun i => 3 * m i) j * pr (fun i => 3 * m i + 1) N := by
    rw [ht, pr_add, pr_add]
    have hle : pr (fun i => 3 * m (j + i)) t ≤ pr (fun i => 3 * m (j + i) + 1) t :=
      pr_le_pr _ _ t (fun i _ => Nat.le_succ _)
    calc pr (fun i => 3 * m i + 1) j * (pr (fun i => 3 * m i) j * pr (fun i => 3 * m (j + i)) t)
        = (pr (fun i => 3 * m i) j * pr (fun i => 3 * m i + 1) j) * pr (fun i => 3 * m (j + i)) t := by ac_rfl
      _ ≤ (pr (fun i => 3 * m i) j * pr (fun i => 3 * m i + 1) j) * pr (fun i => 3 * m (j + i) + 1) t :=
          Nat.mul_le_mul_left _ hle
      _ = pr (fun i => 3 * m i) j * (pr (fun i => 3 * m i + 1) j * pr (fun i => 3 * m (j + i) + 1) t) := by ac_rfl
  -- step 3: m_j Q_N ≤ 2^G m_0 P_N
  have h3 : m j * pr (fun i => 3 * m i) N ≤ 2 ^ G * m 0 * pr (fun i => 3 * m i + 1) N := by
    apply Nat.le_of_mul_le_mul_left _ hQj
    calc pr (fun i => 3 * m i) j * (m j * pr (fun i => 3 * m i) N)
        = (m j * pr (fun i => 3 * m i) j) * pr (fun i => 3 * m i) N := by ac_rfl
      _ ≤ (2 ^ G * m 0 * pr (fun i => 3 * m i + 1) j) * pr (fun i => 3 * m i) N :=
          Nat.mul_le_mul_right _ h1
      _ = 2 ^ G * m 0 * (pr (fun i => 3 * m i + 1) j * pr (fun i => 3 * m i) N) := by ac_rfl
      _ ≤ 2 ^ G * m 0 * (pr (fun i => 3 * m i) j * pr (fun i => 3 * m i + 1) N) :=
          Nat.mul_le_mul_left _ h2
      _ = pr (fun i => 3 * m i) j * (2 ^ G * m 0 * pr (fun i => 3 * m i + 1) N) := by ac_rfl
  -- step 4: multiply by 2^(L+1) and use the packing bound
  have hpack := packing_bound m hm hinj N L hNL
  apply Nat.le_of_mul_le_mul_left _ hQN
  calc pr (fun i => 3 * m i) N * (m j * 2 ^ (L + 1))
      = (m j * pr (fun i => 3 * m i) N) * 2 ^ (L + 1) := by ac_rfl
    _ ≤ (2 ^ G * m 0 * pr (fun i => 3 * m i + 1) N) * 2 ^ (L + 1) := Nat.mul_le_mul_right _ h3
    _ = 2 ^ G * m 0 * (2 ^ (L + 1) * pr (fun i => 3 * m i + 1) N) := by ac_rfl
    _ ≤ 2 ^ G * m 0 * (3 ^ (L + 1) * pr (fun i => 3 * m i) N) := Nat.mul_le_mul_left _ hpack
    _ = pr (fun i => 3 * m i) N * (2 ^ G * m 0 * 3 ^ (L + 1)) := by ac_rfl

/-- Pigeonhole: `N` distinct values in `[1, X]` force `N ≤ X`.
@isnad1 id=le.2h3v.s5.6612aa8cfad2 from=translated src=- shape=121c7631 vocab=6ff3cf84
-/
theorem pigeonhole (m : Nat → Nat) (hinj : ∀ i j, m i = m j → i = j) (N X : Nat)
    (h : ∀ j, j < N → 1 ≤ m j ∧ m j ≤ X) : N ≤ X := by
  have hall : cnt (fun i => decide (1 ≤ m i ∧ m i < X + 1)) N = N := by
    apply cnt_of_true
    intro i hi; have := h i hi; simp; omega
  have := cnt_range_le m hinj 1 (X + 1) N
  omega

/-- **Main core theorem.** No injective positive orbit satisfies an integer lower drift bound.
@isnad1 id=false.4h3v.s7.5ff85b75c458 from=translated src=- shape=aa399b8b vocab=ef9940d3
-/
theorem no_injective_orbit_of_lower_drift (m d : Nat → Nat) (G : Nat)
    (hm : ∀ i, 1 ≤ m i) (hinj : ∀ i j, m i = m j → i = j)
    (hstep : ∀ i, 2 ^ d i * m (i + 1) = 3 * m i + 1)
    (hlow : ∀ j, 3 ^ j ≤ 2 ^ G * 2 ^ sr d j) : False := by
  have hC : 1 ≤ 2 ^ G * m 0 := Nat.mul_le_mul (Nat.pow_pos (by decide)) (hm 0)
  -- K := 9 C, N := 2^K, L := K
  obtain ⟨C, hCdef⟩ : ∃ C, C = 2 ^ G * m 0 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, 9 * C = k + 1 := ⟨9 * C - 1, by omega⟩
  have hsb := state_bound m d G hm hinj hstep hlow (2 ^ (k + 1)) (k + 1) (Nat.le_refl _)
  have hX : ∀ j, j < 2 ^ (k + 1) → 1 ≤ m j ∧ m j ≤ C * 3 ^ (k + 1 + 1) / 2 ^ (k + 1 + 1) := by
    intro j hj
    refine ⟨hm j, ?_⟩
    have := hsb j (Nat.le_of_lt hj)
    rw [← hCdef] at this
    exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).2 this
  have hpig := pigeonhole m hinj (2 ^ (k + 1)) _ hX
  have hmul : 2 ^ (k + 1) * 2 ^ (k + 1 + 1) ≤ C * 3 ^ (k + 1 + 1) :=
    Nat.le_trans (Nat.mul_le_mul_right _ hpig) (Nat.div_mul_le_self _ _)
  -- LHS = 2 * 4^(k+1) ≥ 2 * (3^(k+1) + (k+1) 3^k) ; RHS = 9 C 3^k
  have hbern := bernoulli_nat 3 k
  have h4 : 2 ^ (k + 1) * 2 ^ (k + 1 + 1) = 2 * ((2 * 2) ^ (k + 1)) := by
    rw [Nat.mul_pow, Nat.pow_succ 2 (k + 1)]; ac_rfl
  have h3a : 3 ^ (k + 1) = 3 ^ k * 3 := Nat.pow_succ 3 k
  have h3b : 3 ^ (k + 1 + 1) = 3 ^ k * 9 := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
  rw [h4] at hmul
  rw [h3a] at hbern
  rw [h3b] at hmul
  -- 2 * (3^k*3 + (k+1)*3^k) ≤ 2 * 4^(k+1) ≤ C * (3^k * 9)
  have hcomb : 2 * (3 ^ k * 3 + (k + 1) * 3 ^ k) ≤ C * (3 ^ k * 9) :=
    Nat.le_trans (Nat.mul_le_mul_left 2 hbern) hmul
  have hpos : 0 < 3 ^ k := Nat.pow_pos (by decide)
  -- divide by 3^k: 6 + 2(k+1) ≤ 9 C = k + 1, contradiction
  have hdiv : (2 * 3 + 2 * (k + 1)) * 3 ^ k ≤ (9 * C) * 3 ^ k := by
    calc (2 * 3 + 2 * (k + 1)) * 3 ^ k = 2 * (3 ^ k * 3 + (k + 1) * 3 ^ k) := by
          have e := Nat.mul_add 2 (3 ^ k * 3) ((k + 1) * 3 ^ k)
          rw [e, Nat.add_mul]; ac_rfl
      _ ≤ C * (3 ^ k * 9) := hcomb
      _ = (9 * C) * 3 ^ k := by ac_rfl
  have := Nat.le_of_mul_le_mul_right hdiv hpos
  omega

end EOC.BoundedDriftCore
