import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**Lemma `lem:mixed-support-factorial`**: a pure number-theory building block for
`thm:optimal-divisor`. For a prime `p` with `p^a ∣ n` and `p^b ∣ k`, and `1 ≤ r ≤ n`,
`1 ≤ s ≤ k`,
`v_p(n! k! / ((n-r)! (k-s)!)) - min(v_p(r!), v_p(s!)) ≥ a + b - 1`.

Formalized additively (via descending factorials) to avoid truncated-subtraction and
division pitfalls: `v_p((n)_r) + v_p((k)_s) ≥ a + b - 1 + min(v_p(r!), v_p(s!))`, where
`(n)_r = n!/(n-r)! = n.descFactorial r`.
-/

namespace CongruenceTheory

open Nat

/-- `v_p((p^c)!) ≥ 2c - 1` for `c ≥ 1` (additive form avoiding subtraction:
`2c ≤ v_p((p^c)!) + 1`). The numerical engine behind the sub-lemma below.
@isnad1 id=le.2h2v.s5.f7e7a65e29ba from=translated src=- shape=28a619d9 vocab=85191fad
-/
theorem padicValNat_factorial_pow_ge (p : ℕ) (hp : p.Prime) :
    ∀ c : ℕ, 1 ≤ c → 2 * c ≤ padicValNat p ((p ^ c)!) + 1 := by
  haveI := Fact.mk hp
  intro c hc
  induction c with
  | zero => omega
  | succ c ih =>
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · subst hc0
      have h1 : padicValNat p ((p ^ 1)!) = padicValNat p (1 !) + 1 := by
        have := padicValNat_factorial_mul (p := p) 1
        simpa using this
      simp only [pow_one] at h1
      simp [h1]
    · have hstep : padicValNat p ((p ^ (c + 1))!) = padicValNat p ((p ^ c)!) + p ^ c := by
        have := padicValNat_factorial_mul (p := p) (p ^ c)
        rwa [← pow_succ'] at this
      have hpc2 : 2 ≤ p ^ c := by
        calc (2:ℕ) ≤ p ^ 1 := by simpa using hp.two_le
          _ ≤ p ^ c := Nat.pow_le_pow_right hp.one_lt.le hc0
      have := ih hc0
      omega

/-- `v_p(m!)` is monotone in `m`.
@isnad1 id=le.2h3v.s4.0fbd5f337d6d from=translated src=- shape=1ec5a98c vocab=cdb1c38c
-/
theorem padicValNat_factorial_mono (p : ℕ) (hp : p.Prime) {m n : ℕ} (h : m ≤ n) :
    padicValNat p (m !) ≤ padicValNat p (n !) := by
  haveI := Fact.mk hp
  obtain ⟨t, ht⟩ := factorial_dvd_factorial h
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, mul_zero] at ht; exact factorial_ne_zero n ht
  rw [ht, padicValNat.mul (factorial_ne_zero m) ht0]
  omega

/-- The crux sub-lemma (extracted from the manuscript's proof of
`lem:mixed-support-factorial`): if `v_p(r!) ≤ v_p(s!)` then `v_p(r) ≤ v_p((s-1)!) + 1`.
@isnad1 id=le.4h3v.s6.f7e035932c7e from=translated src=- shape=05d813b8 vocab=96476c22
-/
theorem padicValNat_le_padicValNat_pred_factorial_add_one (p : ℕ) (hp : p.Prime) {r s : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : padicValNat p (r !) ≤ padicValNat p (s !)) :
    padicValNat p r ≤ padicValNat p ((s - 1)!) + 1 := by
  haveI := Fact.mk hp
  by_contra hcon
  push Not at hcon
  set c := padicValNat p r with hc
  have hc2 : 2 ≤ c := by omega
  have hpcr : p ^ c ∣ r := pow_padicValNat_dvd
  have hrpc : p ^ c ≤ r := Nat.le_of_dvd hr hpcr
  have hstep2 : padicValNat p ((p ^ c)!) ≤ padicValNat p (r !) :=
    padicValNat_factorial_mono p hp hrpc
  have hstep3 := padicValNat_factorial_pow_ge p hp c (by omega)
  have hsfact : padicValNat p (s !) = padicValNat p s + padicValNat p ((s - 1)!) := by
    have hseq : s ! = s * (s - 1)! := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      simp [Nat.factorial_succ]
    rw [hseq, padicValNat.mul (by omega) (factorial_ne_zero _)]
  have hsm1 : padicValNat p ((s - 1)!) ≤ c - 2 := by omega
  have hsu : s - 1 < p ^ (c - 1) := by
    by_contra hge
    push Not at hge
    have hmono := padicValNat_factorial_mono p hp hge
    have hgrow := padicValNat_factorial_pow_ge p hp (c - 1) (by omega)
    omega
  have hsle : s ≤ p ^ (c - 1) := by omega
  have hps : p ^ (padicValNat p s) ∣ s := pow_padicValNat_dvd
  have hps' : p ^ (padicValNat p s) ≤ s := Nat.le_of_dvd hs hps
  have hple : p ^ (padicValNat p s) ≤ p ^ (c - 1) := hps'.trans hsle
  have hvs : padicValNat p s ≤ c - 1 :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp hple
  omega

end CongruenceTheory
