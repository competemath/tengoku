import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PrimCosetReps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_card_primCosetReps_eq_dedekindPsi

set_option maxHeartbeats 3200000

open _root_.Finset open _root_.Nat open _root_.Finset.Nat open _root_.ArithmeticFunction

namespace ModularCurve
export _root_.ModularCurve (dedekindPsi primCosetReps mem_primCosetReps)
namespace PrimCosetCount
open _root_.ModularCurve

def h (x : ℕ × ℕ) : ℕ := (x.2 / Nat.gcd x.1 x.2) * Nat.totient (Nat.gcd x.1 x.2)

/--
@isnad1 id=eq.0h2v.s5.9754f32350e0 from=translated src=- shape=876234ff vocab=5403c107
-/
theorem card_filter_coprime_range_mul (g m : ℕ) :
    ((range (g * m)).filter (fun b => Nat.Coprime g b)).card = m * Nat.totient g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.count_eq_card_filter_range] at ih ⊢
    rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
    congr 1
    rw [Nat.count_eq_card_filter_range, Nat.totient_eq_card_coprime]
    refine congrArg Finset.card (Finset.filter_congr (fun k _ => ?_))
    have hper := (Nat.periodic_coprime g).nat_mul m
    rw [Nat.cast_id] at hper
    rw [show g * m + k = k + m * g by ring]
    exact Iff.of_eq (hper k)

/--
@isnad1 id=eq.0h2v.s4.b02675c6ffc1 from=translated src=- shape=53b8944a vocab=932f3bd5
-/
theorem card_fibre (a d : ℕ) :
    ((range d).filter (fun b => Nat.Coprime (Nat.gcd a d) b)).card = h (a, d) := by
  set g := Nat.gcd a d with hg
  have hgd : g ∣ d := Nat.gcd_dvd_right a d
  obtain ⟨m, hm⟩ := hgd
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  ·
    have hd0 : d = 0 := by rw [hm, hg0, zero_mul]
    simp [h, hd0]
  · conv_lhs => rw [hm]
    rw [card_filter_coprime_range_mul, h]
    simp only
    rw [← hg, hm, Nat.mul_div_cancel_left m hgpos]

/--
@isnad1 id=eq.0h3v.s4.55f1786ae22c from=translated src=- shape=cc47edfb vocab=728c9787
-/
theorem gcd_rotate (a b d : ℕ) : Nat.gcd a (Nat.gcd b d) = Nat.gcd (Nat.gcd a d) b := by
  rw [Nat.gcd_comm b d, ← Nat.gcd_assoc]

/--
@isnad1 id=eq.1h1v.s5.36f801db5bb5 from=translated src=- shape=5b9fc11e vocab=4ce1fc6a
-/
theorem card_primCosetReps_eq_sum (N : ℕ) (hN : N ≠ 0) :
    (ModularCurve.primCosetReps N).card = ∑ x ∈ N.divisorsAntidiagonal, h x := by
  classical
  have hσ : (ModularCurve.primCosetReps N).card =
      (N.divisorsAntidiagonal.sigma (fun x => (range x.2).filter (fun b => Nat.Coprime (Nat.gcd x.1 x.2) b))).card := by
    refine Finset.card_nbij' (fun t => ⟨(t.1, t.2.2), t.2.1⟩) (fun s => (s.1.1, s.2, s.1.2)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b, d⟩ ht
      rw [Finset.mem_coe, ModularCurve.mem_primCosetReps hN] at ht
      obtain ⟨had, hbd, hgcd⟩ := ht
      rw [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨had, hN⟩, hbd, by rw [Nat.Coprime, ← gcd_rotate]; exact hgcd⟩
    · rintro ⟨⟨a, d⟩, b⟩ hs
      rw [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨⟨had, -⟩, hbd, hcop⟩ := hs
      rw [Finset.mem_coe, ModularCurve.mem_primCosetReps hN]
      exact ⟨had, hbd, by rw [gcd_rotate]; exact hcop⟩
    · rintro ⟨a, b, d⟩ _
      rfl
    · rintro ⟨⟨a, d⟩, b⟩ _
      rfl
  rw [hσ, Finset.card_sigma]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact card_fibre x.1 x.2

/--
@isnad1 id=eq.2h3v.s7.9c399b5d61a8 from=translated src=- shape=b747adfc vocab=d029fcd1
-/
theorem sum_divisorsAntidiagonal_mul_of_coprime {f : ℕ × ℕ → ℕ}
    (hf : ∀ a₁ d₁ a₂ d₂ : ℕ, Nat.Coprime (a₁ * d₁) (a₂ * d₂) →
      f (a₁ * a₂, d₁ * d₂) = f (a₁, d₁) * f (a₂, d₂))
    {m n : ℕ} (hmn : Nat.Coprime m n) :
    ∑ x ∈ (m * n).divisorsAntidiagonal, f x =
      (∑ x ∈ m.divisorsAntidiagonal, f x) * (∑ x ∈ n.divisorsAntidiagonal, f x) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => (p.1.1 * p.2.1, p.1.2 * p.2.2))
    (fun z => ((Nat.gcd z.1 m, Nat.gcd z.2 m), (Nat.gcd z.1 n, Nat.gcd z.2 n))) ?_ ?_ ?_ ?_ ?_
  ·
    rintro ⟨⟨a₁, d₁⟩, ⟨a₂, d₂⟩⟩ hp
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨h₁, hm0⟩, ⟨h₂, hn0⟩⟩ := hp
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨by rw [← h₁, ← h₂]; ring, Nat.mul_ne_zero hm0 hn0⟩
  ·
    rintro ⟨z₁, z₂⟩ hz
    rw [Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨hz, hmn0⟩ := hz
    have hm0 : m ≠ 0 := fun h0 => hmn0 (by rw [h0, zero_mul])
    have hn0 : n ≠ 0 := fun h0 => hmn0 (by rw [h0, mul_zero])
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, hm0⟩, ⟨?_, hn0⟩⟩
    · exact Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul hmn hz
    · exact Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul hmn.symm (by rw [hz, mul_comm])
  ·
    rintro ⟨⟨a₁, d₁⟩, ⟨a₂, d₂⟩⟩ hp
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨h₁, hm0⟩, ⟨h₂, hn0⟩⟩ := hp

    have ha₂m : Nat.Coprime a₂ m := Nat.Coprime.coprime_dvd_left (Dvd.intro _ h₂) hmn.symm
    have hd₂m : Nat.Coprime d₂ m := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ h₂) hmn.symm
    have ha₁n : Nat.Coprime a₁ n := Nat.Coprime.coprime_dvd_left (Dvd.intro _ h₁) hmn
    have hd₁n : Nat.Coprime d₁ n := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ h₁) hmn
    dsimp only
    simp only [Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel a₁ ha₂m, Nat.gcd_eq_left (Dvd.intro _ h₁)]
    · rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel d₁ hd₂m, Nat.gcd_eq_left (Dvd.intro_left _ h₁)]
    · rw [Nat.Coprime.gcd_mul_left_cancel a₂ ha₁n, Nat.gcd_eq_left (Dvd.intro _ h₂)]
    · rw [Nat.Coprime.gcd_mul_left_cancel d₂ hd₁n, Nat.gcd_eq_left (Dvd.intro_left _ h₂)]
  ·
    rintro ⟨z₁, z₂⟩ hz
    rw [Nat.mem_divisorsAntidiagonal] at hz
    obtain ⟨hz, hmn0⟩ := hz
    dsimp only
    simp only [Prod.mk.injEq]
    constructor
    · rw [← Nat.Coprime.gcd_mul z₁ hmn, Nat.gcd_eq_left (Dvd.intro _ hz)]
    · rw [← Nat.Coprime.gcd_mul z₂ hmn, Nat.gcd_eq_left (Dvd.intro_left _ hz)]
  ·
    rintro ⟨⟨a₁, d₁⟩, ⟨a₂, d₂⟩⟩ hp
    rw [Finset.mem_product, Nat.mem_divisorsAntidiagonal, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨h₁, hm0⟩, ⟨h₂, hn0⟩⟩ := hp
    simp only
    rw [hf a₁ d₁ a₂ d₂ (by rw [h₁, h₂]; exact hmn)]

/--
@isnad1 id=eq.1h4v.s6.6f1ebc9a02f4 from=translated src=- shape=ebd06128 vocab=6292ba4c
-/
theorem h_mul (a₁ d₁ a₂ d₂ : ℕ) (hcop : Nat.Coprime (a₁ * d₁) (a₂ * d₂)) :
    h (a₁ * a₂, d₁ * d₂) = h (a₁, d₁) * h (a₂, d₂) := by
  have ha₁a₂ : Nat.Coprime a₁ a₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop).coprime_dvd_right (Dvd.intro _ rfl)
  have ha₁d₂ : Nat.Coprime a₁ d₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop).coprime_dvd_right (Dvd.intro_left _ rfl)
  have hd₁a₂ : Nat.Coprime d₁ a₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hcop).coprime_dvd_right (Dvd.intro _ rfl)
  have hd₁d₂ : Nat.Coprime d₁ d₂ :=
    (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) hcop).coprime_dvd_right (Dvd.intro_left _ rfl)

  have hg : Nat.gcd (a₁ * a₂) (d₁ * d₂) = Nat.gcd a₁ d₁ * Nat.gcd a₂ d₂ := by
    rw [Nat.Coprime.gcd_mul _ hd₁d₂]
    rw [Nat.gcd_comm (a₁ * a₂) d₁, Nat.gcd_comm (a₁ * a₂) d₂,
      Nat.Coprime.gcd_mul _ ha₁a₂, Nat.Coprime.gcd_mul _ ha₁a₂,
      Nat.Coprime.gcd_eq_one hd₁a₂, (Nat.Coprime.gcd_eq_one ha₁d₂.symm), mul_one, one_mul,
      Nat.gcd_comm d₁ a₁, Nat.gcd_comm d₂ a₂]
  have hg₁ : Nat.gcd a₁ d₁ ∣ d₁ := Nat.gcd_dvd_right _ _
  have hg₂ : Nat.gcd a₂ d₂ ∣ d₂ := Nat.gcd_dvd_right _ _
  have hcopg : Nat.Coprime (Nat.gcd a₁ d₁) (Nat.gcd a₂ d₂) :=
    (hd₁d₂.coprime_dvd_left hg₁).coprime_dvd_right hg₂
  simp only [h]
  rw [hg, Nat.totient_mul hcopg, ← Nat.div_mul_div_comm hg₁ hg₂]
  ring

def G : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ x ∈ n.divisorsAntidiagonal, h x, by simp⟩

/--
@isnad1 id=eq.0h1v.s5.24be484da765 from=translated src=- shape=f4026d55 vocab=3751de09
-/
theorem G_apply (n : ℕ) : G n = ∑ x ∈ n.divisorsAntidiagonal, h x := rfl

/--
@isnad1 id=ismultip.0h0v.s2.de0b55cb120a from=translated src=- shape=25b03439 vocab=876ba459
-/
theorem isMultiplicative_G : G.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [G_apply]
    simp [h, Nat.divisorsAntidiagonal_one]
  · intro m n hmn
    rw [G_apply, G_apply, G_apply]
    exact sum_divisorsAntidiagonal_mul_of_coprime h_mul hmn

/--
@isnad1 id=eq.3h3v.s6.395866d1b776 from=translated src=- shape=ead3f742 vocab=3cda360e
-/
theorem h_prime_pow {p : ℕ} (hp : p.Prime) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    h (p ^ i, p ^ j) + p ^ (j - 1) = p ^ j := by
  simp only [h]
  rcases le_or_gt i j with hij | hij
  ·
    rw [Nat.gcd_eq_left (Nat.pow_dvd_pow p hij), Nat.pow_div hij hp.pos, Nat.totient_prime_pow hp hi]
    have : p ^ (j - i) * (p ^ (i - 1) * (p - 1)) + p ^ (j - 1) = p ^ j := by
      have e1 : p ^ (j - i) * p ^ (i - 1) = p ^ (j - 1) := by
        rw [← _root_.pow_add]; congr 1; omega
      have hp1 : 1 ≤ p := hp.one_le
      calc p ^ (j - i) * (p ^ (i - 1) * (p - 1)) + p ^ (j - 1)
          = p ^ (j - 1) * (p - 1) + p ^ (j - 1) := by rw [← mul_assoc, e1]
        _ = p ^ (j - 1) * (p - 1 + 1) := by ring
        _ = p ^ (j - 1) * p := by rw [Nat.sub_add_cancel hp1]
        _ = p ^ j := by rw [← pow_succ]; congr 1; omega
    exact this
  ·
    rw [Nat.gcd_eq_right (Nat.pow_dvd_pow p hij.le), Nat.div_self (pow_pos hp.pos j),
      Nat.totient_prime_pow hp hj, one_mul]
    have hp1 : 1 ≤ p := hp.one_le
    calc p ^ (j - 1) * (p - 1) + p ^ (j - 1) = p ^ (j - 1) * (p - 1 + 1) := by ring
      _ = p ^ (j - 1) * p := by rw [Nat.sub_add_cancel hp1]
      _ = p ^ j := by rw [← pow_succ]; congr 1; omega

/--
@isnad1 id=eq.0h1v.s3.750cdd6ab64a from=translated src=- shape=f4c0fc42 vocab=7b3b26e4
-/
theorem h_one_left (d : ℕ) : h (1, d) = d := by
  simp [h]

/--
@isnad1 id=eq.0h1v.s4.892184935bcc from=translated src=- shape=70a1ef76 vocab=7b3b26e4
-/
theorem h_one_right (a : ℕ) : h (a, 1) = 1 := by
  simp [h]

/--
@isnad1 id=eq.3h3v.s6.cb5f67299a8e from=translated src=- shape=652ff5cb vocab=7279ac2a
-/
theorem sum_h_prime_pow_partial {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∀ J : ℕ, 1 ≤ J → J ≤ k → ∑ j ∈ range J, h (p ^ (k - j), p ^ j) = p ^ (J - 1) := by
  intro J hJ1 hJk
  induction J with
  | zero => omega
  | succ J ih =>
    rcases Nat.eq_zero_or_pos J with rfl | hJpos
    · simp [h_one_right]
    · rw [Finset.sum_range_succ, ih hJpos (by omega)]
      have := h_prime_pow hp (k - J) J (by omega) hJpos

      have e : J + 1 - 1 = J := by omega
      rw [e]
      omega

/--
@isnad1 id=eq.2h2v.s6.d8778437056c from=translated src=- shape=618850cf vocab=957dffb8
-/
theorem G_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    G (p ^ k) = p ^ k + p ^ (k - 1) := by
  rw [G_apply, Nat.sum_divisorsAntidiagonal' (fun a d => h (a, d)), Nat.sum_divisors_prime_pow hp]

  have hterm : ∀ j ∈ range (k + 1), h (p ^ k / p ^ j, p ^ j) = h (p ^ (k - j), p ^ j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.pow_div (by omega) hp.pos]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ, sum_h_prime_pow_partial hp k k hk le_rfl,
    Nat.sub_self, pow_zero, h_one_left, add_comm]

def sqf : ArithmeticFunction ℕ :=
  ⟨fun n => if Squarefree n then 1 else 0, by simp [not_squarefree_zero]⟩

/--
@isnad1 id=eq.0h1v.s5.2f7ba6d37602 from=translated src=- shape=b4493b29 vocab=4602c577
-/
theorem sqf_apply (n : ℕ) : sqf n = if Squarefree n then 1 else 0 := rfl

/--
@isnad1 id=ismultip.0h0v.s2.185c967cfef3 from=translated src=- shape=25b03439 vocab=32762882
-/
theorem isMultiplicative_sqf : sqf.IsMultiplicative := by
  refine ⟨by simp [sqf_apply], ?_⟩
  intro m n hmn
  simp only [sqf_apply]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;>
    simp [hm, hn, Nat.squarefree_mul hmn]

def Psi : ArithmeticFunction ℕ := sqf * ArithmeticFunction.id

/--
@isnad1 id=ismultip.0h0v.s2.670e0aa53267 from=translated src=- shape=25b03439 vocab=254ddd89
-/
theorem isMultiplicative_Psi : Psi.IsMultiplicative :=
  isMultiplicative_sqf.mul isMultiplicative_id

/--
@isnad1 id=eq.0h1v.s4.22efb242b5a1 from=translated src=- shape=5ff49266 vocab=53f79ecf
-/
theorem Psi_apply (n : ℕ) : Psi n = ModularCurve.dedekindPsi n := by
  rw [Psi, ArithmeticFunction.mul_apply, ModularCurve.dedekindPsi,
    Nat.sum_divisorsAntidiagonal (fun x y => sqf x * ArithmeticFunction.id y), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [sqf_apply, ArithmeticFunction.id_apply]
  split_ifs <;> simp

/--
@isnad1 id=eq.2h2v.s6.c77d981ce534 from=translated src=- shape=618850cf vocab=f065906c
-/
theorem Psi_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    Psi (p ^ k) = p ^ k + p ^ (k - 1) := by
  rw [Psi_apply, ModularCurve.dedekindPsi, Finset.sum_filter, Nat.sum_divisors_prime_pow hp]

  have hterm : ∀ j ∈ range (k + 1),
      (if Squarefree (p ^ j) then p ^ k / p ^ j else 0) = if j = 0 then p ^ k else if j = 1 then p ^ (k - 1) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp
    · rcases eq_or_ne j 1 with rfl | hj1
      · rw [pow_one, ite_eq_left (Irreducible.squarefree hp), ite_eq_right one_ne_zero, ite_eq_left rfl]
        exact Nat.div_eq_of_eq_mul_left hp.pos (by rw [← pow_succ]; congr 1; omega)
      · have : ¬ Squarefree (p ^ j) := by
          rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
          exact fun h => hj1 h.2
        simp [this, hj1, Nat.pos_iff_ne_zero.mp hjpos]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have h0 : (range (k + 1)).filter (fun j => j = 0) = {0} := by
    ext j; simp
  have h1 : ((range (k + 1)).filter (fun j => ¬ j = 0)).filter (fun j => j = 1) = {1} := by
    ext j; simp; omega
  rw [h0, h1]
  simp

/--
@isnad1 id=eq.0h0v.s3.640b07287e1e from=translated src=- shape=836e6cbb vocab=accf8d24
-/
theorem G_eq_Psi : G = Psi := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers G isMultiplicative_G Psi isMultiplicative_Psi]
  intro p i hp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero, isMultiplicative_G.map_one, isMultiplicative_Psi.map_one]
  · rw [G_prime_pow hp i hi, Psi_prime_pow hp i hi]

end ModularCurve.PrimCosetCount

open ModularCurve.PrimCosetCount in

/--
@isnad1 id=eq.1h1v.s4.448a3c73951f from=translated src=- shape=0d930171 vocab=e9ba1ed4
-/
theorem solution (N : ℕ) (hN : N ≠ 0) :
    (ModularCurve.primCosetReps N).card = ModularCurve.dedekindPsi N := by
  rw [card_primCosetReps_eq_sum N hN, ← G_apply, G_eq_Psi, Psi_apply]
