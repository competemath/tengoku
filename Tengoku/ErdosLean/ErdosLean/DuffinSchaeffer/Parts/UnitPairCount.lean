import Tengoku.ErdosLean.ErdosLean.DuffinSchaeffer.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Duffin–Schaeffer — Part 6: counting pairs of reduced residues (CRT)

With `g = gcd(q,r)`, `q = g q'`, `r = g r'`, `m = q' r'`, the number
`N(h)` of pairs `(a mod q, b mod r)` of reduced residues with `a r' - b q' ≡ h (mod lcm(q,r))`
vanishes unless `gcd(h, m) = 1`, and then
`N(h) ≤ g · (φ(q)/q) · (φ(r)/r) · (m/φ(m)) · (d/φ(d))`, `d = gcd(h, g)`.
(Exact CRT count: `a` is fixed mod `q'`, and the `g` lifts are constrained only mod primes `p | g`.)
The case `q = r` (`g = q`, `m = 1`) is used for the lower bound on `λ(A_q)`.

Proof outline.  If `(a₀, b₀)` is one solution, every solution is
`((a₀ + q' t) mod q, (b₀ + r' t) mod r)` for some `t ∈ [0, g)`, and `t` must avoid, for every
prime `p | g`, the roots mod `p` of `F(t) = (a₀ + q' t)(b₀ + r' t)`.  A CRT sieve counts these
`t` exactly as `(g / rad g) ∏_{p | g} #{x < p : p ∤ F x}`; there is at least one root mod `p`, and
two distinct ones unless `p | q' r' h`.  The right-hand side equals
`g ∏_{p | g} (1 - 1/p)^2 / (the factors (1 - 1/p) for p | q', p | r', p | d)`.
-/

open Finset

namespace DuffinSchaeffer

namespace UnitPairCountAux

/-- Counting in blocks: a condition depending only on `s mod d`.-/
lemma card_filter_range_mul_mod (Q : ℕ → Prop) [DecidablePred Q] (d k : ℕ) :
    ((range (d * k)).filter (fun s => Q (s % d))).card = k * ((range d).filter Q).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mul_add, mul_one, Finset.card_filter, Finset.sum_range_add, ← Finset.card_filter, ih,
      Finset.card_filter (p := Q)]
    have : ∀ x ∈ range d, (if Q ((d * k + x) % d) then 1 else 0) = (if Q x then 1 else 0) := by
      intro x hx
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.1 hx)]
    rw [Finset.sum_congr rfl this]
    ring

/-- The Chinese remainder theorem for counting.-/
lemma card_filter_crt (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (co : Nat.Coprime m n)
    (Q1 Q2 : ℕ → Prop) [DecidablePred Q1] [DecidablePred Q2] :
    ((range (m * n)).filter (fun s => Q1 (s % m) ∧ Q2 (s % n))).card =
      ((range m).filter Q1).card * ((range n).filter Q2).card := by
  rw [← card_product]
  refine card_bij (fun s _ => (s % m, s % n)) ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_range, mem_product] at hs ⊢
    exact ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hm), hs.2.1⟩,
      Nat.mod_lt _ (Nat.pos_of_ne_zero hn), hs.2.2⟩
  · intro s1 hs1 s2 hs2 heq
    simp only [mem_filter, mem_range, Prod.mk.injEq] at hs1 hs2 heq
    exact ((Nat.modEq_and_modEq_iff_modEq_mul co).1 ⟨heq.1, heq.2⟩).eq_of_lt_of_lt hs1.1 hs2.1
  · rintro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_range, mem_product] at hxy
    obtain ⟨⟨hx, hQ1⟩, hy, hQ2⟩ := hxy
    have h1 : (Nat.chineseRemainder co x y : ℕ) % m = x :=
      Eq.trans (Nat.chineseRemainder co x y).prop.1 (Nat.mod_eq_of_lt hx)
    have h2 : (Nat.chineseRemainder co x y : ℕ) % n = y :=
      Eq.trans (Nat.chineseRemainder co x y).prop.2 (Nat.mod_eq_of_lt hy)
    refine ⟨Nat.chineseRemainder co x y, ?_, ?_⟩
    · simp only [mem_filter, mem_range, h1, h2]
      exact ⟨Nat.chineseRemainder_lt_mul co x y hm hn, hQ1, hQ2⟩
    · simp only [h1, h2]

/-- A CRT sieve over a finite set of primes.-/
lemma sieve (F : ℕ → ℕ) (hF : ∀ p s, p ∣ F s ↔ p ∣ F (s % p)) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ((range (∏ p ∈ P, p)).filter (fun s => ∀ p ∈ P, ¬ p ∣ F s)).card =
        ∏ p ∈ P, ((range p).filter (fun x => ¬ p ∣ F x)).card := by
  intro P
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | insert p P hpP ih =>
    intro hP
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hR0 : (∏ q ∈ P, q) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun q hq => (hP' q hq).ne_zero)
    have co : Nat.Coprime p (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp (hP' q hq)).2 (fun h => hpP (h ▸ hq))
    rw [prod_insert hpP, prod_insert hpP, ← ih hP',
      ← card_filter_crt p _ hp.ne_zero hR0 co (fun x => ¬ p ∣ F x)
        (fun y => ∀ q ∈ P, ¬ q ∣ F y)]
    congr 1
    apply filter_congr
    intro s _
    simp only [mem_insert, forall_eq_or_imp]
    apply and_congr
    · rw [hF p s]
    · apply forall₂_congr
      intro q hq
      have hqR : q ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem _ hq
      rw [hF q s, hF q (s % ∏ q ∈ P, q), Nat.mod_mod_of_dvd _ hqR]

/-- A linear polynomial `c + e x` with `p ∤ e` has a root mod `p`.-/
lemma exists_root (p c e : ℕ) (hp : p.Prime) (he : ¬ p ∣ e) : ∃ x < p, p ∣ c + e * x := by
  have := Fact.mk hp
  have he' : (e : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact he
  refine ⟨((-(c : ZMod p)) / e).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [mul_comm, div_mul_cancel₀ _ he']
  exact add_neg_cancel _

/-- The local factor `1 - 1/p`.-/
noncomputable def fA (p : ℕ) : ℝ := 1 - (p : ℝ)⁻¹

/-- The local factor of the right-hand side.-/
noncomputable def cfac (x y z p : ℕ) : ℝ :=
  fA p ^ 2 / ((if p ∣ x then fA p else 1) * (if p ∣ y then fA p else 1) *
    (if p ∣ z then fA p else 1))

lemma fA_pos {p : ℕ} (hp : p.Prime) : 0 < fA p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hinv : (p:ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hpos.ne'
  have hi0 : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
  have := mul_le_mul_of_nonneg_left hp2 hi0.le
  unfold fA; linarith

lemma prod_fA_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : 0 < ∏ p ∈ s, fA p :=
  prod_pos (fun p hp => fA_pos (hs p hp))

lemma prod_ite_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (x : ℕ) :
    0 < ∏ p ∈ s, (if p ∣ x then fA p else 1) := by
  apply prod_pos
  intro p hp
  split_ifs
  · exact fA_pos (hs p hp)
  · exact one_pos

lemma per_prime (p x y z good : ℕ) (hp : p.Prime) (h1 : good + 1 ≤ p)
    (h2 : ¬ p ∣ x → ¬ p ∣ y → ¬ p ∣ z → good + 2 ≤ p) :
    (good : ℝ) / p ≤ cfac x y z p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hinv : (p:ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hpos.ne'
  have hf0 : 0 < fA p := fA_pos hp
  have hf1 : fA p ≤ 1 := by
    have : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
    unfold fA; linarith
  have hI : ∀ (P : Prop) [Decidable P],
      0 < (if P then fA p else 1) ∧ (if P then fA p else 1) ≤ 1 := by
    intro P _
    split_ifs <;> constructor <;> linarith
  have b1 := hI (p ∣ x)
  have b2 := hI (p ∣ y)
  have b3 := hI (p ∣ z)
  have e1 : p ∣ x → (if p ∣ x then fA p else 1) = fA p := fun h => by simp [h]
  have e2 : p ∣ y → (if p ∣ y then fA p else 1) = fA p := fun h => by simp [h]
  have e3 : p ∣ z → (if p ∣ z then fA p else 1) = fA p := fun h => by simp [h]
  have e1' : ¬ p ∣ x → (if p ∣ x then fA p else 1) = 1 := fun h => by simp [h]
  have e2' : ¬ p ∣ y → (if p ∣ y then fA p else 1) = 1 := fun h => by simp [h]
  have e3' : ¬ p ∣ z → (if p ∣ z then fA p else 1) = 1 := fun h => by simp [h]
  unfold cfac
  generalize (if p ∣ x then fA p else 1) = i1 at b1 e1 e1' ⊢
  generalize (if p ∣ y then fA p else 1) = i2 at b2 e2 e2' ⊢
  generalize (if p ∣ z then fA p else 1) = i3 at b3 e3 e3' ⊢
  by_cases hall : ¬ p ∣ x ∧ ¬ p ∣ y ∧ ¬ p ∣ z
  · rw [e1' hall.1, e2' hall.2.1, e3' hall.2.2, mul_one, mul_one, div_one]
    have hg2 : (good:ℝ) + 2 ≤ p := by exact_mod_cast h2 hall.1 hall.2.1 hall.2.2
    rw [div_le_iff₀ hpos]
    have e : fA p ^ 2 * p = p - 2 * ((p:ℝ)⁻¹ * p) + (p:ℝ)⁻¹ * ((p:ℝ)⁻¹ * p) := by
      unfold fA; ring
    rw [e, hinv]
    have : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
    linarith
  · have hJ0 : 0 < i1 * i2 * i3 := mul_pos (mul_pos b1.1 b2.1) b3.1
    have hJ : i1 * i2 * i3 ≤ fA p := by
      by_cases hx : p ∣ x
      · rw [e1 hx]
        have := mul_le_mul_of_nonneg_left (mul_le_one₀ b2.2 b3.1.le b3.2) hf0.le
        nlinarith
      · by_cases hy : p ∣ y
        · rw [e2 hy]
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ b1.2 b3.1.le b3.2) hf0.le
          nlinarith
        · have hz : p ∣ z := by
            by_contra hz; exact hall ⟨hx, hy, hz⟩
          rw [e3 hz]
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ b1.2 b2.1.le b2.2) hf0.le
          nlinarith
    have hg1 : (good:ℝ) + 1 ≤ p := by exact_mod_cast h1
    have hA : (good:ℝ) / p ≤ fA p := by
      rw [div_le_iff₀ hpos]; unfold fA; rw [sub_mul, hinv]; linarith
    have hB : fA p ≤ fA p ^ 2 / (i1 * i2 * i3) := by
      rw [le_div_iff₀ hJ0]; nlinarith
    linarith

lemma totient_div_eq (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℝ) / n = ∏ p ∈ n.primeFactors, fA p := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h' : ((Nat.totient n : ℚ) : ℝ) =
      ((n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [mul_div_cancel_left₀ _ this]
  rfl

lemma prod_inter_ite (g x : ℕ) (hx : x ≠ 0) (f : ℕ → ℝ) :
    ∏ p ∈ g.primeFactors ∩ x.primeFactors, f p =
      ∏ p ∈ g.primeFactors, (if p ∣ x then f p else 1) := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [mem_inter, mem_filter, Nat.mem_primeFactors]
  tauto

lemma prod_of_dvd (g d : ℕ) (hg : g ≠ 0) (hdg : d ∣ g) (f : ℕ → ℝ) :
    ∏ p ∈ d.primeFactors, f p = ∏ p ∈ g.primeFactors, (if p ∣ d then f p else 1) := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primeFactors]
  have hd : d ≠ 0 := by rintro rfl; exact hg (Nat.eq_zero_of_zero_dvd hdg)
  constructor
  · rintro ⟨hp, hpd, _⟩; exact ⟨⟨hp, hpd.trans hdg, hg⟩, hpd⟩
  · rintro ⟨⟨hp, _, _⟩, hpd⟩; exact ⟨hp, hpd, hd⟩

end UnitPairCountAux

end DuffinSchaeffer
