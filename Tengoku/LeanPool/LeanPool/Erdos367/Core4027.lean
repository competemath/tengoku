/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import Tengoku

/-! ## Definitions -/

@[expose] public section

open scoped BigOperators

namespace Core4027

/-- The `r`-full part of `m`: the product of `p ^ v_p(m)` over primes `p` with `v_p(m) ≥ r`. -/
def rFullPart (r m : ℕ) : ℕ :=
  (m.factorization.filter (fun p => r ≤ m.factorization p)).prod (fun p v => p ^ v)

/-- The constant `N = 2^14 * 3^4`. -/
def N : ℕ := 1327104

/-- `C(t) = t^4 + 42 t^2 + 72 t + 333`. -/
def Cpoly (t : ℕ) : ℕ := t^4 + 42*t^2 + 72*t + 333

/-- `G(t)`. -/
def Gpoly (t : ℕ) : ℕ :=
  t^9 + 108*t^7 + 216*t^6 + 4374*t^5 + 13608*t^4 + 99468*t^3 + 215784*t^2 + 998001*t + 1474200

/-- `H(t)`. -/
def Hpoly (t : ℕ) : ℕ :=
  t^15 + 198*t^13 + 432*t^12 + 16875*t^11 + 65448*t^10 + 893700*t^9 + 3965760*t^8
    + 32798439*t^7 + 132802416*t^6 + 770808150*t^5 + 2699107920*t^4 + 10666416717*t^3
    + 28403408808*t^2 + 78874347456*t + 150060252672

/-- `n = (G(t)/N)^3`. -/
def nn (t : ℕ) : ℕ := (Gpoly t / N) ^ 3

/-! ## The `rFullPart` factorization theory -/

theorem rFullPart_ne_zero (r M : ℕ) : rFullPart r M ≠ 0 := by
  unfold rFullPart
  simp_all

/-- A perfect cube of a positive number is `3`-full: its `rFullPart 3` is itself. -/
theorem rFullPart_cube_eq (a : ℕ) (ha : 1 ≤ a) : rFullPart 3 (a^3) = a^3 := by
  unfold rFullPart
  have hne : a^3 ≠ 0 := by positivity
  have hfilter : (a^3).factorization.filter (fun p => 3 ≤ (a^3).factorization p)
      = (a^3).factorization := by
    apply Finsupp.ext
    intro p
    rw [Finsupp.filter_apply]
    simp_all
  rw [hfilter]
  exact Nat.prod_factorization_pow_eq_self hne

/-
The factorization of `rFullPart r M` at a prime `q`.
-/
theorem rFullPart_factorization (r M : ℕ) (q : ℕ) :
    (rFullPart r M).factorization q
      = if r ≤ M.factorization q then M.factorization q else 0 := by
  unfold rFullPart
  rw [Nat.prod_pow_factorization_eq_self]
  · rw [Finsupp.filter_apply]
  · simp_all

/-
If `d ^ 3 ∣ M` (and `M > 0`), then `d ^ 3 ∣ rFullPart 3 M`.
-/
theorem pow_dvd_rFullPart (M d : ℕ) (hM : 0 < M) (hd : d ^ 3 ∣ M) :
    d ^ 3 ∣ rFullPart 3 M := by
  have hd0 : d ^ 3 ≠ 0 := fun h => hM.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  rw [← Nat.factorization_le_iff_dvd hd0 hM.ne'] at hd
  rw [← Nat.factorization_le_iff_dvd hd0 (rFullPart_ne_zero 3 M), Finsupp.le_def]
  intro q
  have hq := Finsupp.le_def.mp hd q
  rw [rFullPart_factorization]
  rw [Nat.factorization_pow] at hq ⊢
  simp only [Finsupp.smul_apply, smul_eq_mul] at hq ⊢
  split_ifs with h <;> omega

/-! ## The key algebraic identity -/

theorem IDENT (t : ℕ) : Gpoly t ^ 3 + N ^ 3 = Hpoly t * Cpoly t ^ 3 := by
  unfold Gpoly Hpoly Cpoly N
  ring

/-! ## Polynomial congruence transfer -/

theorem Cpoly_modEq {a b M : ℕ} (h : a ≡ b [MOD M]) : Cpoly a ≡ Cpoly b [MOD M] := by
  unfold Cpoly; gcongr

theorem Gpoly_modEq {a b M : ℕ} (h : a ≡ b [MOD M]) : Gpoly a ≡ Gpoly b [MOD M] := by
  unfold Gpoly; gcongr

theorem Hpoly_modEq {a b M : ℕ} (h : a ≡ b [MOD M]) : Hpoly a ≡ Hpoly b [MOD M] := by
  unfold Hpoly; gcongr

/-! ## Concrete constant facts -/

theorem Gpoly_const_modN : Gpoly 23016 ≡ 0 [MOD N] := by
  unfold Gpoly N Nat.ModEq; norm_num

theorem Cpoly_const_mod2 : Cpoly 23016 % 2 = 1 := by
  unfold Cpoly; norm_num

theorem Cpoly_const_mod27 : Cpoly 23016 % 27 = 9 := by
  unfold Cpoly; norm_num

/-! ## Pure polynomial bounds -/

theorem Cpoly_gt (t : ℕ) : t^4 < Cpoly t := by
  exact lt_add_of_le_of_pos
    (Nat.le_add_right _ _ |> Nat.le_trans (Nat.le_add_right _ _))
    (by norm_num [ Cpoly ])

theorem Cpoly_cube_gt (t : ℕ) : t^12 < Cpoly t ^ 3 := by
  convert Nat.pow_lt_pow_left ( Cpoly_gt t ) three_ne_zero using 1; ring

theorem Gpoly_ge_const (t : ℕ) : 1474200 ≤ Gpoly t := by
  exact le_add_of_nonneg_left ( Nat.zero_le _ )

theorem Gpoly_div_pos (t : ℕ) : 1 ≤ Gpoly t / N := by
  exact Nat.div_pos
    (show N ≤ Gpoly t by exact le_trans ( by decide ) ( Gpoly_ge_const t ))
    (by decide)

theorem Gpoly_upper (t : ℕ) (ht : 1676 ≤ t) : Gpoly t ≤ 2 * t^9 := by
  unfold Gpoly
  nlinarith [Nat.pow_le_pow_left ht 2, Nat.pow_le_pow_left ht 3,
    Nat.pow_le_pow_left ht 4, Nat.pow_le_pow_left ht 5, Nat.pow_le_pow_left ht 6,
    Nat.pow_le_pow_left ht 7]

theorem Gpoly_cube_le (t : ℕ) (ht : 1676 ≤ t) : Gpoly t ^ 3 ≤ 8 * t^27 := by
  convert Nat.pow_le_pow_left ( Gpoly_upper t ht ) 3 using 1; ring

/-! ## T1 : `n` is `3`-full -/

theorem T1 (t : ℕ) : rFullPart 3 (nn t) = nn t := by
  unfold nn
  exact rFullPart_cube_eq _ (Gpoly_div_pos t)

/-! ## Main section: the prime-supply hypotheses -/

section
variable (s t₀ t : ℕ)
variable (hs : s.Prime) (hs6 : ¬ s ∣ 6)
variable (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ N * s ^ 3)
variable (hcong : t₀ % N = 23016 % N)
variable (hH : s ^ 3 ∣ Hpoly t₀) (hC : ¬ s ∣ Cpoly t₀)
variable (ht : t = t₀ + N * s ^ 3)

include hcong ht in
theorem t_mod_N : t ≡ 23016 [MOD N] := by
  simp +decide [ *, Nat.ModEq, Nat.add_mod ]

include ht in
theorem t_mod_s3 : t ≡ t₀ [MOD s^3] := by
  norm_num [ ht, Nat.ModEq, Nat.add_mod, Nat.mul_mod ]

include ht in
theorem t_mod_s : t ≡ t₀ [MOD s] := by
  norm_num [ ht, Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ]

include hH ht in
theorem hHt : s ^ 3 ∣ Hpoly t := by
  rw [ ← Nat.modEq_zero_iff_dvd ] at *; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
  simp_all +decide [ Hpoly ]

include hC ht in
theorem hCt : ¬ s ∣ Cpoly t := by
  rw [← ZMod.natCast_eq_zero_iff] at hC ⊢
  rw [ht]
  unfold Cpoly at *; simp_all +decide [ pow_succ, mul_assoc ]

include hcong ht in
theorem L1 : N ∣ Gpoly t := by
  have h_gt_mod : Gpoly t ≡ Gpoly 23016 [MOD N] :=
    Gpoly_modEq (t_mod_N s t₀ t hcong ht)
  exact (Nat.modEq_zero_iff_dvd).mp (h_gt_mod.trans Gpoly_const_modN)

include hcong ht in
theorem L2 : Cpoly t % 2 = 1 := by
  exact Cpoly_modEq (show t ≡ 23016 [MOD 2] by
    exact Nat.ModEq.of_dvd (by decide) (t_mod_N s t₀ t hcong ht))

include hcong ht in
theorem L3mod : Cpoly t % 27 = 9 := by
  rw [ ← Cpoly_const_mod27 ];
  rw [ ← Nat.mod_add_div t 27, ← Nat.mod_add_div 23016 27 ];
  norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Cpoly ]; ring_nf;
  rw [ ht ]; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hcong ];
  rw [ ← Nat.mod_mod_of_dvd t₀ ( by decide : 27 ∣ N ), hcong ]; norm_num [ N ];

include hcong ht in
theorem L3a : 9 ∣ Cpoly t := by
  have := L3mod s t₀ t hcong ht; omega;

include hcong ht in
theorem L3b : ¬ 27 ∣ Cpoly t := by
  rw [ Nat.dvd_iff_mod_eq_zero, L3mod s t₀ t hcong ht ]
  norm_num

include hs hs6 in
theorem hs_ge5 : 5 ≤ s := by
  contrapose! hs6; interval_cases s <;> trivial;

include ht in
theorem Ns3_le_t : N * s^3 ≤ t := by
  linarith

include ht ht₀ in
theorem t_le_2Ns3 : t ≤ 2 * (N * s ^ 3) := by
  linarith

include ht hs hs6 in
theorem t_big : 1676 ≤ t := by
  exact ht.symm ▸
    le_add_of_nonneg_of_le (Nat.zero_le _) (by
      exact le_trans (by decide)
        (Nat.mul_le_mul_left _
          (pow_le_pow_left' (show s ≥ 5 by
            contrapose! hs6
            interval_cases s <;> trivial) 3)))

include hcong ht in
theorem N3_mul_nn : N ^ 3 * nn t = Gpoly t ^ 3 := by
  rw [ nn ];
  rw [ ← mul_pow, Nat.mul_div_cancel' ( L1 s t₀ t hcong ht ) ]

include hcong ht in
theorem T0 : N ^ 3 * (nn t + 1) = Hpoly t * Cpoly t ^ 3 := by
  rw [ ← IDENT t, mul_add, mul_one ];
  rw [ ← N3_mul_nn ];
  exacts [ s, t₀, hcong, ht ]

include hcong ht in
theorem T0_div : nn t + 1 = Hpoly t * Cpoly t ^ 3 / N ^ 3 := by
  exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( by decide ) ( by linarith [ T0 s t₀ t hcong ht ] ) )

include hcong ht in
theorem Ctil_eq : Cpoly t = 9 * (Cpoly t / 9) := by
  rw [ Nat.mul_div_cancel' ( show 9 ∣ Cpoly t from ?_ ) ];
  convert L3a s t₀ t hcong ht using 1

include hC ht hs hcong in
theorem Ctil_coprime_s : Nat.Coprime (Cpoly t / 9) s := by
  -- By definition of $Ctil$, we know that $Ctil = Cpoly t / 9$.
  set Ctil := Cpoly t / 9 with hCtil_def
  have hCtil_dvd : Ctil ∣ Cpoly t := by
    exact Nat.div_dvd_of_dvd <| L3a _ _ t hcong ht
  have hCtil_not_dvd : ¬ s ∣ Ctil := by
    have := hCt s t₀ t hC ht; ( contrapose! this; );
    exact dvd_trans this hCtil_dvd
  have hCtil_coprime : Nat.Coprime s Ctil := by
    exact hs.coprime_iff_not_dvd.mpr hCtil_not_dvd
  exact hCtil_coprime.symm

end

end Core4027
