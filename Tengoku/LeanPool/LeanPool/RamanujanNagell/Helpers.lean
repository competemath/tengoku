/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/
module

public import Tengoku

/-!
# Algebraic infrastructure for `R = QuadraticAlgebra ℤ (-2) 1 = ℤ[(1+√-7)/2]`

Following Michael Stoll's suggestion to work directly in `QuadraticAlgebra ℤ (-2) 1`
rather than through `𝓞 K` where `K = QuadraticAlgebra ℚ (-2) 1`. The payoff:

* `θ ^ 2 = θ - 2`, `θ * θ' = 2`, `θ + θ' = 1`, `norm θ = 2`, `norm θ' = 2`
  are all literal `rfl`s (no `Subtype.ext` ceremony, no
  `omega_mul_omega_eq_mk`).
* `units_pm_one` reduces to a one-page completing-the-square argument over ℤ.
* `EuclideanDomain R → IsPrincipalIdealRing R → UniqueFactorizationMonoid R`
  replaces the discriminant / class-number-1 detour through Dirichlet.
-/

@[expose] public section

namespace RamanujanNagell

open QuadraticAlgebra

/-- The integer ring `ℤ[(1 + √-7)/2]`, packaged as `QuadraticAlgebra ℤ (-2) 1`. -/
abbrev R : Type := QuadraticAlgebra ℤ (-2) 1

/-- `θ = (1 + √-7)/2`, the generator of `R`. -/
def θ : R := ⟨0, 1⟩

/-- `θ' = (1 - √-7)/2 = 1 - θ`, the Galois conjugate of `θ`. -/
def θ' : R := ⟨1, -1⟩

/-! ## Stoll's `rfl` claims -/

/--
@isnad1 id=eq.0h0v.s6.8932a3d5e55b from=translated src=- shape=7dc6ab06 vocab=87a2aca0
-/
lemma theta_sq : θ ^ 2 = θ - 2 := rfl

/--
@isnad1 id=eq.0h0v.s5.3031391a0b8c from=translated src=- shape=33aceabd vocab=874d8836
-/
lemma theta_mul_theta' : θ * θ' = 2 := rfl

/--
@isnad1 id=eq.0h0v.s5.e6ddb6c30ddb from=translated src=- shape=33aceabd vocab=f78f8e91
-/
lemma theta_add_theta' : θ + θ' = 1 := rfl

/--
@isnad1 id=eq.0h0v.s5.677cbbe54605 from=translated src=- shape=f464b020 vocab=351f0cc1
-/
lemma theta'_eq_one_sub_theta : θ' = 1 - θ := rfl

/-- For backward compatibility with the old Helpers API.
@isnad1 id=eq.0h0v.s6.bbe45756e696 from=translated src=- shape=4909fd7e vocab=0317b9e8
-/
lemma two_factorisation_R : θ * (1 - θ) = 2 := rfl

/-! ## Norm form and positivity

`norm ⟨x, y⟩ = x² + xy + 2y²`; the key identity is `4·N = (2x + y)² + 7y²`. -/

/--
@isnad1 id=eq.0h2v.s8.adf0cdd7686e from=translated src=- shape=604b4a28 vocab=687c12ea
-/
lemma norm_eq (x y : ℤ) : QuadraticAlgebra.norm (⟨x, y⟩ : R) = x ^ 2 + x * y + 2 * y ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

/-- The completing-the-square identity.
@isnad1 id=eq.0h1v.s8.63b90ade54c6 from=translated src=- shape=4ad0708f vocab=c3596174
-/
lemma four_norm_eq (z : R) :
    4 * QuadraticAlgebra.norm z = (2 * z.re + z.im) ^ 2 + 7 * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

/--
@isnad1 id=le.0h1v.s8.61bb1ced1f41 from=translated src=- shape=016b060b vocab=d54873c0
-/
lemma norm_nonneg (z : R) : 0 ≤ QuadraticAlgebra.norm z := by
  have h := four_norm_eq z
  have h1 : 0 ≤ (2 * z.re + z.im) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 7 * z.im ^ 2 := by positivity
  linarith

/--
@isnad1 id=iff.0h1v.s8.61dc8ee67d64 from=translated src=- shape=7c95c982 vocab=33e79ba7
-/
lemma norm_eq_zero_iff (z : R) : QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ QuadraticAlgebra.norm_zero⟩
  have h4 := four_norm_eq z
  rw [h] at h4
  have hv : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]
  have hu : z.re = 0 := by nlinarith [h4, hv, sq_nonneg z.re]
  exact QuadraticAlgebra.ext hu hv

/--
@isnad1 id=lt.1h1v.s8.81481f71aa82 from=translated src=- shape=696ee058 vocab=f3c3a7c2
-/
lemma norm_pos {z : R} (hz : z ≠ 0) : 0 < QuadraticAlgebra.norm z := by
  rcases lt_or_eq_of_le (norm_nonneg z) with h | h
  · exact h
  · exact absurd ((norm_eq_zero_iff z).mp h.symm) hz

/-! ## Units are ±1 -/

/--
@isnad1 id=or.0h1v.s8.e3462ac6934f from=translated src=- shape=b8546b79 vocab=a964f6e2
-/
lemma units_pm_one (u : Rˣ) : u = 1 ∨ u = -1 := by
  have hunit : IsUnit (QuadraticAlgebra.norm (u : R)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  rcases Int.isUnit_iff.mp hunit with hn | hn
  · set x := (u : R).re
    set y := (u : R).im
    have hcoord : (u : R) = ⟨x, y⟩ := by apply QuadraticAlgebra.ext <;> rfl
    have hn' : x ^ 2 + x * y + 2 * y ^ 2 = 1 := by
      rw [← norm_eq, ← hcoord]; exact hn
    have h_csq : (2 * x + y) ^ 2 + 7 * y ^ 2 = 4 := by linarith
    have hy : y = 0 := by nlinarith [sq_nonneg y, sq_nonneg (2 * x + y)]
    have hx2 : x ^ 2 = 1 := by nlinarith
    have hx : x = 1 ∨ x = -1 := by
      simp_all
    rcases hx with hx1 | hx1
    · exact Or.inl (Units.ext (by rw [hcoord, hx1, hy]; rfl))
    · exact Or.inr (Units.ext (by rw [hcoord, hx1, hy]; rfl))
  · exfalso
    have := norm_nonneg (u : R)
    omega

/-! ## θ and θ' are irreducible -/

private lemma norm_factor_dichotomy {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m * n = 2) :
    m = 1 ∨ n = 1 := by
  have hm_pos : 0 < m := by rcases hm.lt_or_eq with h | h; exacts [h, by simp [← h] at hmn]
  have hn_pos : 0 < n := by rcases hn.lt_or_eq with h | h; exacts [h, by simp [← h] at hmn]
  have hm_le : m ≤ 2 := by nlinarith
  interval_cases m
  · left; rfl
  · right; linarith

private lemma isUnit_of_norm_one {a : R} (h : QuadraticAlgebra.norm a = 1) : IsUnit a := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  rw [h]; exact isUnit_one

private lemma irreducible_of_norm_two {z : R} (hz : QuadraticAlgebra.norm z = 2) :
    Irreducible z := by
  refine ⟨?_, ?_⟩
  · intro hu
    have h2 : IsUnit (2 : ℤ) := hz ▸ QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    exact absurd (Int.isUnit_iff.mp h2) (by decide)
  · intro a b hab
    have hnab : QuadraticAlgebra.norm a * QuadraticAlgebra.norm b = 2 := by
      rw [← map_mul, ← hab]; exact hz
    rcases norm_factor_dichotomy (norm_nonneg a) (norm_nonneg b) hnab with h | h
    · exact Or.inl (isUnit_of_norm_one h)
    · exact Or.inr (isUnit_of_norm_one h)

/--
@isnad1 id=irreduci.0h0v.s4.23eaa3d3c6ef from=translated src=- shape=25b03439 vocab=6b6bd3b7
-/
lemma theta_irreducible : Irreducible θ := irreducible_of_norm_two rfl

/--
@isnad1 id=irreduci.0h0v.s4.dbaf6dd15373 from=translated src=- shape=25b03439 vocab=d4fe5113
-/
lemma theta'_irreducible : Irreducible θ' := irreducible_of_norm_two rfl

/-! ## EuclideanDomain instance via smart rounding

`R = ℤ[(1+√-7)/2]` with norm `N(x, y) = x² + xy + 2y²`. To divide `a` by `b ≠ 0`,
we want `q` such that `N(a - b·q) < N(b)`. Naive independent rounding of `(a/b)`
in the `(re, im)` basis can leave `N = 1` exactly at the fundamental-domain
corner; the fix is to round `im` first, then re-round `re` shifted by half the
`im` residual. With that choice `16·N(rem) ≤ 11·N(b)`. -/

private lemma b_mul_star_eq_norm (b : R) :
    b * star b = ((QuadraticAlgebra.norm b : ℤ) : R) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.norm_def, Int.cast_id]
    ring
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.im_intCast]
    ring

private lemma N_mul_rem_eq (a b q : R) :
    ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q) =
      b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hbs := b_mul_star_eq_norm b
  calc ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)
      = (b * star b) * (a - b * q) := by rw [← hbs]
    _ = b * (a * star b - (b * star b) * q) := by ring
    _ = b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by rw [hbs]

private lemma N_mul_norm_rem_eq (a b q : R) (hb : b ≠ 0) :
    QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q) =
      QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hN_ne : QuadraticAlgebra.norm b ≠ 0 := hN_pos.ne'
  have h_key := N_mul_rem_eq a b q
  have h_norm : QuadraticAlgebra.norm
      (((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)) =
      QuadraticAlgebra.norm
      (b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q)) := by
    rw [h_key]
  rw [map_mul, map_mul, QuadraticAlgebra.norm_intCast] at h_norm
  have h_sq : (QuadraticAlgebra.norm b) ^ 2 =
              QuadraticAlgebra.norm b * QuadraticAlgebra.norm b := sq _
  have : QuadraticAlgebra.norm b *
         (QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q)) =
         QuadraticAlgebra.norm b *
         QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
    rwa [← mul_assoc, ← h_sq]
  exact mul_left_cancel₀ hN_ne this

/-- Smart-rounded quotient. -/
noncomputable def quot (a b : R) : R :=
  let N : ℤ := QuadraticAlgebra.norm b
  if N = 0 then 0
  else
    let s : R := a * star b
    let n : ℤ := round ((s.im : ℚ) / N)
    let m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N))
    ⟨m, n⟩

/-- Smart-rounded remainder: `rem a b = a - b * quot a b`. -/
noncomputable def rem (a b : R) : R := a - b * quot a b

/--
@isnad1 id=eq.0h1v.s5.fd88c28adbe4 from=translated src=- shape=1d838610 vocab=486d07ea
-/
@[simp] lemma quot_zero (a : R) : quot a 0 = 0 := by unfold quot; simp

/--
@isnad1 id=eq.0h2v.s5.f6edc9c8956e from=translated src=- shape=d5e8f1fa vocab=15dc10ac
-/
lemma quot_mul_add_rem_eq (a b : R) : b * quot a b + rem a b = a := by
  unfold rem; ring

private lemma sq_le_of_round_eq {N w : ℤ} {r : ℚ} (h2N : (0 : ℚ) < 2 * N)
    (habs : |r| ≤ 1 / 2) (heq : r * (2 * N) = ((w : ℤ) : ℚ)) : w ^ 2 ≤ N ^ 2 := by
  have h_abs : |((w : ℤ) : ℚ)| ≤ N := by
    rw [← heq, abs_mul, abs_of_pos h2N]
    have := mul_le_mul_of_nonneg_right habs h2N.le
    linarith
  have h_sq : ((w : ℤ) : ℚ) ^ 2 ≤ (N : ℚ) ^ 2 := by
    rw [(sq_abs ((w : ℤ) : ℚ)).symm]
    exact sq_le_sq' (by linarith [abs_nonneg ((w : ℤ) : ℚ)]) h_abs
  exact_mod_cast h_sq

private lemma sixteen_norm_rem_le (a b : R) (hb : b ≠ 0) :
    16 * QuadraticAlgebra.norm (rem a b) ≤ 11 * QuadraticAlgebra.norm b := by
  set N := QuadraticAlgebra.norm b with hN_def
  have hN_pos : 0 < N := norm_pos hb
  have hN_ne : N ≠ 0 := hN_pos.ne'
  set s : R := a * star b with hs_def
  set n : ℤ := round ((s.im : ℚ) / N) with hn_def
  set m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N)) with hm_def
  have hquot : quot a b = (⟨m, n⟩ : R) := by
    change (if QuadraticAlgebra.norm b = 0 then (0 : R) else _) = _
    rw [ite_eq_right hN_ne]
  set u : ℤ := s.re - N * m with hu_def
  set v : ℤ := s.im - N * n with hv_def
  have hNq_pos : (0 : ℚ) < N := by exact_mod_cast hN_pos
  have hNq : (N : ℚ) ≠ 0 := hNq_pos.ne'
  have h2Nq_pos : (0 : ℚ) < 2 * N := by linarith
  have hv_bd : (2 * v) ^ 2 ≤ N ^ 2 :=
    sq_le_of_round_eq h2Nq_pos (abs_sub_round ((s.im : ℚ) / N))
      (by rw [← hn_def]; push_cast [hv_def]; field_simp)
  have huv_bd : (2 * u + v) ^ 2 ≤ N ^ 2 :=
    sq_le_of_round_eq h2Nq_pos (abs_sub_round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N)))
      (by rw [← hm_def]; push_cast [hu_def, hv_def]; field_simp; ring)
  have h_chain : N * QuadraticAlgebra.norm (rem a b) = u ^ 2 + u * v + 2 * v ^ 2 := by
    unfold rem
    rw [hquot]
    have h := N_mul_norm_rem_eq a b (⟨m, n⟩ : R) hb
    rw [h]
    have hre : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).re = u := by
      simp_all
    have him : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).im = v := by
      simp_all
    rw [QuadraticAlgebra.norm_def, hre, him]; ring
  have h_bd : 16 * (u ^ 2 + u * v + 2 * v ^ 2) ≤ 11 * N ^ 2 := by
    nlinarith [hv_bd, huv_bd]
  nlinarith [h_chain, h_bd, hN_pos, sq N]

/-- The natural absolute value of the quadratic-algebra norm. -/
noncomputable def normMeasure (a : R) : ℕ := Int.natAbs (QuadraticAlgebra.norm a)

private lemma natAbs_norm_rem_lt (a : R) {b : R} (hb : b ≠ 0) :
    normMeasure (rem a b) < normMeasure b := by
  unfold normMeasure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hr_nn : 0 ≤ QuadraticAlgebra.norm (rem a b) := norm_nonneg _
  have h_bd := sixteen_norm_rem_le a b hb
  have hr_lt : QuadraticAlgebra.norm (rem a b) < QuadraticAlgebra.norm b := by linarith
  zify
  rwa [abs_of_nonneg hr_nn, abs_of_nonneg hN_pos.le]

private lemma norm_mul_left_not_lt (a : R) {b : R} (hb : b ≠ 0) :
    ¬ normMeasure (a * b) < normMeasure a := by
  unfold normMeasure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have ha_nn : 0 ≤ QuadraticAlgebra.norm a := norm_nonneg a
  have hab : QuadraticAlgebra.norm (a * b) =
             QuadraticAlgebra.norm a * QuadraticAlgebra.norm b := map_mul _ _ _
  have hab_nn : 0 ≤ QuadraticAlgebra.norm (a * b) := hab ▸ mul_nonneg ha_nn hN_pos.le
  intro h
  zify at h
  rw [abs_of_nonneg hab_nn, abs_of_nonneg ha_nn, hab] at h
  nlinarith [ha_nn, hN_pos]

/-- `R` is a Euclidean domain. Division of `a` by `b ≠ 0` uses smart rounding of
`a · star b / N(b)` (round the `im` coordinate first, then shift-round `re`),
which guarantees `16 · N(rem) ≤ 11 · N(b)`, hence a strictly smaller norm. -/
noncomputable instance instEuclideanDomain : EuclideanDomain R where
  quotient := quot
  quotient_zero := quot_zero
  remainder := rem
  quotient_mul_add_remainder_eq := quot_mul_add_rem_eq
  r := fun a b => normMeasure a < normMeasure b
  r_wellFounded := (measure normMeasure).wf
  remainder_lt := by exact natAbs_norm_rem_lt
  mul_left_not_lt := by exact norm_mul_left_not_lt

/-- `R` is a principal ideal ring, since every Euclidean domain is one.
@isnad1 id=isprinci.0h0v.s4.0d682b35b077 from=translated src=- shape=49959d42 vocab=868110b8
-/
instance instPrincipalIdealRing : IsPrincipalIdealRing R :=
  EuclideanDomain.instIsPrincipalIdealRing

/-- `R` is a unique factorization domain, since every principal ideal ring is one.
@isnad1 id=uniquefa.0h0v.s4.8ae871719602 from=translated src=- shape=49959d42 vocab=cb444f91
-/
instance instUniqueFactorizationMonoid : UniqueFactorizationMonoid R := inferInstance

/-! ## θ, θ' are prime -/

/--
@isnad1 id=prime.0h0v.s4.9104830d0e5d from=translated src=- shape=25b03439 vocab=33a10d2a
-/
lemma theta_prime : Prime θ :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta_irreducible

/--
@isnad1 id=prime.0h0v.s4.8d61406f3711 from=translated src=- shape=25b03439 vocab=8f420d44
-/
lemma theta'_prime : Prime θ' :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta'_irreducible

/-! ## UFD scaffolding for the Ramanujan-Nagell argument

These lemmas combine `units_pm_one` with `UniqueFactorizationMonoid R` to give
the key dichotomy `α * β = θ^m · θ'^m ∧ IsCoprime α β → α = ±θ^m ∨ α = ±θ'^m`. -/

/--
@isnad1 id=not.0h0v.s4.ba106f208cc4 from=translated src=- shape=6516253f vocab=7d5d3287
-/
lemma theta_theta'_not_associated : ¬ Associated θ θ' := by
  rintro ⟨u, hu⟩
  rcases units_pm_one u with rfl | rfl <;>
    · have h := congrArg QuadraticAlgebra.re hu
      simp [θ, θ'] at h

/--
@isnad1 id=not.0h0v.s5.b2210d606043 from=translated src=- shape=6516253f vocab=8fa992a0
-/
lemma theta_not_dvd_theta' : ¬ (θ ∣ θ') := by
  intro h
  exact theta_theta'_not_associated (theta_irreducible.associated_of_dvd theta'_irreducible h)

/--
@isnad1 id=not.0h0v.s5.b37adea8fd15 from=translated src=- shape=6516253f vocab=8fa992a0
-/
lemma theta'_not_dvd_theta : ¬ (θ' ∣ θ) := by
  intro h
  exact theta_theta'_not_associated
    (theta'_irreducible.associated_of_dvd theta_irreducible h).symm

/--
@isnad1 id=or.2h3v.s8.227bc3ca07a7 from=translated src=- shape=49e5188c vocab=e746a0fd
-/
lemma theta_pow_dvd_of_coprime_prod (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β) :
    θ ^ m ∣ α ∨ θ ^ m ∣ β := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Or.inl (one_dvd α)
  have hθ_prime : _root_.Prime θ := theta_prime
  have h_dvd_prod : θ ^ m ∣ α * β := h_prod ▸ dvd_mul_right (θ ^ m) (θ' ^ m)
  have h_dvd_or : θ ∣ α ∨ θ ∣ β :=
    hθ_prime.dvd_or_dvd (dvd_trans (dvd_pow_self θ (by omega)) h_dvd_prod)
  rcases h_dvd_or with h_dvd_α | h_dvd_β
  · have h_not_dvd_β : ¬ (θ ∣ β) := fun h_dvd_β =>
      hθ_prime.not_isUnit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inl (hθ_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_β h_dvd_prod)
  · have h_not_dvd_α : ¬ (θ ∣ α) := fun h_dvd_α =>
      hθ_prime.not_isUnit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inr (hθ_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_α h_dvd_prod)

/--
@isnad1 id=associat.5h3v.s8.ec24509d6258 from=translated src=- shape=989a2b50 vocab=b58a0e28
-/
lemma associated_of_theta_pow_dvd (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (_hα : ¬IsUnit α) (hβ : ¬IsUnit β)
    (h_dvd : θ ^ m ∣ α) :
    Associated α (θ ^ m) := by
  obtain ⟨γ, hγ⟩ := h_dvd
  have hθm_ne : θ ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta_irreducible)
  have hθ'm_ne : θ' ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta'_irreducible)
  have h_cancel : γ * β = θ' ^ m := by
    have h1 := h_prod
    rw [hγ, mul_assoc] at h1
    exact mul_left_cancel₀ hθm_ne h1
  have hθ'_prime : _root_.Prime θ' := theta'_prime
  have h_not_dvd_γ : ¬ (θ' ∣ γ) := by
    intro h_dvd_γ
    have h_dvd_α : θ' ∣ α := hγ ▸ dvd_mul_of_dvd_right h_dvd_γ (θ ^ m)
    have h_not_dvd_β : ¬ (θ' ∣ β) := fun h_dvd_β =>
      hθ'_prime.not_isUnit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    have h_dvd_prod : θ' ^ m ∣ γ * β := h_cancel ▸ dvd_refl (θ' ^ m)
    have h_θ'_pow_dvd_γ : θ' ^ m ∣ γ :=
      hθ'_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_β h_dvd_prod
    obtain ⟨δ, hδ⟩ := h_θ'_pow_dvd_γ
    have h_eq := h_cancel
    rw [hδ, mul_assoc] at h_eq
    have h_δβ : δ * β = 1 := by
      simp_all
    exact hβ (IsUnit.of_mul_eq_one δ (by rw [mul_comm]; exact h_δβ))
  have h_dvd_prod : θ' ^ m ∣ γ * β := h_cancel ▸ dvd_refl (θ' ^ m)
  have h_θ'_dvd_β : θ' ^ m ∣ β :=
    hθ'_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_γ h_dvd_prod
  obtain ⟨ε, hε⟩ := h_θ'_dvd_β
  have h_eq := h_cancel
  rw [hε, ← mul_assoc, mul_comm γ (θ' ^ m), mul_assoc] at h_eq
  have h_γε : γ * ε = 1 := by
    simp_all
  have hγ_unit : IsUnit γ := IsUnit.of_mul_eq_one ε h_γε
  rw [hγ]
  exact associated_mul_unit_left (θ ^ m) γ hγ_unit

/--
@isnad1 id=associat.5h3v.s8.c6a6610f1851 from=translated src=- shape=eb210ab5 vocab=b58a0e28
-/
lemma associated_of_theta_pow_dvd_right (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (_hβ : ¬IsUnit β)
    (h_dvd : θ ^ m ∣ β) :
    Associated α (θ' ^ m) := by
  obtain ⟨γ, hγ⟩ := h_dvd
  have hθm_ne : θ ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta_irreducible)
  have hθ'm_ne : θ' ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta'_irreducible)
  have h_cancel : α * γ = θ' ^ m := by
    have h1 := h_prod
    rw [hγ, ← mul_assoc, mul_comm α (θ ^ m), mul_assoc] at h1
    exact mul_left_cancel₀ hθm_ne h1
  have hθ'_prime : _root_.Prime θ' := theta'_prime
  have h_not_dvd_γ : ¬ (θ' ∣ γ) := by
    intro h_dvd_γ
    have h_dvd_β : θ' ∣ β := hγ ▸ dvd_mul_of_dvd_right h_dvd_γ (θ ^ m)
    have h_not_dvd_α : ¬ (θ' ∣ α) := fun h_dvd_α =>
      hθ'_prime.not_isUnit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    have h_dvd_prod : θ' ^ m ∣ α * γ := h_cancel ▸ dvd_refl (θ' ^ m)
    have h_θ'_pow_dvd_γ : θ' ^ m ∣ γ :=
      hθ'_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_α h_dvd_prod
    obtain ⟨δ, hδ⟩ := h_θ'_pow_dvd_γ
    have h_eq := h_cancel
    rw [hδ, ← mul_assoc, mul_comm α (θ' ^ m), mul_assoc] at h_eq
    have h_αδ : α * δ = 1 := by
      simp_all
    exact hα (IsUnit.of_mul_eq_one δ h_αδ)
  have h_dvd_prod : θ' ^ m ∣ α * γ := h_cancel ▸ dvd_refl (θ' ^ m)
  have h_θ'_dvd_α : θ' ^ m ∣ α :=
    hθ'_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_γ h_dvd_prod
  obtain ⟨ε, hε⟩ := h_θ'_dvd_α
  have h_eq := h_cancel
  rw [hε, mul_assoc] at h_eq
  have h_εγ : ε * γ = 1 := by
    simp_all
  have hε_unit : IsUnit ε := IsUnit.of_mul_eq_one γ h_εγ
  rw [hε]
  exact associated_mul_unit_left (θ' ^ m) ε hε_unit

/--
@isnad1 id=or.4h3v.s8.6125f702317a from=translated src=- shape=2619ca67 vocab=af21160d
-/
lemma ufd_associated_dichotomy (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β) :
    Associated α (θ ^ m) ∨ Associated α (θ' ^ m) := by
  rcases theta_pow_dvd_of_coprime_prod α β m h_prod h_coprime with h | h
  · exact Or.inl (associated_of_theta_pow_dvd α β m h_prod h_coprime hα hβ h)
  · exact Or.inr (associated_of_theta_pow_dvd_right α β m h_prod h_coprime hα hβ h)

/--
@isnad1 id=or.1h2v.s5.e75c242dfad8 from=translated src=- shape=1d31b535 vocab=e919e667
-/
lemma associated_eq_or_neg (α γ : R) (h : Associated α γ) :
    α = γ ∨ α = -γ := by
  rcases h with ⟨u, rfl⟩
  rcases units_pm_one u with rfl | rfl
  · left; simp
  · right; simp

/--
@isnad1 id=or.4h3v.s8.f8cb3253a1e7 from=translated src=- shape=ddca0880 vocab=fa85ec89
-/
lemma ufd_power_association (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β) :
    (α = θ ^ m ∨ α = -(θ ^ m)) ∨ (α = θ' ^ m ∨ α = -(θ' ^ m)) := by
  have h_assoc := ufd_associated_dichotomy α β m h_prod h_coprime hα hβ
  rcases h_assoc with h_left | h_right
  · left; exact associated_eq_or_neg α (θ ^ m) h_left
  · right; exact associated_eq_or_neg α (θ' ^ m) h_right

end RamanujanNagell
