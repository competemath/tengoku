/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/
module

public import Tengoku

public import Tengoku.LeanPool.LeanPool.KasamiCyclicAdditive.Statement.Definitions

/-!
# Frobenius transport between complementary parameters

Since the Kasami parameters `k` and `n - k` are related by a Frobenius twist,
the two derivative images `Δ_k` and `Δ_(n-k)` have the same cardinality.  This
is what lets the half-size fact be proved for odd `k` only and then transported
to the even case, where coprimality forces `n - k` to be odd.

Also recorded here is the elementary fact that `0 ∈ Δ_k` for every `k` (take
the derivative parameter `b = 0`), and the packaging of the half-size fact into
the derivative-image half-size equation at both `k` and the complementary
parameter `n - k`.
-/

@[expose] public section

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-! ### The complementary Frobenius equivalence -/

/-- The Frobenius map used to transport data from parameter `n - k` to `k`.

The parameter `n` is not needed to define the equivalence; it enters only in
the identity below relating the Kasami exponents at `k` and `n - k`. -/
noncomputable def complementFrobeniusEquiv (k : ℕ) : K ≃+* K := by
  have hinj : Function.Injective (iterateFrobenius K 2 (2 * k)) := RingHom.injective _
  have hbij : Function.Bijective (iterateFrobenius K 2 (2 * k)) :=
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  exact RingEquiv.ofBijective (iterateFrobenius K 2 (2 * k)) hbij

omit [DecidableEq K] in
/-- `complementFrobeniusEquiv k` acts as the `2 ^ (2k)`-power Frobenius.
@isnad1 id=eq.0h3v.s8.014cdf1f87f5 from=translated src=- shape=ce8ce874 vocab=a8b07967
-/
@[simp] theorem complementFrobeniusEquiv_apply (k : ℕ) (x : K) :
    complementFrobeniusEquiv k x = iterateFrobenius K 2 (2 * k) x := rfl

/-! ### Frobenius transport of the derivative image -/

/-- The Kasami exponent over `ℤ`, free of truncated subtraction.
@isnad1 id=eq.0h1v.s6.660bbe3ad934 from=translated src=- shape=b155b08b vocab=6fb00dde
-/
theorem kasamiExponent_cast (k : ℕ) :
    ((kasamiExponent k : ℕ) : ℤ) = 4 ^ k - 2 ^ k + 1 := by
  have h : (2 : ℕ) ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
  unfold kasamiExponent
  push_cast [Nat.cast_sub h]
  ring

/-- `2 ^ (2k)` times the complementary Kasami exponent differs from the Kasami
exponent at `k` by a multiple of `2 ^ n - 1`.
@isnad1 id=eq.1h2v.s7.e620df29b87f from=translated src=- shape=f7e3d078 vocab=cfb83c5f
-/
theorem kasamiExponent_complement {n k : ℕ} (hk : k ≤ n) :
    2 ^ (2 * k) * kasamiExponent (n - k)
      = kasamiExponent k + (2 ^ n - 1) * ((2 ^ n - 2 ^ k) + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : (1 : ℕ) ≤ 2 ^ (k + j) := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ k ≤ 2 ^ (k + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkj : k + j - k = j := by omega
  rw [hkj]
  have hZ : ((2 ^ (2 * k) * kasamiExponent j : ℕ) : ℤ)
      = ((kasamiExponent k + (2 ^ (k + j) - 1) * ((2 ^ (k + j) - 2 ^ k) + 1) : ℕ) : ℤ) := by
    push_cast [kasamiExponent_cast, Nat.cast_sub h1, Nat.cast_sub h2]
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, pow_add]
    ring
  exact_mod_cast hZ

omit [DecidableEq K] [CharP K 2] in
/-- Exponents may be shifted by multiples of `#K - 1` on all of `K`.
@isnad1 id=eq.1h4v.s6.14faa2de4e19 from=translated src=- shape=5ac9fb90 vocab=15c1f955
-/
theorem pow_add_card_sub_one_mul (x : K) (e c : ℕ) (he : e ≠ 0) :
    x ^ (e + (Fintype.card K - 1) * c) = x ^ e := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_pow he, zero_pow (by positivity)]
  · rw [pow_add, pow_mul, FiniteField.pow_card_sub_one_eq_one x hx, one_pow, mul_one]

omit [DecidableEq K] [CharP K 2] in
/-- On a field of order `2 ^ n` the two exponents therefore act alike:
`x ^ (d_(n-k) * 2 ^ (2k)) = x ^ d_k`.
@isnad1 id=eq.2h4v.s7.7aed0f9e00dd from=translated src=- shape=bcd38f5d vocab=cf380e8b
-/
theorem pow_kasamiExponent_complement {n k : ℕ} (hk : k ≤ n)
    (hcard : Fintype.card K = 2 ^ n) (x : K) :
    x ^ (kasamiExponent (n - k) * 2 ^ (2 * k)) = x ^ kasamiExponent k := by
  rw [mul_comm, kasamiExponent_complement hk, ← hcard]
  exact pow_add_card_sub_one_mul x _ _ (by simp [kasamiExponent])

omit [DecidableEq K] in
/-- The derivative at `k` is the `2 ^ (2k)`-power Frobenius image of the
derivative at `n - k`.
@isnad1 id=eq.2h4v.s7.169d2ebfcb56 from=translated src=- shape=beb6b4b0 vocab=368d80c9
-/
theorem kasamiDerivative_complement {n k : ℕ} (hk : k ≤ n)
    (hcard : Fintype.card K = 2 ^ n) (b : K) :
    kasamiDerivative k b = iterateFrobenius K 2 (2 * k) (kasamiDerivative (n - k) b) := by
  rw [kasamiDerivative, kasamiDerivative, map_add, map_add, map_one, iterateFrobenius_def,
    iterateFrobenius_def, ← pow_mul, ← pow_mul,
    pow_kasamiExponent_complement hk hcard,
    pow_kasamiExponent_complement hk hcard]

/-- The complementary derivative image is the Frobenius image of the original
derivative image.
@isnad1 id=eq.2h3v.s7.2aaad1a086a2 from=translated src=- shape=40a16bfb vocab=273defab
-/
theorem derivativeImage_complement_eq_image {n k : ℕ} (hk : k ≤ n)
    (hcard : Fintype.card K = 2 ^ n) :
    derivativeImage k K =
      (derivativeImage (n - k) K).image (complementFrobeniusEquiv k) := by
  let e : K ≃+* K := complementFrobeniusEquiv k
  have hdt : ∀ b : K, kasamiDerivative k b = e (kasamiDerivative (n - k) b) := by
    intro b
    rw [complementFrobeniusEquiv_apply]
    exact kasamiDerivative_complement hk hcard b
  ext x
  simp only [derivativeImage, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨kasamiDerivative (n - k) b, ⟨b, rfl⟩, by rw [hdt b]⟩
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, by rw [hdt b]⟩

/-- Frobenius transport preserves the size of the Kasami derivative image:
`|Δ_k| = |Δ_(n-k)|`.
@isnad1 id=eq.2h3v.s6.aca1526a0adc from=translated src=- shape=64f03ca6 vocab=f4a00ae4
-/
theorem card_derivativeImage_complement {n k : ℕ} (hk : k ≤ n)
    (hcard : Fintype.card K = 2 ^ n) :
    (derivativeImage k K).card = (derivativeImage (n - k) K).card := by
  rw [derivativeImage_complement_eq_image hk hcard,
    Finset.card_image_of_injective _ (complementFrobeniusEquiv k).injective]

/-! ### Zero always lies in the derivative image -/

/-- Zero belongs to every Kasami derivative image.
@isnad1 id=mem.0h2v.s5.36e1167e43a7 from=translated src=- shape=2d6eebbc vocab=c0a17d6d
-/
theorem zero_mem_derivativeImage (k : ℕ) : (0 : K) ∈ derivativeImage k K := by
  have hd : kasamiExponent k ≠ 0 := by simp [kasamiExponent]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [derivativeImage]
  refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
  rw [kasamiDerivative, zero_add, one_pow, zero_pow hd]
  linear_combination h2

end KasamiCyclicAdditive
