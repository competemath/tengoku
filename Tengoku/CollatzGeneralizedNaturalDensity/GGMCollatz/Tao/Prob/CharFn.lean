import Tengoku.CollatzGeneralizedNaturalDensity.GGMCollatz.Tao.Prob.LocalBound
import Tengoku.Seed.Analysis.Fourier.ZMod
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite circle method: characteristic functions on `ZMod N × ZMod N` (counterpart of node S3 of tao-collatz)

Derived from `TaoCollatz/Prob/CharFn.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r). The content of this file consists of general PMF lemmas that do not
depend on `p`, `q`, `r`, so the body is unchanged (only the namespace is `GGMCollatz`).

The Fourier inversion integral over `[-π,π]²` in the proof of Lemma 2.2 of Tao 2019 (pp.15–16) is replaced by
finite Fourier inversion on the group `ZMod N × ZMod N` (all sums finite, no measure theory):
```
r x = N⁻² ∑_ξ  r̂(ξ) e(-ξ·x),      r̂(ξ) = ∑_y r y · e(ξ·y),
```
An i.i.d. sum raises `r̂` to a power, so `P(S_n = x) ≤ N⁻² ∑_ξ ‖r̂(ξ)‖ⁿ`.

* `pairChar ξ y = e((ξ₁y₁ + ξ₂y₂)/N)`: the standard character of the product.
* `sum_pairChar`: two-dimensional orthogonality.
* `charFn r ξ`: the characteristic function `r̂(ξ)`.
* `charFn_inversion`, `apply_toReal_le_sum_norm_charFn`: inversion and the triangle inequality.
* `charFn_iidSum`: `charFn (iidSum r n) = charFn r ^ n`.
* `iidSum_apply_toReal_le`: the combined circle-method bound.
* `charFn_normSq_pair_bound`, `sum_exp_neg_nd_sq_le`, etc.: ingredients for the decay of the characteristic
  function and for bounding Gaussian-type sums.
-/

open scoped ENNReal

namespace GGMCollatz

variable {N : ℕ} [NeZero N]

/-- 1-D orthogonality: the geometric sum of the standard character `e(t·/N)`.
@isnad1 id=eq.0h2v.s7.3b297adb87bc from=translated src=- shape=1d570b0e vocab=43545723
-/
theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ i : ZMod N, ZMod.stdAddChar (t * i) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · simp only [← AddChar.mulShift_apply (ψ := ZMod.stdAddChar) (r := t)]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- The product standard character on `ZMod N × ZMod N`: `e((ξ₁y₁ + ξ₂y₂)/N)`.-/
noncomputable def pairChar (ξ y : ZMod N × ZMod N) : ℂ :=
  ZMod.stdAddChar (ξ.1 * y.1 + ξ.2 * y.2)

/--
@isnad1 id=eq.0h3v.s5.b9227a0fc069 from=translated src=- shape=376f560d vocab=3cd73a4d
-/
theorem pairChar_norm (ξ y : ZMod N × ZMod N) : ‖pairChar ξ y‖ = 1 := by
  rw [pairChar, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/--
@isnad1 id=eq.0h2v.s6.504d81bed791 from=translated src=- shape=67940b2a vocab=cee260e1
-/
theorem pairChar_zero_right (ξ : ZMod N × ZMod N) : pairChar ξ 0 = 1 := by
  rw [pairChar]
  simp

/--
@isnad1 id=eq.0h4v.s6.3b8f0c8d2b2c from=translated src=- shape=59dbef9a vocab=f5783a73
-/
theorem pairChar_add_right (ξ y z : ZMod N × ZMod N) :
    pairChar ξ (y + z) = pairChar ξ y * pairChar ξ z := by
  rw [pairChar, pairChar, pairChar, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- 2-D orthogonality: `∑_ξ e(ξ·z/N) = N²` at `z = 0` and `0` elsewhere.
@isnad1 id=eq.0h2v.s7.03f6ca440c3a from=translated src=- shape=a048c6ea vocab=34aea940
-/
theorem sum_pairChar (z : ZMod N × ZMod N) :
    ∑ ξ : ZMod N × ZMod N, pairChar ξ z = if z = 0 then ((N : ℂ) ^ 2) else 0 := by
  have hsplit : ∑ ξ : ZMod N × ZMod N, pairChar ξ z
      = (∑ t : ZMod N, ZMod.stdAddChar (z.1 * t))
      * (∑ t : ZMod N, ZMod.stdAddChar (z.2 * t)) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ξ₁ _ => Finset.sum_congr rfl fun ξ₂ _ => ?_
    rw [pairChar, AddChar.map_add_eq_mul, mul_comm ξ₁ z.1, mul_comm ξ₂ z.2]
  rw [hsplit, sum_stdAddChar_mul, sum_stdAddChar_mul]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [sq]
  · rw [ite_eq_right hz]
    have : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (Prod.ext h.1 h.2)
    rcases this with h1 | h2
    · rw [ite_eq_right h1, zero_mul]
    · rw [ite_eq_right h2, mul_zero]

/-- The characteristic function `r̂(ξ)` of a PMF on the pair group (finite sum).-/
noncomputable def charFn (r : PMF (ZMod N × ZMod N)) (ξ : ZMod N × ZMod N) : ℂ :=
  ∑ y, ((r y).toReal : ℂ) * pairChar ξ y

/-- Bind mass on a finite type, in real form.
@isnad1 id=eq.0h5v.s6.9d6b61992455 from=translated src=- shape=6881cdf3 vocab=9e298f6d
-/
theorem toReal_bind_apply {α β : Type*} [Fintype α] (p : PMF α) (f : α → PMF β)
    (y : β) : ((p.bind f) y).toReal = ∑ a, (p a).toReal * ((f a) y).toReal := by
  rw [PMF.bind_apply, tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha),
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a) ((f a).apply_ne_top y))]
  exact Finset.sum_congr rfl fun a _ => ENNReal.toReal_mul

/-- Pushforward change of variables for finite complex-weighted sums.
@isnad1 id=eq.0h5v.s6.2be6a691d41f from=translated src=- shape=41a530dc vocab=fd2e39bd
-/
theorem sum_map_mul_complex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (q : PMF α) (φ : α → β) (g : β → ℂ) :
    ∑ y, (((q.map φ) y).toReal : ℂ) * g y = ∑ z, ((q z).toReal : ℂ) * g (φ z) := by
  classical
  have h1 : ∀ y, (((q.map φ) y).toReal : ℂ)
      = ∑ z, if y = φ z then ((q z).toReal : ℂ) else 0 := by
    intro y
    rw [PMF.map_apply, tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha),
      ENNReal.toReal_sum (fun a _ => by
        split_ifs with h
        · exact q.apply_ne_top a
        · exact ENNReal.zero_ne_top)]
    push_cast
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> simp
  calc ∑ y, (((q.map φ) y).toReal : ℂ) * g y
      = ∑ y, ∑ z, (if y = φ z then ((q z).toReal : ℂ) else 0) * g y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [h1, Finset.sum_mul]
    _ = ∑ z, ∑ y, (if y = φ z then ((q z).toReal : ℂ) else 0) * g y :=
        Finset.sum_comm
    _ = ∑ z, ((q z).toReal : ℂ) * g (φ z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_eq_single (φ z)
          (fun y _ hy => by rw [ite_eq_right hy, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h)]
        rw [ite_eq_left rfl]

/-- Fourier inversion for PMFs on the pair group (paper pp.15–16, finite form).
@isnad1 id=eq.0h3v.s7.7861f6822bdf from=translated src=- shape=e6035f60 vocab=51c166e3
-/
theorem charFn_inversion (r : PMF (ZMod N × ZMod N)) (x : ZMod N × ZMod N) :
    ((r x).toReal : ℂ)
      = ((N : ℂ) ^ 2)⁻¹ * ∑ ξ, charFn r ξ * pairChar ξ (-x) := by
  have hkey : ∑ ξ, charFn r ξ * pairChar ξ (-x)
      = ((r x).toReal : ℂ) * (N : ℂ) ^ 2 := by
    calc ∑ ξ, charFn r ξ * pairChar ξ (-x)
        = ∑ ξ, ∑ y, ((r y).toReal : ℂ) * pairChar ξ (y + -x) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [charFn, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [pairChar_add_right, mul_assoc]
      _ = ∑ y, ((r y).toReal : ℂ) * ∑ ξ, pairChar ξ (y + -x) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ y, ((r y).toReal : ℂ) * (if y + -x = 0 then ((N : ℂ) ^ 2) else 0) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [sum_pairChar]
      _ = ((r x).toReal : ℂ) * (N : ℂ) ^ 2 := by
          rw [Finset.sum_eq_single x
            (fun y _ hy => by
              rw [ite_eq_right (fun h => hy (by rwa [add_neg_eq_zero] at h)), mul_zero])
            (fun h => absurd (Finset.mem_univ _) h)]
          rw [ite_eq_left (by rw [add_neg_cancel])]
  have hN : ((N : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne N))
  rw [hkey, mul_comm (((N : ℂ) ^ 2)⁻¹), mul_assoc, mul_inv_cancel₀ hN, mul_one]

/-- Triangle-inequality form of the inversion: the point mass is at most the
normalized `ℓ¹` mass of the characteristic function.
@isnad1 id=le.0h3v.s6.2a67b82ebbf1 from=translated src=- shape=50c692d8 vocab=a53ade43
-/
theorem apply_toReal_le_sum_norm_charFn (r : PMF (ZMod N × ZMod N))
    (x : ZMod N × ZMod N) :
    (r x).toReal ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ, ‖charFn r ξ‖ := by
  have h0 : (r x).toReal = ‖((r x).toReal : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [h0, charFn_inversion r x]
  calc ‖((N : ℂ) ^ 2)⁻¹ * ∑ ξ, charFn r ξ * pairChar ξ (-x)‖
      = ((N : ℝ) ^ 2)⁻¹ * ‖∑ ξ, charFn r ξ * pairChar ξ (-x)‖ := by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    _ ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ, ‖charFn r ξ‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ξ _ => ?_)
        rw [norm_mul, pairChar_norm, mul_one]

/--
@isnad1 id=eq.0h2v.s6.fc9352d3b403 from=translated src=- shape=e2400a14 vocab=900a81f6
-/
theorem charFn_pure_zero (ξ : ZMod N × ZMod N) :
    charFn (PMF.pure 0) ξ = 1 := by
  rw [charFn, Finset.sum_eq_single (0 : ZMod N × ZMod N)
    (fun y _ hy => by
      rw [show ((PMF.pure (0 : ZMod N × ZMod N)) y) = 0 from by
        rw [PMF.pure_apply, ite_eq_right hy], ENNReal.toReal_zero, Complex.ofReal_zero,
        zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [PMF.pure_apply, ite_eq_left rfl, ENNReal.toReal_one, Complex.ofReal_one, one_mul,
    pairChar_zero_right]

/-- `charFn` of a translated PMF picks up the character of the shift.
@isnad1 id=eq.0h4v.s6.ee0604e53ce1 from=translated src=- shape=87168360 vocab=40d7c564
-/
theorem charFn_map_add (q : PMF (ZMod N × ZMod N)) (a ξ : ZMod N × ZMod N) :
    charFn (q.map (a + ·)) ξ = pairChar ξ a * charFn q ξ := by
  rw [charFn, sum_map_mul_complex q (a + ·) (pairChar ξ), charFn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [pairChar_add_right]
  ring

/-- `charFn` of a bind averages the component characteristic functions.
@isnad1 id=eq.0h4v.s7.6b29ff47be43 from=translated src=- shape=c9584c76 vocab=1e05fb45
-/
theorem charFn_bind (p : PMF (ZMod N × ZMod N)) (f : ZMod N × ZMod N → PMF (ZMod N × ZMod N))
    (ξ : ZMod N × ZMod N) :
    charFn (p.bind f) ξ = ∑ a, ((p a).toReal : ℂ) * charFn (f a) ξ := by
  rw [charFn]
  calc ∑ y, (((p.bind f) y).toReal : ℂ) * pairChar ξ y
      = ∑ y, ∑ a, ((p a).toReal : ℂ) * (((f a) y).toReal : ℂ) * pairChar ξ y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [toReal_bind_apply]
        push_cast
        rw [Finset.sum_mul]
    _ = ∑ a, ∑ y, ((p a).toReal : ℂ) * (((f a) y).toReal : ℂ) * pairChar ξ y :=
        Finset.sum_comm
    _ = ∑ a, ((p a).toReal : ℂ) * charFn (f a) ξ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [charFn, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring

/-- **Characteristic functions of iid sums are powers** (the circle-method engine).
@isnad1 id=eq.0h4v.s6.865622f65765 from=translated src=- shape=907b8f92 vocab=152d6480
-/
theorem charFn_iidSum (r : PMF (ZMod N × ZMod N)) (n : ℕ) (ξ : ZMod N × ZMod N) :
    charFn (iidSum r n) ξ = (charFn r ξ) ^ n := by
  induction n with
  | zero => rw [iidSum_zero, pow_zero, charFn_pure_zero]
  | succ n IH =>
    rw [iidSum_succ, charFn_bind, pow_succ]
    calc ∑ a, ((r a).toReal : ℂ) * charFn ((iidSum r n).map (a + ·)) ξ
        = ∑ a, ((r a).toReal : ℂ) * pairChar ξ a * (charFn r ξ) ^ n := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [charFn_map_add, IH]
          ring
      _ = (∑ a, ((r a).toReal : ℂ) * pairChar ξ a) * (charFn r ξ) ^ n := by
          rw [Finset.sum_mul]
      _ = (charFn r ξ) ^ n * charFn r ξ := by
          rw [← charFn]
          ring

/-- **The composite circle-method bound**: for any PMF on `ZMod N × ZMod N`, the
`n`-fold iid sum has point masses `≤ N⁻² ∑_ξ ‖r̂(ξ)‖ⁿ`.
@isnad1 id=le.0h4v.s7.237e40e63cd8 from=translated src=- shape=3e84ef8e vocab=1d694a03
-/
theorem iidSum_apply_toReal_le (r : PMF (ZMod N × ZMod N)) (n : ℕ)
    (x : ZMod N × ZMod N) :
    ((iidSum r n) x).toReal ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ, ‖charFn r ξ‖ ^ n := by
  refine le_trans (apply_toReal_le_sum_norm_charFn (iidSum r n) x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_)
  rw [charFn_iidSum, norm_pow]

/-- Conjugating the product character negates its argument.
@isnad1 id=eq.0h3v.s6.4f4becf8124c from=translated src=- shape=b8bffff3 vocab=37c18dbe
-/
theorem pairChar_conj (ξ y : ZMod N × ZMod N) :
    (starRingEnd ℂ) (pairChar ξ y) = pairChar ξ (-y) := by
  have hneg : pairChar ξ (-y) = (pairChar ξ y)⁻¹ := by
    rw [pairChar, pairChar, show ξ.1 * (-y).1 + ξ.2 * (-y).2
        = -(ξ.1 * y.1 + ξ.2 * y.2) from by
      simp only [Prod.fst_neg, Prod.snd_neg]
      ring, AddChar.map_neg_eq_inv]
  rw [hneg, Complex.inv_eq_conj (pairChar_norm ξ y)]

/-- Character product with a conjugate is the character of the difference.
@isnad1 id=eq.0h4v.s7.32e1b011538e from=translated src=- shape=9780bba7 vocab=37d8fa38
-/
theorem pairChar_mul_conj (ξ y y' : ZMod N × ZMod N) :
    pairChar ξ y * (starRingEnd ℂ) (pairChar ξ y') = pairChar ξ (y - y') := by
  rw [pairChar_conj, ← pairChar_add_right, sub_eq_add_neg]

/-- PMF masses on a finite type sum to one (real form).
@isnad1 id=eq.0h2v.s5.860e80102d13 from=translated src=- shape=821dc207 vocab=947d49fd
-/
theorem sum_toReal_eq_one {α : Type*} [Fintype α] (r : PMF α) :
    ∑ y, (r y).toReal = 1 := by
  have h := r.tsum_coe
  rw [tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha)] at h
  rw [← ENNReal.toReal_sum (fun a _ => r.apply_ne_top a), h, ENNReal.toReal_one]

/-- **The two-atom anti-concentration bound** (heart of the paper's `|M(it)| < 1`
nondegeneracy step, p.16): any two distinct atoms of `r` whose relative character is
bounded away from `1` pull `‖r̂(ξ)‖` off the unit circle, quantitatively.
@isnad1 id=le.1h5v.s7.f75b767d8eca from=translated src=- shape=d0be87a7 vocab=179a0531
-/
theorem charFn_normSq_pair_bound (r : PMF (ZMod N × ZMod N))
    (ξ y₀ y₁ : ZMod N × ZMod N) (h01 : y₀ ≠ y₁) :
    2 * (r y₀).toReal * (r y₁).toReal * (1 - (pairChar ξ (y₀ - y₁)).re)
      ≤ 1 - ‖charFn r ξ‖ ^ 2 := by
  classical
  set m : ZMod N × ZMod N → ℝ := fun y => (r y).toReal with hm
  set F : ZMod N × ZMod N → ZMod N × ZMod N → ℝ :=
    fun y y' => m y * m y' * (1 - (pairChar ξ (y - y')).re) with hF
  -- expansion of the squared norm as a double character sum
  have hexp : ‖charFn r ξ‖ ^ 2
      = ∑ y, ∑ y', m y * m y' * (pairChar ξ (y - y')).re := by
    have h0 : ‖charFn r ξ‖ ^ 2 = (charFn r ξ * (starRingEnd ℂ) (charFn r ξ)).re := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h0, charFn, map_sum, Finset.sum_mul_sum]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    have hterm : ((m y : ℂ) * pairChar ξ y) * ((m y' : ℂ) * (starRingEnd ℂ) (pairChar ξ y'))
        = ((m y * m y' : ℝ) : ℂ) * pairChar ξ (y - y') := by
      rw [← pairChar_mul_conj]
      push_cast
      ring
    rw [hterm, Complex.re_ofReal_mul, mul_assoc]
  -- the double sum of the complementary weights
  have hone : (1 : ℝ) = ∑ y, ∑ y', m y * m y' := by
    calc (1 : ℝ) = (∑ y, m y) * (∑ y', m y') := by
          rw [sum_toReal_eq_one, one_mul]
      _ = ∑ y, ∑ y', m y * m y' := Finset.sum_mul_sum _ _ _ _
  have hsub : 1 - ‖charFn r ξ‖ ^ 2 = ∑ y, ∑ y', F y y' := by
    rw [hexp]
    calc (1 : ℝ) - ∑ y, ∑ y', m y * m y' * (pairChar ξ (y - y')).re
        = (∑ y, ∑ y', m y * m y') - ∑ y, ∑ y', m y * m y' * (pairChar ξ (y - y')).re := by
          rw [← hone]
      _ = ∑ y, ((∑ y', m y * m y') - ∑ y', m y * m y' * (pairChar ξ (y - y')).re) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ y, ∑ y', F y y' := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [hF]
          ring
  -- every term of the double sum is nonnegative
  have hterm_nonneg : ∀ y y', 0 ≤ F y y' := by
    intro y y'
    refine mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_
    rw [sub_nonneg]
    calc (pairChar ξ (y - y')).re ≤ |(pairChar ξ (y - y')).re| := le_abs_self _
      _ ≤ ‖pairChar ξ (y - y')‖ := Complex.abs_re_le_norm _
      _ = 1 := pairChar_norm _ _
  -- single out the (y₀,y₁) and (y₁,y₀) terms
  have hsym : F y₁ y₀ = F y₀ y₁ := by
    simp only [hF]
    have hre : (pairChar ξ (y₁ - y₀)).re = (pairChar ξ (y₀ - y₁)).re := by
      rw [show y₁ - y₀ = -(y₀ - y₁) from by ring, ← pairChar_conj, Complex.conj_re]
    rw [hre]
    ring
  have hrow : ∀ y, 0 ≤ ∑ y', F y y' :=
    fun y => Finset.sum_nonneg fun y' _ => hterm_nonneg y y'
  have h1 : F y₀ y₁ ≤ ∑ y', F y₀ y' :=
    Finset.single_le_sum (fun y' _ => hterm_nonneg y₀ y') (Finset.mem_univ y₁)
  have h2 : F y₁ y₀ ≤ ∑ y', F y₁ y' :=
    Finset.single_le_sum (fun y' _ => hterm_nonneg y₁ y') (Finset.mem_univ y₀)
  have h3 : (∑ y', F y₀ y') + (∑ y', F y₁ y') ≤ ∑ y, ∑ y', F y y' := by
    have hp := Finset.sum_pair (f := fun y => ∑ y', F y y') h01
    rw [← hp]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hrow y)
  have hfinal : F y₀ y₁ + F y₁ y₀ ≤ ∑ y, ∑ y', F y y' := by
    calc F y₀ y₁ + F y₁ y₀ ≤ (∑ y', F y₀ y') + (∑ y', F y₁ y') := add_le_add h1 h2
      _ ≤ _ := h3
  rw [hsub]
  calc 2 * m y₀ * m y₁ * (1 - (pairChar ξ (y₀ - y₁)).re)
      = F y₀ y₁ + F y₁ y₀ := by rw [hsym, hF]; ring
    _ ≤ ∑ y, ∑ y', F y y' := hfinal

/-- **Jordan-type lower bound for the character defect**: `1 - Re e(j/N)` is at
least `8·dist(j/N, ℤ)²` (where `dist(j/N, ℤ) = min(val, N - val)/N`).
@isnad1 id=le.0h2v.s7.4881a9cc4ba0 from=translated src=- shape=4af3e2ef vocab=e8c998dc
-/
theorem one_sub_re_stdAddChar_ge (j : ZMod N) :
    8 * ((min (j.val : ℝ) ((N : ℝ) - j.val)) / N) ^ 2
      ≤ 1 - (ZMod.stdAddChar j).re := by
  have hN : (0 : ℝ) < N := by
    have := NeZero.ne N
    positivity
  set v : ℝ := (j.val : ℝ) with hv
  have hv0 : 0 ≤ v := Nat.cast_nonneg _
  have hvN : v < N := by
    rw [hv]
    have := ZMod.val_lt j
    exact_mod_cast this
  -- the real part is a cosine
  have hre : (ZMod.stdAddChar j).re = Real.cos (2 * Real.pi * v / N) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    have harg : 2 * Real.pi * Complex.I * (j.val : ℂ) / N
        = ((2 * Real.pi * v / N : ℝ) : ℂ) * Complex.I := by
      rw [hv]
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  set t : ℝ := v / N with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hN]
    exact hvN
  have hmin : min v (N - v) / N = min t (1 - t) := by
    rw [ht, ← min_div_div_right hN.le, sub_div, div_self hN.ne']
  rw [hmin]
  -- 1 - cos(2πt) = 2 sin²(πt)
  have hangle : 2 * Real.pi * v / N = 2 * (Real.pi * t) := by
    rw [ht]
    ring
  rw [hangle]
  have hcos : Real.cos (2 * (Real.pi * t)) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    have h1 := Real.cos_two_mul (Real.pi * t)
    have h2 := Real.sin_sq_add_cos_sq (Real.pi * t)
    nlinarith
  rw [hcos]
  -- Jordan: sin(πt) ≥ 2·min(t, 1-t) on [0,1]
  have hsin : 2 * min t (1 - t) ≤ Real.sin (Real.pi * t) := by
    rcases le_or_gt t 2⁻¹ with hhalf | hhalf
    · rw [min_eq_left (by linarith)]
      have h := Real.mul_le_sin (x := Real.pi * t)
        (by positivity) (by nlinarith [Real.pi_pos])
      calc 2 * t = 2 / Real.pi * (Real.pi * t) := by
            field_simp
        _ ≤ Real.sin (Real.pi * t) := h
    · rw [min_eq_right (by linarith)]
      have hs : Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
        rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t from by ring,
          Real.sin_pi_sub]
      rw [hs]
      have h := Real.mul_le_sin (x := Real.pi * (1 - t))
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      calc 2 * (1 - t) = 2 / Real.pi * (Real.pi * (1 - t)) := by
            field_simp
        _ ≤ Real.sin (Real.pi * (1 - t)) := h
  have hmin0 : 0 ≤ min t (1 - t) := le_min ht0 (by linarith)
  nlinarith [hsin, hmin0, sq_nonneg (Real.sin (Real.pi * t) - 2 * min t (1 - t))]

/-! ### The cyclic distance `nd` and its subadditivity -/

/-- Distance of `j` to `0` on the cycle `ZMod N`: `min(val, N - val)`.-/
def nd (j : ZMod N) : ℕ := min j.val (N - j.val)

/-- Any integer representative bounds the cyclic distance.
@isnad1 id=le.0h2v.s5.53c771ebcfd3 from=translated src=- shape=295049b8 vocab=2bcc3da3
-/
theorem nd_le_natAbs (x : ℤ) : nd ((x : ZMod N)) ≤ x.natAbs := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNI : (0 : ℤ) < N := by exact_mod_cast hN
  have hval : (((x : ZMod N)).val : ℤ) = x % N := ZMod.val_intCast x
  have h0 : 0 ≤ x % N := Int.emod_nonneg x hNz
  have hlt : x % N < N := Int.emod_lt_of_pos x hNI
  have hq := Int.mul_ediv_add_emod x N
  rcases le_or_gt 0 x with hx | hx
  · have hqnn : 0 ≤ x / N := Int.ediv_nonneg hx hNI.le
    have hNq : 0 ≤ (N : ℤ) * (x / N) := mul_nonneg hNI.le hqnn
    rw [nd]
    generalize (N : ℤ) * (x / N) = t at hq hNq
    generalize x % N = r at hval h0 hlt hq
    omega
  · have hqle : x / N ≤ -1 := by
      by_contra hcon
      push Not at hcon
      have hge : 0 ≤ x / N := by omega
      have hprod : 0 ≤ (N : ℤ) * (x / N) := mul_nonneg hNI.le hge
      linarith [hq, h0]
    have hNq : (N : ℤ) * (x / N) ≤ (N : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left hqle hNI.le
    rw [nd]
    generalize (N : ℤ) * (x / N) = t at hq hNq
    generalize x % N = r at hval h0 hlt hq
    omega

/-- The cyclic distance is attained by a representative.
@isnad1 id=ex.0h2v.s5.c9dd703a126d from=translated src=- shape=368238a1 vocab=b402c709
-/
theorem exists_natAbs_eq_nd (j : ZMod N) :
    ∃ x : ℤ, (x : ZMod N) = j ∧ x.natAbs = nd j := by
  have hvlt : j.val < N := ZMod.val_lt j
  rcases le_or_gt (j.val) (N - j.val) with h | h
  · refine ⟨(j.val : ℤ), ?_, ?_⟩
    · rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    · rw [nd, min_eq_left h, Int.natAbs_natCast]
  · refine ⟨(j.val : ℤ) - N, ?_, ?_⟩
    · rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
        ZMod.natCast_self, sub_zero]
    · rw [nd, min_eq_right h.le]
      omega

/-- Subadditivity of the cyclic distance over differences.
@isnad1 id=le.0h3v.s5.4aeb6ea20d4a from=translated src=- shape=95656b1d vocab=594cefdd
-/
theorem nd_sub_le (a b : ZMod N) : nd (a - b) ≤ nd a + nd b := by
  obtain ⟨x, hxa, hxn⟩ := exists_natAbs_eq_nd a
  obtain ⟨y, hyb, hyn⟩ := exists_natAbs_eq_nd b
  have hab : a - b = ((x - y : ℤ) : ZMod N) := by
    rw [Int.cast_sub, hxa, hyb]
  calc nd (a - b) = nd ((x - y : ℤ) : ZMod N) := by rw [hab]
    _ ≤ (x - y).natAbs := nd_le_natAbs _
    _ ≤ x.natAbs + y.natAbs := Int.natAbs_sub_le x y
    _ = nd a + nd b := by rw [hxn, hyn]

/-- Real form of `nd` matching the Jordan bound's distance expression.
@isnad1 id=eq.0h2v.s5.dc02beb8e055 from=translated src=- shape=d068bdaf vocab=fc2277e2
-/
theorem nd_cast (j : ZMod N) :
    ((nd j : ℕ) : ℝ) = min (j.val : ℝ) ((N : ℝ) - j.val) := by
  have hvlt : j.val ≤ N := (ZMod.val_lt j).le
  rw [nd]
  rcases le_or_gt (j.val) (N - j.val) with h | h
  · rw [min_eq_left h, min_eq_left (by
      rw [← Nat.cast_sub hvlt]
      exact_mod_cast h)]
  · rw [min_eq_right h.le, min_eq_right (by
      rw [← Nat.cast_sub hvlt]
      exact_mod_cast h.le), ← Nat.cast_sub hvlt]

/-- Jordan bound in `nd` form.
@isnad1 id=le.0h2v.s7.7e0f716dd392 from=translated src=- shape=3e305b48 vocab=d327fa3f
-/
theorem one_sub_re_stdAddChar_ge' (j : ZMod N) :
    8 * ((nd j : ℝ) / N) ^ 2 ≤ 1 - (ZMod.stdAddChar j).re := by
  have h := one_sub_re_stdAddChar_ge j
  rwa [← nd_cast] at h

/-! ### Gaussian summation over `ZMod N` (node S3, step (E)) -/

/-- Powers of a sub-unit modulus with quadratic defect decay exponentially:
`x² ≤ 1 - D` gives `xⁿ ≤ exp(-n·D/4)` for `n ≥ 2` (the lost factor `4` absorbs
both the `n/2` halving and the odd-`n` floor).
@isnad1 id=le.4h3v.s6.15d84bfdbd0d from=translated src=- shape=6b498793 vocab=3f5554db
-/
theorem pow_le_exp_of_sq_le_one_sub {x D : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hx : 0 ≤ x) (hD : 0 ≤ D) (h : x ^ 2 ≤ 1 - D) :
    x ^ n ≤ Real.exp (-(n : ℝ) * D / 4) := by
  have h1D : 0 ≤ 1 - D := le_trans (sq_nonneg x) h
  have hx1 : x ≤ 1 := by nlinarith
  set m := n / 2 with hm
  have h4m : (n : ℝ) ≤ 4 * m := by
    have : n ≤ 4 * m := by omega
    exact_mod_cast this
  have hexp1 : 1 - D ≤ Real.exp (-D) := by
    have := Real.add_one_le_exp (-D)
    linarith
  calc x ^ n ≤ x ^ (2 * m) := pow_le_pow_of_le_one hx hx1 (by omega)
    _ = (x ^ 2) ^ m := by rw [← pow_mul]
    _ ≤ (1 - D) ^ m := pow_le_pow_left₀ (sq_nonneg x) h m
    _ ≤ Real.exp (-D) ^ m := pow_le_pow_left₀ h1D hexp1 m
    _ = Real.exp ((m : ℝ) * -D) := (Real.exp_nat_mul _ m).symm
    _ ≤ Real.exp (-(n : ℝ) * D / 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hD (by linarith : (0 : ℝ) ≤ 4 * (m : ℝ) - n)]

/-- Finite geometric sums with ratio `exp(-a)` are bounded by `(1 - exp(-a))⁻¹`.
@isnad1 id=le.1h2v.s5.7ec1c2c65c8f from=translated src=- shape=2d1211b5 vocab=26877948
-/
theorem sum_exp_neg_mul_le {a : ℝ} (ha : 0 < a) (M : ℕ) :
    ∑ m ∈ Finset.range M, Real.exp (-(a * m)) ≤ (1 - Real.exp (-a))⁻¹ := by
  set q := Real.exp (-a) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 < q := Real.exp_pos _
  have h1q : 0 < 1 - q := by linarith
  have hterm : ∀ m : ℕ, Real.exp (-(a * m)) = q ^ m := fun m => by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    ring
  calc ∑ m ∈ Finset.range M, Real.exp (-(a * m))
      = ∑ m ∈ Finset.range M, q ^ m := Finset.sum_congr rfl fun m _ => hterm m
    _ = (q ^ M - 1) / (q - 1) := geom_sum_eq hq1.ne M
    _ = (1 - q ^ M) / (1 - q) := by
        rw [show (1 : ℝ) - q ^ M = -(q ^ M - 1) from by ring,
          show (1 : ℝ) - q = -(q - 1) from by ring, neg_div_neg_eq]
    _ ≤ 1 / (1 - q) := by
        have hpow : 0 ≤ q ^ M := pow_nonneg hq0.le M
        gcongr
        linarith
    _ = (1 - q)⁻¹ := one_div _

/-- Reindexing along `val`: sums over `ZMod N` are sums over `range N`.
@isnad1 id=eq.0h2v.s5.b2a5819c3355 from=translated src=- shape=de32b0c5 vocab=030d8e2e
-/
theorem sum_zmod_eq_sum_range (f : ℕ → ℝ) :
    ∑ t : ZMod N, f t.val = ∑ m ∈ Finset.range N, f m :=
  Finset.sum_nbij' (fun t => t.val) (fun m => (m : ZMod N))
    (fun t _ => Finset.mem_range.mpr (ZMod.val_lt t))
    (fun _ _ => Finset.mem_univ _)
    (fun t _ => ZMod.natCast_rightInverse t)
    (fun _ => (ZMod.val_cast_of_lt <| Finset.mem_range.mp ·))
    (fun _ _ => rfl)

/-- **1-D Gaussian summation on `ZMod N`** ((E) of node S3): the exponential sum of
quadratic cyclic-distance decay is at most twice the geometric constant, uniformly
in `N`. Route: `nd² ≥ nd`, `exp(-a·min) ≤ exp(-a·val) + exp(-a·(N-val))`, reindex
both halves along `val` (the second reflected), geometric domination.
@isnad1 id=le.1h2v.s6.4e1e818bb8d2 from=translated src=- shape=7ba8e609 vocab=aece822a
-/
theorem sum_exp_neg_nd_sq_le {a : ℝ} (ha : 0 < a) :
    ∑ t : ZMod N, Real.exp (-(a * ((nd t : ℝ)) ^ 2))
      ≤ 2 * (1 - Real.exp (-a))⁻¹ := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- quadratic decay dominates linear decay on ℕ
  have hstep1 : ∀ t : ZMod N,
      Real.exp (-(a * ((nd t : ℝ)) ^ 2)) ≤ Real.exp (-(a * (nd t : ℝ))) := by
    intro t
    apply Real.exp_le_exp.mpr
    have hself : (nd t : ℝ) ≤ ((nd t : ℝ)) ^ 2 := by
      have h := Nat.le_self_pow (two_ne_zero) (nd t)
      exact_mod_cast h
    nlinarith
  -- linear cyclic decay splits into the two val-monotone halves
  have hstep2 : ∀ t : ZMod N,
      Real.exp (-(a * (nd t : ℝ)))
        ≤ Real.exp (-(a * (t.val : ℝ))) + Real.exp (-(a * ((N - t.val : ℕ) : ℝ))) := by
    intro t
    rcases min_cases (t.val) (N - t.val) with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [nd, hmin]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [nd, hmin]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc ∑ t : ZMod N, Real.exp (-(a * ((nd t : ℝ)) ^ 2))
      ≤ ∑ t : ZMod N, (Real.exp (-(a * (t.val : ℝ)))
          + Real.exp (-(a * ((N - t.val : ℕ) : ℝ)))) :=
        Finset.sum_le_sum fun t _ => le_trans (hstep1 t) (hstep2 t)
    _ = (∑ t : ZMod N, Real.exp (-(a * (t.val : ℝ))))
          + ∑ t : ZMod N, Real.exp (-(a * ((N - t.val : ℕ) : ℝ))) :=
        Finset.sum_add_distrib
    _ ≤ (1 - Real.exp (-a))⁻¹ + (1 - Real.exp (-a))⁻¹ := by
        refine add_le_add ?_ ?_
        · rw [sum_zmod_eq_sum_range (fun m => Real.exp (-(a * (m : ℝ))))]
          exact sum_exp_neg_mul_le ha N
        · rw [sum_zmod_eq_sum_range (fun m => Real.exp (-(a * ((N - m : ℕ) : ℝ))))]
          rw [← Finset.sum_range_reflect (fun m => Real.exp (-(a * ((N - m : ℕ) : ℝ)))) N]
          refine le_trans (Finset.sum_le_sum fun j hj => ?_) (sum_exp_neg_mul_le ha N)
          have hjN : j < N := Finset.mem_range.mp hj
          have hidx : (N - (N - 1 - j) : ℕ) = j + 1 := by omega
          rw [hidx]
          apply Real.exp_le_exp.mpr
          have : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
            push_cast
            linarith
          nlinarith
    _ = 2 * (1 - Real.exp (-a))⁻¹ := by ring

/-- Elementary bound `(1 - exp(-a))⁻¹ ≤ 2/a` on `(0, 1]` (via `exp(-a) ≤ (1+a)⁻¹`).
@isnad1 id=le.2h1v.s6.11c2d8a6dd80 from=translated src=- shape=141414d5 vocab=e5d57273
-/
theorem one_sub_exp_neg_inv_le {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1) :
    (1 - Real.exp (-a))⁻¹ ≤ 2 / a := by
  have hea : Real.exp (-a) ≤ (1 + a)⁻¹ := by
    rw [Real.exp_neg]
    have hle : 1 + a ≤ Real.exp a := by
      have := Real.add_one_le_exp a
      linarith
    gcongr
  have hkey : a / 2 ≤ 1 - Real.exp (-a) := by
    have hinv : (1 + a)⁻¹ ≤ 1 - a / 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      nlinarith
    linarith
  calc (1 - Real.exp (-a))⁻¹ ≤ (a / 2)⁻¹ := by
        gcongr
    _ = 2 / a := by rw [inv_div]

end GGMCollatz
