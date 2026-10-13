/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Asymptotic notation for natural number functions

This module defines `Complexity.BigO` and `Complexity.LittleO`, thin adapters
that lift Mathlib's `Asymptotics.IsBigO` and `Asymptotics.IsLittleO` to
`ℕ → ℕ` functions (casting through `ℝ`).

The scoped notations `f =O g` and `f =o g` are available when `Complexity` is
opened and read like standard complexity-theoretic asymptotic notation.

## Main definitions

- `BigO` — `f =O g` means `f(n) = O(g(n))` as `n → ∞`
- `LittleO` — `f =o g` means `f(n) = o(g(n))` as `n → ∞`

## Main results

### BigO
- `BigO.refl` — reflexivity
- `BigO.trans` — transitivity
- `BigO.of_le` — pointwise `≤` implies big-O
- `BigO.add` — sum of big-O is big-O
- `BigO.pow` — fixed powers preserve big-O
- `BigO.const_mul_left` — constant multiple preserves big-O
- `BigO.natSize_of_pow` — binary widths of power-bounded values are logarithmic
- `BigO.le_add_left` / `BigO.le_add_right` — projections from a sum
- `BigO.const_mul_add` — `c * f₁ + f₂ = O(T₁ + T₂)`
- `polynomial_eval_mono_nat` — natural polynomial evaluation is monotone

### LittleO
- `LittleO.isBigO` — little-o implies big-O
- `LittleO.trans` — transitivity
- `LittleO.trans_bigO` — mixed: `o` then `O` gives `o`
- `BigO.trans_littleO` — mixed: `O` then `o` gives `o`
- `LittleO.add` — sum of little-o is little-o
- `LittleO.const_mul_left` — constant multiple preserves little-o
-/

@[expose] public section

open Asymptotics Filter

namespace Complexity

-- ════════════════════════════════════════════════════════════════════════
-- Definitions
-- ════════════════════════════════════════════════════════════════════════

/-- `f` grows at most as fast as `g` asymptotically: `f(n) = O(g(n))` as `n → ∞`.
    Lifts Mathlib's `Asymptotics.IsBigO` to `ℕ → ℕ` functions, avoiding
    repeated `Nat.cast` coercions in complexity class definitions.

    Unfolding: `f =O g ↔ ∃ C, ∀ᶠ n in atTop, ↑(f n) ≤ C * ↑(g n)`. -/
def BigO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ))

@[inherit_doc BigO]
scoped infixl:50 " =O " => BigO

/-- `f` grows strictly slower than `g` asymptotically: `f(n) = o(g(n))` as `n → ∞`.
    Lifts Mathlib's `Asymptotics.IsLittleO` to `ℕ → ℕ` functions.

    Unfolding: `f =o g ↔ ∀ ε > 0, ∀ᶠ n in atTop, ↑(f n) ≤ ε * ↑(g n)`. -/
def LittleO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =o[atTop] (fun n => (g n : ℝ))

@[inherit_doc LittleO]
scoped infixl:50 " =o " => LittleO

-- ════════════════════════════════════════════════════════════════════════
-- BigO core lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Big-O is reflexive: `f = O(f)`.
@isnad1 id=bigo.0h1v.s2.961406a93ab1 from=translated src=- shape=bf503969 vocab=d76903b9
-/
theorem BigO.refl (f : ℕ → ℕ) : f =O f :=
  isBigO_refl _ _

/-- Big-O is transitive: `f = O(g) → g = O(h) → f = O(h)`.
@isnad1 id=bigo.2h3v.s4.732f1e7c8631 from=translated src=- shape=a4c11d09 vocab=d76903b9
-/
theorem BigO.trans {f g h : ℕ → ℕ} (h₁ : f =O g) (h₂ : g =O h) : f =O h :=
  IsBigO.trans h₁ h₂

/-- Pointwise `≤` implies big-O.
@isnad1 id=bigo.1h2v.s4.13f5a826f0e1 from=translated src=- shape=0c161374 vocab=3de7f4a5
-/
theorem BigO.of_le {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) : f =O g := by
  apply IsBigO.of_bound 1
  filter_upwards with n
  simp only [one_mul, Real.norm_natCast]
  exact_mod_cast h n

/-- Sum of two big-O functions: `f₁ = O(g) → f₂ = O(g) → (f₁ + f₂) = O(g)`.
@isnad1 id=bigo.2h3v.s5.b0d6c59e08fd from=translated src=- shape=2b866508 vocab=ae82657f
-/
theorem BigO.add {f₁ f₂ g : ℕ → ℕ} (h₁ : f₁ =O g) (h₂ : f₂ =O g) :
    (fun n => f₁ n + f₂ n) =O g := by
  show (fun n => ((f₁ n + f₂ n : ℕ) : ℝ)) =O[atTop] _
  have key := IsBigO.add h₁ h₂
  convert key using 1
  all_goals first | rfl | (ext n; push_cast; ring)

/-- Product of two big-O bounds: `f₁ = O(g₁) → f₂ = O(g₂) → (f₁·f₂) = O(g₁·g₂)`.
@isnad1 id=bigo.2h4v.s5.56cd97e139c8 from=translated src=- shape=220367dc vocab=be380102
-/
theorem BigO.mul {f₁ f₂ g₁ g₂ : ℕ → ℕ} (h₁ : f₁ =O g₁) (h₂ : f₂ =O g₂) :
    (fun n => f₁ n * f₂ n) =O (fun n => g₁ n * g₂ n) := by
  show (fun n => ((f₁ n * f₂ n : ℕ) : ℝ)) =O[atTop] (fun n => ((g₁ n * g₂ n : ℕ) : ℝ))
  have key := IsBigO.mul h₁ h₂
  convert key using 1
  all_goals first | rfl | (ext n; push_cast; ring)

/-- Raising both sides of a big-O bound to a fixed natural power preserves
big-O.
@isnad1 id=bigo.1h3v.s5.263b5b5fd37e from=translated src=- shape=203dcbf4 vocab=b41448dc
-/
theorem BigO.pow {f g : ℕ → ℕ} (h : f =O g) (k : ℕ) :
    (fun n => (f n) ^ k) =O (fun n => (g n) ^ k) := by
  induction k with
  | zero => exact BigO.refl fun _ => 1
  | succ k ih =>
      simpa only [pow_succ] using BigO.mul ih h

/-- Constant multiple preserves big-O.
@isnad1 id=bigo.1h3v.s4.73816fc886b7 from=translated src=- shape=1751b289 vocab=be380102
-/
theorem BigO.const_mul_left (c : ℕ) {f g : ℕ → ℕ} (h : f =O g) :
    (fun n => c * f n) =O g := by
  show (fun n => ((c * f n : ℕ) : ℝ)) =O[atTop] _
  have hcf : (fun n => (c : ℝ) * (f n : ℝ)) =O[atTop] (fun n => (f n : ℝ)) :=
    IsBigO.const_mul_left (isBigO_refl _ _) (c : ℝ)
  have key := IsBigO.trans hcf h
  convert key using 1
  ext n; push_cast; ring

-- ════════════════════════════════════════════════════════════════════════
-- LittleO core lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Little-o implies big-O: if `f = o(g)` then `f = O(g)`.
@isnad1 id=bigo.1h2v.s3.dddfc2667fc8 from=translated src=- shape=42193498 vocab=6e953e36
-/
theorem LittleO.isBigO {f g : ℕ → ℕ} (h : f =o g) : f =O g :=
  IsLittleO.isBigO h

/-- Little-o is transitive: `f = o(g) → g = o(h) → f = o(h)`.
@isnad1 id=littleo.2h3v.s4.96c63d9e7db3 from=translated src=- shape=a4c11d09 vocab=c9ff6b3f
-/
theorem LittleO.trans {f g h : ℕ → ℕ} (h₁ : f =o g) (h₂ : g =o h) : f =o h :=
  IsLittleO.trans_isBigO h₁ (IsLittleO.isBigO h₂)

/-- Mixed transitivity: `f = o(g) → g = O(h) → f = o(h)`.
@isnad1 id=littleo.2h3v.s4.4616bfcc8b79 from=translated src=- shape=a4c11d09 vocab=6e953e36
-/
theorem LittleO.trans_bigO {f g h : ℕ → ℕ} (h₁ : f =o g) (h₂ : g =O h) : f =o h :=
  IsLittleO.trans_isBigO h₁ h₂

/-- Mixed transitivity: `f = O(g) → g = o(h) → f = o(h)`.
@isnad1 id=littleo.2h3v.s4.d55fae6bb6d0 from=translated src=- shape=23cf5086 vocab=6e953e36
-/
theorem BigO.trans_littleO {f g h : ℕ → ℕ} (h₁ : f =O g) (h₂ : g =o h) : f =o h :=
  IsBigO.trans_isLittleO h₁ h₂

/-- Sum of two little-o functions: `f₁ = o(g) → f₂ = o(g) → (f₁ + f₂) = o(g)`.
@isnad1 id=littleo.2h3v.s5.3ffab79eb8f8 from=translated src=- shape=2b866508 vocab=45c5b8b5
-/
theorem LittleO.add {f₁ f₂ g : ℕ → ℕ} (h₁ : f₁ =o g) (h₂ : f₂ =o g) :
    (fun n => f₁ n + f₂ n) =o g := by
  show (fun n => ((f₁ n + f₂ n : ℕ) : ℝ)) =o[atTop] _
  have key := IsLittleO.add h₁ h₂
  convert key using 1
  all_goals first | rfl | (ext n; push_cast; ring)

/-- Constant multiple preserves little-o.
@isnad1 id=littleo.1h3v.s4.6fba58af464d from=translated src=- shape=1751b289 vocab=64e9f637
-/
theorem LittleO.const_mul_left (c : ℕ) {f g : ℕ → ℕ} (h : f =o g) :
    (fun n => c * f n) =o g := by
  show (fun n => ((c * f n : ℕ) : ℝ)) =o[atTop] _
  have hcf : (fun n => (c : ℝ) * (f n : ℝ)) =O[atTop] (fun n => (f n : ℝ)) :=
    IsBigO.const_mul_left (isBigO_refl _ _) (c : ℝ)
  have key := IsBigO.trans_isLittleO hcf h
  convert key using 1
  ext n; push_cast; ring

-- ════════════════════════════════════════════════════════════════════════
-- BigO arithmetic lemmas (addition bounds)
-- ════════════════════════════════════════════════════════════════════════

/-- `T₁` is big-O of `T₁ + T₂`.
@isnad1 id=bigo.0h2v.s4.ea6a913b4763 from=translated src=- shape=0469d9d7 vocab=ae82657f
-/
theorem BigO.le_add_left (T₁ T₂ : ℕ → ℕ) :
    T₁ =O (fun n => T₁ n + T₂ n) := by
  show (fun n => ((T₁ n : ℕ) : ℝ)) =O[atTop] (fun n => ((T₁ n + T₂ n : ℕ) : ℝ))
  apply IsBigO.of_bound 1
  filter_upwards with n
  simp only [Nat.cast_add, one_mul, Real.norm_natCast]
  exact le_of_le_of_eq (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) (T₂ n)))
    (abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).symm

/-- `T₂` is big-O of `T₁ + T₂`.
@isnad1 id=bigo.0h2v.s4.eb0f34761590 from=translated src=- shape=fa5d57f4 vocab=ae82657f
-/
theorem BigO.le_add_right (T₁ T₂ : ℕ → ℕ) :
    T₂ =O (fun n => T₁ n + T₂ n) := by
  show (fun n => ((T₂ n : ℕ) : ℝ)) =O[atTop] (fun n => ((T₁ n + T₂ n : ℕ) : ℝ))
  apply IsBigO.of_bound 1
  filter_upwards with n
  simp only [Nat.cast_add, one_mul, Real.norm_natCast]
  exact le_of_le_of_eq (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) (T₁ n)))
    (abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).symm

/-- If `f₁ =O T₁` and `f₂ =O T₂`, then `c * f₁ + f₂ =O (T₁ + T₂)`.
@isnad1 id=bigo.2h5v.s6.b57760a119d5 from=translated src=- shape=d6e62f25 vocab=28d5c550
-/
theorem BigO.const_mul_add (c : ℕ) {f₁ f₂ T₁ T₂ : ℕ → ℕ}
    (ho₁ : f₁ =O T₁) (ho₂ : f₂ =O T₂) :
    (fun n => c * f₁ n + f₂ n) =O (fun n => T₁ n + T₂ n) := by
  show (fun n => ((c * f₁ n + f₂ n : ℕ) : ℝ)) =O[atTop]
       (fun n => ((T₁ n + T₂ n : ℕ) : ℝ))
  have hf₁ : (fun n => ((f₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := IsBigO.trans ho₁ (le_add_left T₁ T₂)
  have hcf₁ : (fun n => ((c * f₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := by
    have : (fun n => (c : ℝ) * ((f₁ n : ℕ) : ℝ)) =O[atTop]
        (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) :=
      IsBigO.const_mul_left hf₁ c
    convert this using 1
    ext n; push_cast; ring
  have hf₂ : (fun n => ((f₂ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := IsBigO.trans ho₂ (le_add_right T₁ T₂)
  have := IsBigO.add hcf₁ hf₂
  convert this using 1
  all_goals first | rfl | (ext n; push_cast; ring)

-- ════════════════════════════════════════════════════════════════════════
-- BigO max and power bounds
-- ════════════════════════════════════════════════════════════════════════

/-- `T₁` is big-O of `max T₁ T₂`.
@isnad1 id=bigo.0h2v.s4.46b03f4a7284 from=translated src=- shape=10c5fe3c vocab=cc86d071
-/
theorem BigO.le_max_left (T₁ T₂ : ℕ → ℕ) :
    T₁ =O (fun n => max (T₁ n) (T₂ n)) :=
  BigO.of_le fun _ => Nat.le_max_left _ _

/-- `T₂` is big-O of `max T₁ T₂`.
@isnad1 id=bigo.0h2v.s4.0af8b86c9d15 from=translated src=- shape=b81a25f9 vocab=cc86d071
-/
theorem BigO.le_max_right (T₁ T₂ : ℕ → ℕ) :
    T₂ =O (fun n => max (T₁ n) (T₂ n)) :=
  BigO.of_le fun _ => Nat.le_max_right _ _

/-- `max T₁ T₂ =O (T₁ + T₂)`.
@isnad1 id=bigo.0h2v.s5.eca48a938f1a from=translated src=- shape=63953d6e vocab=823b9b0c
-/
theorem BigO.max_le_add (T₁ T₂ : ℕ → ℕ) :
    (fun n => max (T₁ n) (T₂ n)) =O (fun n => T₁ n + T₂ n) :=
  BigO.of_le fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

/-- A pointwise maximum of two functions with the same asymptotic bound has
that bound as well.
@isnad1 id=bigo.2h3v.s5.8abfcba193a7 from=translated src=- shape=db85ae1a vocab=cc86d071
-/
theorem BigO.max_same {f₁ f₂ g : ℕ → ℕ} (h₁ : f₁ =O g) (h₂ : f₂ =O g) :
    (fun n => max (f₁ n) (f₂ n)) =O g :=
  (BigO.max_le_add f₁ f₂).trans (BigO.add h₁ h₂)

/-- Any function is big-O of itself-plus-constant: `f =O (fun n => f n + c)`.
@isnad1 id=bigo.0h2v.s4.16a5ad00560d from=translated src=- shape=1b1c65d0 vocab=ae82657f
-/
theorem BigO.self_le_add_const (f : ℕ → ℕ) (c : ℕ) :
    f =O (fun n => f n + c) :=
  BigO.of_le fun _ => Nat.le_add_right _ _

/-- `n^k` is big-O of `n^(k+1)` on sequences with `n ≥ 1`.
@isnad1 id=bigo.0h1v.s5.c7881feab965 from=translated src=- shape=3063a88d vocab=932cc747
-/
theorem BigO.pow_le_pow_succ (k : ℕ) :
    (· ^ k) =O ((· ^ (k + 1)) : ℕ → ℕ) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [one_mul, Real.norm_natCast]
  exact_mod_cast Nat.pow_le_pow_right hn (Nat.le_succ k)

/-- `n^j =O n^k` when `j ≤ k` (on sequences with `n ≥ 1`).
@isnad1 id=bigo.1h2v.s5.a67b9fc088dd from=translated src=- shape=48ffc658 vocab=25200ac8
-/
theorem BigO.pow_le_pow_right {j k : ℕ} (hjk : j ≤ k) :
    (· ^ j) =O ((· ^ k) : ℕ → ℕ) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [one_mul, Real.norm_natCast]
  exact_mod_cast Nat.pow_le_pow_right hn hjk

/-- A constant function is big-O of `n^k` (eventually `n^k ≥ 1`).
@isnad1 id=bigo.0h2v.s4.f650aa521a27 from=translated src=- shape=e604873b vocab=b41448dc
-/
theorem BigO.const_le_pow (c k : ℕ) :
    (fun _ : ℕ => c) =O ((· ^ k) : ℕ → ℕ) := by
  apply IsBigO.of_bound c
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_natCast]
  have : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
  exact_mod_cast le_mul_of_one_le_right (Nat.zero_le _) this

/-- Every fixed natural constant is eventually bounded by a constant multiple
of the unshifted base-two logarithm. The threshold `n ≥ 2` is necessary because
`Nat.log 2 0 = Nat.log 2 1 = 0`.
@isnad1 id=bigo.0h1v.s3.a486702c8776 from=translated src=- shape=a9e1e803 vocab=d619587f
-/
theorem BigO.const_le_logTwo (c : ℕ) :
    (fun _ : ℕ => c) =O (fun n => Nat.log 2 n) := by
  apply IsBigO.of_bound c
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  simp only [Real.norm_natCast]
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) hn
  exact_mod_cast le_mul_of_one_le_right (Nat.zero_le c) hlog

/-- `n^j + n^k =O n^(max j k)` on sequences with `n ≥ 1`.
@isnad1 id=bigo.0h2v.s5.18f8f8fe9e66 from=translated src=- shape=8b4997c5 vocab=4db6ceb4
-/
theorem BigO.pow_add_pow (j k : ℕ) :
    (fun n => n ^ j + n ^ k) =O ((· ^ max j k) : ℕ → ℕ) := by
  apply IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_natCast]
  have h1 : n ^ j ≤ n ^ max j k := Nat.pow_le_pow_right hn (Nat.le_max_left j k)
  have h2 : n ^ k ≤ n ^ max j k := Nat.pow_le_pow_right hn (Nat.le_max_right j k)
  have : n ^ j + n ^ k ≤ 2 * n ^ max j k := by omega
  exact_mod_cast this

/-! ### Natural polynomial evaluation -/

/-- Evaluation of a polynomial with natural coefficients is monotone in its
    natural-number argument.
@isnad1 id=monotone.0h1v.s4.1a2a5bf70df2 from=translated src=- shape=1f4dac01 vocab=abb5aa40
-/
theorem polynomial_eval_mono_nat (p : Polynomial ℕ) : Monotone p.eval := by
  intro m n hmn
  change p.eval m ≤ p.eval n
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ =>
    Nat.mul_le_mul_left (p.coeff i) (Nat.pow_le_pow_left hmn i)

-- ════════════════════════════════════════════════════════════════════════
-- BigO ⇒ polynomial bound
-- ════════════════════════════════════════════════════════════════════════

/-- **From `f =O (·^k)` to an explicit polynomial bound.** If `f : ℕ → ℕ`
    is big-O of `n^k`, then there exists a polynomial `p` in `Polynomial ℕ`
    with `f n ≤ p.eval n` *for every* `n` (not just eventually).

    The standard big-O definition gives only an asymptotic bound; this lemma
    turns that into an everywhere-bound by (i) extracting a real constant
    `C` and threshold `N` such that `f n ≤ C · n^k` for `n ≥ N`, (ii)
    rounding `C` up to a natural number, and (iii) adding a constant term
    that dominates `f` on the initial segment `[0, N)`.

    This is the bridge from big-O hypotheses to the explicit
    `Polynomial ℕ` shape expected by definitions like `PolyBalanced` and
    by time-bound packaging in the `WitnessNTMConstruction`
    construction.
@isnad1 id=ex.1h2v.s5.c48d3d3deb22 from=translated src=- shape=3dfc1397 vocab=d85cb79c
-/
theorem BigO.pow_polynomial_bound {f : ℕ → ℕ} {k : ℕ} (h : f =O (· ^ k)) :
    ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n := by
  rw [BigO, Asymptotics.isBigO_iff] at h
  obtain ⟨C, hC⟩ := h
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  refine ⟨Polynomial.C ⌈C⌉₊ * Polynomial.X ^ k +
          Polynomial.C ((Finset.range N).sup f), ?_⟩
  intro n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
             Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hn : n < N
  · have : f n ≤ (Finset.range N).sup f :=
      Finset.le_sup (f := f) (Finset.mem_range.mpr hn)
    omega
  · push Not at hn
    have hb := hN n hn
    simp only [Real.norm_natCast] at hb
    have hC_le : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
    have h_nk_nonneg : (0 : ℝ) ≤ ((n ^ k : ℕ) : ℝ) := by positivity
    have h_real : (f n : ℝ) ≤ (⌈C⌉₊ : ℝ) * ((n ^ k : ℕ) : ℝ) :=
      le_trans hb (mul_le_mul_of_nonneg_right hC_le h_nk_nonneg)
    have h_nat : f n ≤ ⌈C⌉₊ * n ^ k := by exact_mod_cast h_real
    omega

/-- **From a polynomial bound to `=O (·^deg)`.** If `f : ℕ → ℕ` is
    pointwise bounded by a polynomial `p`, then `f =O (·^p.natDegree)`.

    Companion to `BigO.pow_polynomial_bound`; the pair lets you convert
    freely between the big-O form used by complexity classes and the
    explicit `Polynomial ℕ` shape used in `PolyBalanced` and in
    running-time packaging for composite machines.
@isnad1 id=bigo.1h2v.s5.5b95a0648a51 from=translated src=- shape=0cc85e12 vocab=e954a736
-/
theorem BigO.of_polynomial_bound {f : ℕ → ℕ} (p : Polynomial ℕ)
    (h : ∀ n, f n ≤ p.eval n) : f =O (· ^ p.natDegree) := by
  set S : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i with hS
  apply IsBigO.of_bound S
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_natCast]
  have hp : p.eval n ≤ S * n ^ p.natDegree := by
    rw [Polynomial.eval_eq_sum_range, hS, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ p.natDegree := by
      rw [Finset.mem_range] at hi; omega
    have : n ^ i ≤ n ^ p.natDegree := Nat.pow_le_pow_right hn hi'
    exact Nat.mul_le_mul_left _ this
  exact_mod_cast le_trans (h n) hp

/-- Extract a natural-number constant and threshold from a big-O bound:
    `f =O g` yields `c` and `N` with `f n ≤ c * g n` for all `n ≥ N`.
@isnad1 id=ex.1h2v.s5.d6a5c3c49548 from=translated src=- shape=b6e1b7e2 vocab=55819fb8
-/
theorem BigO.exists_nat_bound {f g : ℕ → ℕ} (h : f =O g) :
    ∃ (c N : ℕ), ∀ n, N ≤ n → f n ≤ c * g n := by
  rw [BigO, Asymptotics.isBigO_iff] at h
  obtain ⟨C, hC⟩ := h
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  refine ⟨⌈C⌉₊, N, fun n hn => ?_⟩
  have hb := hN n hn
  simp only [Real.norm_natCast] at hb
  have hr : (f n : ℝ) ≤ (⌈C⌉₊ : ℝ) * (g n : ℝ) :=
    le_trans hb (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
  exact_mod_cast hr

/-- Binary widths of power-bounded natural values are logarithmic. The proof
raises the eventual power bound by one, which uniformly handles exponent zero
and constant functions.
@isnad1 id=bigo.1h2v.s5.cfa2c3191cb9 from=translated src=- shape=cbd83fd8 vocab=c9a828c8
-/
theorem BigO.natSize_of_pow {f : ℕ → ℕ} {d : ℕ}
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (fun n => (f n).size) =O (fun n => Nat.log 2 n) := by
  obtain ⟨c, N, hbound⟩ := BigO.exists_nat_bound hf
  rw [BigO]
  apply Asymptotics.IsBigO.of_bound (2 * (d + 1))
  filter_upwards [Filter.eventually_ge_atTop (max 2 (max c N))] with n hn
  simp only [Real.norm_natCast]
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left 2 (max c N)) hn
  have hcn : c ≤ n := le_trans (le_trans (Nat.le_max_left c N)
    (Nat.le_max_right 2 (max c N))) hn
  have hNn : N ≤ n := le_trans (le_trans (Nat.le_max_right c N)
    (Nat.le_max_right 2 (max c N))) hn
  have hvalue : f n ≤ n ^ (d + 1) := by
    calc
      f n ≤ c * n ^ d := hbound n hNn
      _ ≤ n * n ^ d := Nat.mul_le_mul_right _ hcn
      _ = n ^ (d + 1) := by rw [pow_succ']
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) hn2
  have hpow : n ^ (d + 1) < 2 ^ ((d + 1) * (Nat.log 2 n + 1)) := by
    calc
      n ^ (d + 1) < (2 ^ (Nat.log 2 n + 1)) ^ (d + 1) :=
        Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by omega) n) (by omega)
      _ = 2 ^ ((d + 1) * (Nat.log 2 n + 1)) := by
        rw [← pow_mul']
  have hsize : (f n).size ≤ (d + 1) * (Nat.log 2 n + 1) :=
    Nat.size_le.mpr (lt_of_le_of_lt hvalue hpow)
  have hlog' : Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n := by omega
  have hfinal : (f n).size ≤ (2 * (d + 1)) * Nat.log 2 n :=
    hsize.trans (by
      calc
        (d + 1) * (Nat.log 2 n + 1) ≤
            (d + 1) * (2 * Nat.log 2 n) := Nat.mul_le_mul_left _ hlog'
        _ = (2 * (d + 1)) * Nat.log 2 n := by ring)
  exact_mod_cast hfinal

/-- Binary widths of pointwise polynomial-bounded natural values are logarithmic.
@isnad1 id=bigo.1h2v.s5.065c3425bf82 from=translated src=- shape=5543da9c vocab=a63d363b
-/
theorem BigO.natSize_of_polynomial_bound {f : ℕ → ℕ}
    (p : Polynomial ℕ) (hf : ∀ n, f n ≤ p.eval n) :
    (fun n => (f n).size) =O (fun n => Nat.log 2 n) :=
  BigO.natSize_of_pow (BigO.of_polynomial_bound p hf)

/-- The binary width of a fixed natural polynomial evaluation is logarithmic.
@isnad1 id=bigo.0h1v.s4.f80df93739f3 from=translated src=- shape=4d9336bf vocab=b3738f84
-/
theorem BigO.natSize_polynomial_eval (p : Polynomial ℕ) :
    (fun n => (p.eval n).size) =O (fun n => Nat.log 2 n) :=
  BigO.natSize_of_polynomial_bound p fun _ => le_rfl

/-- Strict power gap, shifted to the everywhere-positive base `n + 1`:
    `(n + 1)^p = o((n + 1)^q)` when `p < q`.
@isnad1 id=littleo.1h2v.s6.c95603989574 from=translated src=- shape=5a7d8afc vocab=9bbc3fef
-/
theorem LittleO.pow_lt_pow {p q : ℕ} (hpq : p < q) :
    LittleO (fun n => (n + 1) ^ p) (fun n => (n + 1) ^ q) := by
  have hbase : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have key :=
    (Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) hpq).comp_tendsto hbase
  exact key.congr (fun n => by simp only [Function.comp_apply]; push_cast; ring)
    (fun n => by simp only [Function.comp_apply]; push_cast; ring)

end Complexity
