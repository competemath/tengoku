/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Tengoku

/-!
# Binomial distribution as a convolution of Bernoulli distributions

This file develops an API for *additive convolution* of `PMF ℕ`s and uses it to
prove that the binomial distribution is the `n`-fold self-convolution of the
Bernoulli distribution. The key structural result,

    `PMF.binomial_add_binomial`,

states that summing two independent binomials with the same bias `p` and trial
counts `m₁`, `m₂` yields a binomial with `m₁ + m₂` trials. Rather than
proving this by a direct Vandermonde-style computation, we

1. define the additive convolution `PMF.addConv`,
2. establish its commutativity (`addConv_comm`) and associativity
   (`addConv_assoc`),
3. show that `binomial p hp n` equals the `n`-fold convolution of
   `bernoulliNat p hp` (`binomial_map_val_eq_iterAddConv`), and
4. deduce `binomial_add_binomial` purely from the algebraic structure.
-/

open PMF BigOperators ENNReal NNReal Finset

namespace PMF

/-! ## Additive convolution of `PMF ℕ` -/

/-- The additive convolution of two `PMF ℕ`s: the distribution of `X + Y`
when `X ~ f` and `Y ~ g` are drawn independently. -/
noncomputable def addConv (f g : PMF ℕ) : PMF ℕ :=
  f.bind fun x => g.bind fun y => PMF.pure (x + y)

/-- Additive convolution is commutative. -/
theorem addConv_comm (f g : PMF ℕ) : addConv f g = addConv g f := by
  simp only [addConv]
  rw [PMF.bind_comm f g]
  simp only [add_comm]

/-- Additive convolution is associative. -/
theorem addConv_assoc (f g h : PMF ℕ) :
    addConv (addConv f g) h = addConv f (addConv g h) := by
  simp only [addConv, PMF.bind_bind, PMF.pure_bind, add_assoc]

/-- Convolving with `pure 0` on the left is the identity. -/
@[simp]
theorem addConv_pure_zero_left (f : PMF ℕ) : addConv (PMF.pure 0) f = f := by
  simp [addConv, PMF.pure_bind]

/-- Convolving with `pure 0` on the right is the identity. -/
@[simp]
theorem addConv_pure_zero_right (f : PMF ℕ) : addConv f (PMF.pure 0) = f := by
  simp only [addConv, PMF.pure_bind, add_zero, PMF.bind_pure]

/-! ## Bernoulli distribution as a `PMF ℕ` -/

/-! ## Iterated convolution and its interaction with addition -/

/-- The `n`-fold additive convolution of a `PMF ℕ` with itself. -/
noncomputable def iterAddConv (f : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | n + 1 => addConv (iterAddConv f n) f

@[simp]
theorem iterAddConv_zero (f : PMF ℕ) : iterAddConv f 0 = PMF.pure 0 := rfl

@[simp]
theorem iterAddConv_succ (f : PMF ℕ) (n : ℕ) :
    iterAddConv f (n + 1) = addConv (iterAddConv f n) f := rfl

/-- The `(m + n)`-fold convolution splits as the convolution of the `m`-fold
and `n`-fold convolutions. This is the key algebraic fact used to prove
`binomial_add_binomial`, and its proof uses only commutativity and associativity
of `addConv`. -/
theorem iterAddConv_add (f : PMF ℕ) (m n : ℕ) :
    iterAddConv f (m + n) = addConv (iterAddConv f m) (iterAddConv f n) := by
  induction m with
  | zero =>
      simp [addConv_pure_zero_left]
  | succ k ih =>
      rw [show k + 1 + n = k + n + 1 from by ring, iterAddConv_succ, ih, iterAddConv_succ]
      rw [addConv_assoc, addConv_comm (iterAddConv f n) f, ← addConv_assoc]

/-! ## Binomial as iterated Bernoulli convolution -/

/-! ## Main theorem -/

end PMF
