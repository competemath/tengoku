/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku
/-!
# Trigonometric polynomials

A **trigonometric polynomial** in `k` real variables is a finite `ℂ`-linear combination of the
characters `x ↦ exp (i ⟨ω, x⟩)`, where the frequency vectors `ω` range over a finite set.
These are exactly the trigonometric polynomials, and they are closed under addition,
scaling, multiplication by a single character, products, and complex conjugation — the
algebraic facts that drive the Fourier representation of the quantum kernel.

This module is quantum-free: it only knows about `ℂ`, finite sums, the real pairing
`⟨ω, x⟩ = ∑ i, ω i * x i`, and real one-variable trigonometric identities.
-/

@[expose] public section

namespace QuantumAlg

open Complex BigOperators

variable {k : ℕ}

/-- The real pairing `⟨ω, x⟩ = ∑ i, ω i * x i` of a frequency vector with a data point. -/
def freqDot (ω x : Fin k → ℝ) : ℝ := ∑ i, ω i * x i

/-- An **trigonometric polynomial** in `k` real variables: the function
`x ↦ ∑_{ω ∈ freqs} coeff ω · exp(i⟨ω, x⟩)`. The data is a finite set of
frequency vectors together with a complex coefficient at each. -/
structure TrigPolynomial (k : ℕ) where
  /-- The finite set of frequency vectors carrying nonzero (or bookkept) coefficients. -/
  freqs : Finset (Fin k → ℝ)
  /-- The complex coefficient at each frequency. -/
  coeff : (Fin k → ℝ) → ℂ

/-- Evaluate an trigonometric polynomial at a data point `x`. -/
noncomputable def TrigPolynomial.eval (f : TrigPolynomial k) (x : Fin k → ℝ) : ℂ :=
  ∑ ω ∈ f.freqs, f.coeff ω * Complex.exp (Complex.I * (freqDot ω x : ℂ))

/-- The pairing is additive in the frequency argument.
@isnad1 id=eq.0h4v.s6.2b84dd07c092 from=translated src=- shape=a1c791df vocab=f281d401
-/
theorem freqDot_add (ω₁ ω₂ x : Fin k → ℝ) :
    freqDot (ω₁ + ω₂) x = freqDot ω₁ x + freqDot ω₂ x := by
  simp only [freqDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The pairing negates with the frequency argument.
@isnad1 id=eq.0h3v.s5.b6b66a5cbd3d from=translated src=- shape=03ecd70a vocab=e06f7eec
-/
theorem freqDot_neg (ω x : Fin k → ℝ) : freqDot (-ω) x = -freqDot ω x := by
  simp only [freqDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- The pairing is additive in the data argument.
@isnad1 id=eq.0h4v.s6.935a1261530e from=translated src=- shape=de7ba5db vocab=f281d401
-/
theorem freqDot_add_right (ω x₁ x₂ : Fin k → ℝ) :
    freqDot ω (x₁ + x₂) = freqDot ω x₁ + freqDot ω x₂ := by
  simp only [freqDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The pairing is symmetric.
@isnad1 id=eq.0h3v.s4.3f93f7eb2d2c from=translated src=- shape=7d1fcdcb vocab=87daefa3
-/
theorem freqDot_comm (ω x : Fin k → ℝ) : freqDot ω x = freqDot x ω := by
  unfold freqDot; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The zero trigonometric polynomial (empty frequency set). -/
def TrigPolynomial.zero : TrigPolynomial k where
  freqs := ∅
  coeff := fun _ => 0

/--
@isnad1 id=eq.0h2v.s4.a7c8181b3ddc from=translated src=- shape=d955200f vocab=13a79852
-/
@[simp] theorem TrigPolynomial.eval_zero (x : Fin k → ℝ) :
    (TrigPolynomial.zero : TrigPolynomial k).eval x = 0 := by
  simp [TrigPolynomial.eval, TrigPolynomial.zero]

/-- Scale an trigonometric polynomial by a complex constant. -/
def TrigPolynomial.smul (c : ℂ) (f : TrigPolynomial k) : TrigPolynomial k where
  freqs := f.freqs
  coeff := fun ω => c * f.coeff ω

/--
@isnad1 id=eq.0h4v.s5.5ab8262a5494 from=translated src=- shape=081c7a5f vocab=f4d1b42c
-/
theorem TrigPolynomial.eval_smul (c : ℂ) (f : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.smul c).eval x = c * f.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.smul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- Sum of two trigonometric polynomials: union of frequencies, with guarded
coefficients added. -/
noncomputable def TrigPolynomial.add (f g : TrigPolynomial k) : TrigPolynomial k where
  freqs := f.freqs ∪ g.freqs
  coeff := fun ω =>
    (if ω ∈ f.freqs then f.coeff ω else 0) + (if ω ∈ g.freqs then g.coeff ω else 0)

/--
@isnad1 id=eq.0h4v.s5.d31c4b373a8f from=translated src=- shape=6d2a4b45 vocab=ffcb758a
-/
theorem TrigPolynomial.eval_add (f g : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.add g).eval x = f.eval x + g.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.add, add_mul, Finset.sum_add_distrib]
  simp_all

/-- Multiply an trigonometric polynomial by the character `e^{i⟨a,x⟩}`: shifts every frequency
by `a` and leaves the coefficients (re-indexed) unchanged. -/
noncomputable def TrigPolynomial.expMul (a : Fin k → ℝ) (f : TrigPolynomial k) :
    TrigPolynomial k where
  freqs := f.freqs.image (fun ω => ω + a)
  coeff := fun ω => f.coeff (ω - a)

/--
@isnad1 id=eq.0h4v.s5.246adcc97131 from=translated src=- shape=7bad4941 vocab=00b143e0
-/
theorem TrigPolynomial.eval_expMul (a : Fin k → ℝ) (f : TrigPolynomial k)
    (x : Fin k → ℝ) :
    (f.expMul a).eval x = Complex.exp (Complex.I * (freqDot a x : ℂ)) * f.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.expMul]
  rw [Finset.sum_image (by intro p _ q _ h; exact add_right_cancel h), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [add_sub_cancel_right, freqDot_add]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-- A finite sum of trigonometric polynomials: frequencies union over the index,
with coefficients added. -/
noncomputable def TrigPolynomial.sum {ι : Type*} (s : Finset ι)
    (F : ι → TrigPolynomial k) : TrigPolynomial k where
  freqs := s.biUnion (fun i => (F i).freqs)
  coeff := fun ω => ∑ i ∈ s, (if ω ∈ (F i).freqs then (F i).coeff ω else 0)

/--
@isnad1 id=eq.0h5v.s5.6d33ffeb29c5 from=translated src=- shape=544adf50 vocab=e80b5c6a
-/
theorem TrigPolynomial.eval_sum {ι : Type*} (s : Finset ι) (F : ι → TrigPolynomial k)
    (x : Fin k → ℝ) :
    (TrigPolynomial.sum s F).eval x = ∑ i ∈ s, (F i).eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← Finset.sum_subset (Finset.subset_biUnion_of_mem (fun j => (F j).freqs) hi)
        (fun ω _ hω => by rw [ite_eq_right hω, zero_mul])]
  exact Finset.sum_congr rfl (fun ω hω => by rw [ite_eq_left hω])

/-- Product of two trigonometric polynomials: realised as the sum, over `f`'s frequencies, of `g`
shifted by that frequency and scaled by `f`'s coefficient. -/
noncomputable def TrigPolynomial.mul (f g : TrigPolynomial k) : TrigPolynomial k :=
  TrigPolynomial.sum f.freqs (fun ω => (g.expMul ω).smul (f.coeff ω))

/--
@isnad1 id=eq.0h4v.s5.f84cfc19bca6 from=translated src=- shape=6d2a4b45 vocab=1ac787b0
-/
theorem TrigPolynomial.eval_mul (f g : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.mul g).eval x = f.eval x * g.eval x := by
  rw [TrigPolynomial.mul, TrigPolynomial.eval_sum]
  simp only [TrigPolynomial.eval_smul, TrigPolynomial.eval_expMul]
  rw [Finset.sum_congr rfl (fun ω _ => by ring :
        ∀ ω ∈ f.freqs, f.coeff ω * (Complex.exp (Complex.I * (freqDot ω x : ℂ)) * g.eval x)
          = (f.coeff ω * Complex.exp (Complex.I * (freqDot ω x : ℂ))) * g.eval x),
    ← Finset.sum_mul]
  rfl

/-- Complex conjugate of an trigonometric polynomial: negate frequencies, conjugate coefficients. -/
noncomputable def TrigPolynomial.conj (f : TrigPolynomial k) : TrigPolynomial k where
  freqs := f.freqs.image (fun ω => -ω)
  coeff := fun ω => (starRingEnd ℂ) (f.coeff (-ω))

/--
@isnad1 id=eq.0h3v.s5.922aea74996c from=translated src=- shape=8b314091 vocab=eb231e71
-/
theorem TrigPolynomial.eval_conj (f : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.conj).eval x = (starRingEnd ℂ) (f.eval x) := by
  simp only [TrigPolynomial.eval, TrigPolynomial.conj]
  rw [map_sum, Finset.sum_image (by intro p _ q _ h; exact neg_injective h)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [neg_neg, map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  rw [freqDot_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  simp_all

/-- The canonical coefficient of an trigonometric polynomial at a frequency: its (guarded)
contribution. Two trigonometric polynomials with the same values have the same canonical
coefficients (`coeffAt_eq_of_eval_eq`). -/
noncomputable def TrigPolynomial.coeffAt (f : TrigPolynomial k) (ω : Fin k → ℝ) : ℂ :=
  if ω ∈ f.freqs then f.coeff ω else 0

/-- Pairing against a single scaled basis frequency picks out one coordinate.
@isnad1 id=eq.0h4v.s6.c18a8d60d9b5 from=translated src=- shape=7ef0e9eb vocab=283532b2
-/
theorem freqDot_smul_single (ω : Fin k → ℝ) (t : ℝ) (j : Fin k) :
    freqDot ω (t • Pi.single j (1 : ℝ)) = t * ω j := by
  rw [freqDot, Finset.sum_eq_single j]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]; ring
  · simp_all
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- If `t ↦ exp(i t a)` and `t ↦ exp(i t b)` agree for all real `t`, then `a = b`.
@isnad1 id=eq.1h2v.s5.41dd5cdce66c from=translated src=- shape=53805fbe vocab=ecfafdc9
-/
theorem exp_I_real_inj {a b : ℝ}
    (h : ∀ t : ℝ, Complex.exp (Complex.I * ((t * a : ℝ) : ℂ))
                = Complex.exp (Complex.I * ((t * b : ℝ) : ℂ))) : a = b := by
  by_contra hab
  have hc : a - b ≠ 0 := sub_ne_zero.mpr hab
  have key := h (Real.pi / (a - b))
  have e1 : Complex.exp (Complex.I * ((Real.pi / (a - b) * a : ℝ) : ℂ))
          / Complex.exp (Complex.I * ((Real.pi / (a - b) * b : ℝ) : ℂ)) = 1 := by
    rw [key, div_self (Complex.exp_ne_zero _)]
  rw [← Complex.exp_sub] at e1
  have harg : Complex.I * ((Real.pi / (a - b) * a : ℝ) : ℂ)
            - Complex.I * ((Real.pi / (a - b) * b : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    rw [← mul_sub, ← Complex.ofReal_sub]
    have hpi : Real.pi / (a - b) * a - Real.pi / (a - b) * b = Real.pi := by
      rw [← mul_sub, div_mul_cancel₀ _ hc]
    rw [hpi]; ring
  rw [harg, Complex.exp_pi_mul_I] at e1
  norm_num at e1

/-- The character `x ↦ exp(i⟨ω,x⟩)` as a monoid homomorphism from the additive group of
data points (written multiplicatively) to `ℂ`. -/
noncomputable def chiHom (ω : Fin k → ℝ) : Multiplicative (Fin k → ℝ) →* ℂ where
  toFun := fun y => Complex.exp (Complex.I * (freqDot ω (Multiplicative.toAdd y) : ℂ))
  map_one' := by
    change Complex.exp (Complex.I *
      ((freqDot ω (Multiplicative.toAdd (1 : Multiplicative (Fin k → ℝ))) : ℝ) : ℂ)) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin k → ℝ))
        = (0 : Fin k → ℝ) from rfl]
    simp [freqDot]
  map_mul' := fun y₁ y₂ => by
    change Complex.exp (Complex.I * ((freqDot ω (Multiplicative.toAdd (y₁ * y₂)) : ℝ) : ℂ))
       = Complex.exp (Complex.I * ((freqDot ω (Multiplicative.toAdd y₁) : ℝ) : ℂ))
       * Complex.exp (Complex.I * ((freqDot ω (Multiplicative.toAdd y₂) : ℝ) : ℂ))
    rw [show Multiplicative.toAdd (y₁ * y₂)
          = Multiplicative.toAdd y₁ + Multiplicative.toAdd y₂ from rfl, freqDot_add_right]
    push_cast
    rw [mul_add, Complex.exp_add]

/--
@isnad1 id=eq.0h3v.s7.1b1bf2ff4886 from=translated src=- shape=50fa61d1 vocab=3fa39389
-/
@[simp] theorem chiHom_apply (ω : Fin k → ℝ) (y : Multiplicative (Fin k → ℝ)) :
    (chiHom ω) y = Complex.exp (Complex.I * (freqDot ω (Multiplicative.toAdd y) : ℂ)) := rfl

/-- Distinct frequencies give distinct characters.
@isnad1 id=injectiv.0h1v.s5.30b434ccec7c from=translated src=- shape=7cb3abe9 vocab=c0a729de
-/
theorem chiHom_injective :
    Function.Injective
      (chiHom : (Fin k → ℝ) → (Multiplicative (Fin k → ℝ) →* ℂ)) := by
  intro ω ω' h
  funext j
  refine exp_I_real_inj (fun t => ?_)
  have hto : Multiplicative.toAdd (Multiplicative.ofAdd (t • Pi.single j (1 : ℝ)))
      = t • Pi.single j (1 : ℝ) := rfl
  have hc := DFunLike.congr_fun h (Multiplicative.ofAdd (t • Pi.single j (1 : ℝ)))
  simp only [chiHom_apply, hto, freqDot_smul_single] at hc
  exact hc

/-- **Uniqueness of trigonometric-polynomial coefficients.** A vanishing finite combination of the
distinct characters has all coefficients zero (Dedekind's independence of characters).
@isnad1 id=eq.2h4v.s6.4f763da46cd2 from=translated src=- shape=b8c045de vocab=db515de4
-/
theorem expSum_coeff_zero_of_eval_zero {s : Finset (Fin k → ℝ)} {c : (Fin k → ℝ) → ℂ}
    (h : ∀ x, ∑ ω ∈ s, c ω * Complex.exp (Complex.I * (freqDot ω x : ℂ)) = 0) :
    ∀ ω ∈ s, c ω = 0 := by
  have hli : LinearIndependent ℂ (fun ω : Fin k → ℝ => ⇑(chiHom ω)) :=
    (linearIndependent_monoidHom (Multiplicative (Fin k → ℝ)) ℂ).comp chiHom chiHom_injective
  apply linearIndependent_iff'.mp hli s c
  funext y
  simp_all

/-- Two trigonometric polynomials with the same values have the same canonical coefficients.
@isnad1 id=eq.1h4v.s5.f3a8038b63b1 from=translated src=- shape=805276fc vocab=4ce1ac1b
-/
theorem TrigPolynomial.coeffAt_eq_of_eval_eq {f g : TrigPolynomial k}
    (h : ∀ x, f.eval x = g.eval x) (ω : Fin k → ℝ) : f.coeffAt ω = g.coeffAt ω := by
  have hzero : ∀ x, ∑ ν ∈ f.freqs ∪ g.freqs,
      (f.coeffAt ν - g.coeffAt ν) * Complex.exp (Complex.I * (freqDot ν x : ℂ)) = 0 := by
    intro x
    have hf : f.eval x
        = ∑ ν ∈ f.freqs ∪ g.freqs,
            f.coeffAt ν * Complex.exp (Complex.I * (freqDot ν x : ℂ)) := by
      rw [TrigPolynomial.eval, ← Finset.sum_subset Finset.subset_union_left
            (fun ν _ hν => by rw [TrigPolynomial.coeffAt, ite_eq_right hν, zero_mul])]
      exact Finset.sum_congr rfl (fun ν hν => by rw [TrigPolynomial.coeffAt, ite_eq_left hν])
    have hg : g.eval x
        = ∑ ν ∈ f.freqs ∪ g.freqs,
            g.coeffAt ν * Complex.exp (Complex.I * (freqDot ν x : ℂ)) := by
      rw [TrigPolynomial.eval, ← Finset.sum_subset Finset.subset_union_right
            (fun ν _ hν => by rw [TrigPolynomial.coeffAt, ite_eq_right hν, zero_mul])]
      exact Finset.sum_congr rfl (fun ν hν => by rw [TrigPolynomial.coeffAt, ite_eq_left hν])
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, ← hf, ← hg, h x, sub_self]
  by_cases hω : ω ∈ f.freqs ∪ g.freqs
  · exact sub_eq_zero.mp
      (expSum_coeff_zero_of_eval_zero (c := fun ν => f.coeffAt ν - g.coeffAt ν) hzero ω hω)
  · rw [TrigPolynomial.coeffAt, TrigPolynomial.coeffAt,
        ite_eq_right (fun hf => hω (Finset.mem_union_left _ hf)),
        ite_eq_right (fun hg => hω (Finset.mem_union_right _ hg))]

/-- The canonical coefficient of a conjugated trigonometric polynomial negates the frequency and
conjugates.
@isnad1 id=eq.0h3v.s6.77670fbc93a3 from=translated src=- shape=d274ff81 vocab=dbf9d8be
-/
theorem TrigPolynomial.coeffAt_conj (f : TrigPolynomial k) (ω : Fin k → ℝ) :
    (f.conj).coeffAt ω = (starRingEnd ℂ) (f.coeffAt (-ω)) := by
  have hmem : ω ∈ (f.conj).freqs ↔ -ω ∈ f.freqs := by
    simp only [TrigPolynomial.conj, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; rwa [neg_neg]
    · intro h; exact ⟨-ω, h, neg_neg ω⟩
  unfold TrigPolynomial.coeffAt
  by_cases h : -ω ∈ f.freqs
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun hc => h (hmem.mp hc)), ite_eq_right h, map_zero]

/-! ### Frequency-set characterizations (for tracking which frequencies appear) -/

/--
@isnad1 id=eq.0h3v.s4.49b92736052f from=translated src=- shape=a02f1c3e vocab=142f76f5
-/
@[simp] theorem TrigPolynomial.smul_freqs (c : ℂ) (f : TrigPolynomial k) :
    (f.smul c).freqs = f.freqs := rfl

/--
@isnad1 id=eq.0h3v.s6.8c26c285eab8 from=translated src=- shape=a5b9a51e vocab=c5e6fa3c
-/
@[simp] theorem TrigPolynomial.expMul_freqs (a : Fin k → ℝ) (f : TrigPolynomial k) :
    (f.expMul a).freqs = f.freqs.image (fun ω => ω + a) := rfl

/--
@isnad1 id=eq.0h2v.s6.fdf5d88d4853 from=translated src=- shape=1a003a58 vocab=25ce5af9
-/
@[simp] theorem TrigPolynomial.conj_freqs (f : TrigPolynomial k) :
    (f.conj).freqs = f.freqs.image (fun ω => -ω) := rfl

/--
@isnad1 id=eq.0h4v.s6.6641bdf1dfcb from=translated src=- shape=8b963811 vocab=e1ed03bb
-/
@[simp] theorem TrigPolynomial.sum_freqs {ι : Type*} (s : Finset ι)
    (F : ι → TrigPolynomial k) :
    (TrigPolynomial.sum s F).freqs = s.biUnion (fun i => (F i).freqs) := rfl

/--
@isnad1 id=eq.0h3v.s7.cb17936ece81 from=translated src=- shape=0b661a23 vocab=f80f9749
-/
theorem TrigPolynomial.mul_freqs (f g : TrigPolynomial k) :
    (f.mul g).freqs = f.freqs.biUnion (fun ω => g.freqs.image (fun ν => ν + ω)) := rfl

/-! ### Embedding into more variables (for products of sums in disjoint variable blocks) -/

section Embed
variable {m n : ℕ}

/-- The pairing of left-block-supported frequencies sees only the first block.
@isnad1 id=eq.0h5v.s6.8354c6252738 from=translated src=- shape=0d5f7b4b vocab=6f8b84c9
-/
theorem freqDot_append_left (ω x : Fin m → ℝ) (y : Fin n → ℝ) :
    freqDot (Fin.append ω (0 : Fin n → ℝ)) (Fin.append x y) = freqDot ω x := by
  simp only [freqDot, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

/-- The pairing of right-block-supported frequencies sees only the second block.
@isnad1 id=eq.0h5v.s6.364f19bd133b from=translated src=- shape=0fae0dd4 vocab=6f8b84c9
-/
theorem freqDot_append_right (ω : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    freqDot (Fin.append (0 : Fin m → ℝ) ω) (Fin.append x y) = freqDot ω y := by
  simp only [freqDot, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]

/-- Embed an `m`-variable trigonometric polynomial into `m + n` variables on the first block. -/
noncomputable def TrigPolynomial.embedL (f : TrigPolynomial m) : TrigPolynomial (m + n) where
  freqs := f.freqs.image (fun ω => Fin.append ω (0 : Fin n → ℝ))
  coeff := fun σ => f.coeff (fun i => σ (Fin.castAdd n i))

/-- Embed an `n`-variable trigonometric polynomial into `m + n` variables on the second block. -/
noncomputable def TrigPolynomial.embedR (f : TrigPolynomial n) : TrigPolynomial (m + n) where
  freqs := f.freqs.image (fun ω => Fin.append (0 : Fin m → ℝ) ω)
  coeff := fun σ => f.coeff (fun i => σ (Fin.natAdd m i))

/--
@isnad1 id=eq.0h5v.s5.587653ae91e4 from=translated src=- shape=0ed95fe6 vocab=405627a2
-/
theorem TrigPolynomial.eval_embedL (f : TrigPolynomial m) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (f.embedL (n := n)).eval (Fin.append x y) = f.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.embedL]
  rw [Finset.sum_image (by
    intro p _ q _ hpq; funext i
    have := congrFun hpq (Fin.castAdd n i); simpa [Fin.append_left] using this)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [freqDot_append_left]
  simp_all

/--
@isnad1 id=eq.0h5v.s5.583742bae9a2 from=translated src=- shape=4bca05a3 vocab=300c6ea8
-/
theorem TrigPolynomial.eval_embedR (f : TrigPolynomial n) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (f.embedR (m := m)).eval (Fin.append x y) = f.eval y := by
  simp only [TrigPolynomial.eval, TrigPolynomial.embedR]
  rw [Finset.sum_image (by
    intro p _ q _ hpq; funext i
    have := congrFun hpq (Fin.natAdd m i); simpa [Fin.append_right] using this)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [freqDot_append_right]
  simp_all

/--
@isnad1 id=eq.0h3v.s7.57600323ec8f from=translated src=- shape=72d4effd vocab=8af63a3c
-/
@[simp] theorem TrigPolynomial.embedL_freqs (f : TrigPolynomial m) :
    (f.embedL (n := n)).freqs = f.freqs.image (fun ω => Fin.append ω (0 : Fin n → ℝ)) := rfl

/--
@isnad1 id=eq.0h3v.s7.fcb05f21d8fc from=translated src=- shape=48289c00 vocab=bc53a89c
-/
@[simp] theorem TrigPolynomial.embedR_freqs (f : TrigPolynomial n) :
    (f.embedR (m := m)).freqs = f.freqs.image (fun ω => Fin.append (0 : Fin m → ℝ) ω) := rfl

end Embed

/-! ### One-variable parameter-shift identity -/

noncomputable section

/-- **Parameter-shift identity.** The derivative of `a + b cos θ + c sin θ`
equals the symmetric `π/2`-shifted finite difference `(C(θ+π/2) - C(θ-π/2))/2`.
@isnad1 id=eq.0h4v.s8.0e3540338fff from=translated src=- shape=88a88c0f vocab=d1de5f41
-/
theorem trig_parameter_shift (a b c θ : ℝ) :
    deriv (fun t => a + b * Real.cos t + c * Real.sin t) θ
      = ((a + b * Real.cos (θ + Real.pi / 2) + c * Real.sin (θ + Real.pi / 2))
          - (a + b * Real.cos (θ - Real.pi / 2) + c * Real.sin (θ - Real.pi / 2))) / 2 := by
  have hd : deriv (fun t => a + b * Real.cos t + c * Real.sin t) θ
      = -(b * Real.sin θ) + c * Real.cos θ := by
    simp_all
  rw [hd, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

end

end QuantumAlg
