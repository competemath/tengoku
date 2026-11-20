/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate partial derivatives on `Fin n → ℝ`

This file sets up the single primitive on which all of `GRLab` rests: the coordinate
partial derivative

  `∂_b F (x)  :=  (d/dt) F(x¹,…,t,…,xⁿ) |_{t = x^b}`

realised as a one–dimensional `deriv` along the `b`-th coordinate line through `x`,
where the coordinate line is produced by `Function.update`.

## Fidelity note

`GRLab.pderiv b F x = deriv (fun t => F (Function.update x b t)) (x b)`.

This is *literally* the textbook definition `∂F/∂x^b` — the derivative of the
one-variable function obtained by freezing every coordinate except the `b`-th.  It is
total: when the section is not differentiable at `x b`, Mathlib's `deriv` junk value `0`
is returned, exactly as for `deriv` itself.  `pderiv_eq_fderiv` below records the bridge
to Mathlib's Fréchet derivative: for `f` differentiable at `x` in the total sense,
`pderiv b f x = fderiv ℝ f x (Pi.single b 1)`, i.e. the partial derivative is the
directional derivative along the `b`-th basis vector.

Working with `deriv` of a one-variable section rather than with `fderiv` is a deliberate
choice: it makes every curvature computation a *one-variable* calculus problem, for which
Mathlib's `HasDerivAt` combinator API is complete and fast.
-/

namespace GRLab

open Function Filter Topology

variable {n : ℕ}

/-- The coordinate line through `x` in the `b`-th direction.-/
noncomputable def coordLine (x : Fin n → ℝ) (b : Fin n) (t : ℝ) : Fin n → ℝ :=
  Function.update x b t

/--
@isnad1 id=eq.0h4v.s4.40849d88d780 from=translated src=- shape=24e4705d vocab=0802e6bd
-/
@[simp] lemma coordLine_same (x : Fin n → ℝ) (b : Fin n) (t : ℝ) :
    coordLine x b t b = t := by
  simp [coordLine]

/--
@isnad1 id=eq.1h5v.s5.58a58152f604 from=translated src=- shape=44363b9d vocab=0802e6bd
-/
@[simp] lemma coordLine_of_ne {x : Fin n → ℝ} {b c : Fin n} (h : c ≠ b) (t : ℝ) :
    coordLine x b t c = x c := by
  simp [coordLine, Function.update_of_ne h]

/--
@isnad1 id=eq.0h3v.s4.b788a3a0f1b8 from=translated src=- shape=0b47a3e0 vocab=0802e6bd
-/
@[simp] lemma coordLine_self (x : Fin n → ℝ) (b : Fin n) :
    coordLine x b (x b) = x := by
  simp [coordLine]

/-- **The coordinate partial derivative.**  `pderiv b F x` is `∂F/∂x^b` evaluated at `x`.-/
noncomputable def pderiv (b : Fin n) (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t : ℝ => F (coordLine x b t)) (x b)

/--
@isnad1 id=eq.0h4v.s6.73c1dd1e8658 from=translated src=- shape=06dbb838 vocab=df96a1b6
-/
lemma pderiv_def (b : Fin n) (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    pderiv b F x = deriv (fun t : ℝ => F (Function.update x b t)) (x b) := rfl

/-! ### Evaluation lemmas

The workhorse is `pderiv_eq_of_hasDerivAt`: to evaluate `∂_b F` at `x` it suffices to
exhibit a one-variable function `φ` that agrees with the section of `F` *near* `x b`,
together with a `HasDerivAt` fact for `φ`.  The "near" is essential — curvature
computations are only valid on the open set where the metric is nondegenerate.
-/

/-- If the `b`-section of `F` through `x` agrees with `φ` near `x b`, the partial
derivative of `F` is the derivative of `φ`.
@isnad1 id=eq.1h5v.s6.8ae6dc2eb07c from=translated src=- shape=9ea2bbb0 vocab=806f4da9
-/
lemma pderiv_eq_deriv_of_eventuallyEq {b : Fin n} {F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {φ : ℝ → ℝ} (h : ∀ᶠ t in 𝓝 (x b), F (coordLine x b t) = φ t) :
    pderiv b F x = deriv φ (x b) :=
  Filter.EventuallyEq.deriv_eq h

/-- The main evaluation rule: agreement near the point plus a `HasDerivAt` witness.
@isnad1 id=eq.2h6v.s6.12100f60bcc1 from=translated src=- shape=d00a2077 vocab=b9708090
-/
lemma pderiv_eq_of_hasDerivAt {b : Fin n} {F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {φ : ℝ → ℝ} {c : ℝ} (h : ∀ᶠ t in 𝓝 (x b), F (coordLine x b t) = φ t)
    (hd : HasDerivAt φ c (x b)) : pderiv b F x = c := by
  rw [pderiv_eq_deriv_of_eventuallyEq h, hd.deriv]

/-- Global version of `pderiv_eq_of_hasDerivAt`.
@isnad1 id=eq.2h6v.s6.58d0ea3a8943 from=translated src=- shape=d5945bde vocab=a37722aa
-/
lemma pderiv_eq_of_hasDerivAt' {b : Fin n} {F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {φ : ℝ → ℝ} {c : ℝ} (h : ∀ t, F (coordLine x b t) = φ t)
    (hd : HasDerivAt φ c (x b)) : pderiv b F x = c :=
  pderiv_eq_of_hasDerivAt (Filter.Eventually.of_forall h) hd

/-- Two functions agreeing on a neighbourhood of `x` have the same partials at `x`.
(The neighbourhood is taken in `Fin n → ℝ`; agreement along the coordinate line
suffices, which is what `pderiv_eq_deriv_of_eventuallyEq` provides.)
@isnad1 id=eq.1h5v.s6.d44b31a537f6 from=translated src=- shape=b2530fc7 vocab=1aa5af1b
-/
lemma pderiv_congr {b : Fin n} {F G : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : ∀ᶠ t in 𝓝 (x b), F (coordLine x b t) = G (coordLine x b t)) :
    pderiv b F x = pderiv b G x :=
  Filter.EventuallyEq.deriv_eq h

/-! ### Structural lemmas -/

/--
@isnad1 id=eq.0h4v.s4.43ee5ed2d9f9 from=translated src=- shape=6f551b01 vocab=38d16194
-/
@[simp] lemma pderiv_const (b : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    pderiv b (fun _ => c) x = 0 := deriv_const _ _

/-- A function of a *single* coordinate `c ≠ b` has vanishing `b`-partial.
@isnad1 id=eq.1h5v.s5.d4dd587bc7ea from=translated src=- shape=44a2bf22 vocab=38d16194
-/
lemma pderiv_of_ne {b c : Fin n} (h : c ≠ b) (φ : ℝ → ℝ) (x : Fin n → ℝ) :
    pderiv b (fun y => φ (y c)) x = 0 := by
  have hfun : (fun t : ℝ => φ (coordLine x b t c)) = fun _ : ℝ => φ (x c) := by
    funext t; rw [coordLine_of_ne h]
  show deriv (fun t : ℝ => φ (coordLine x b t c)) (x b) = 0
  rw [hfun, deriv_const]

/-- The `b`-partial of the `c`-th coordinate function.
@isnad1 id=eq.0h4v.s5.682a6ff84c65 from=translated src=- shape=b27941f2 vocab=10176c55
-/
lemma pderiv_coord (b c : Fin n) (x : Fin n → ℝ) :
    pderiv b (fun y => y c) x = if c = b then 1 else 0 := by
  by_cases h : c = b
  · subst h
    show deriv (fun t : ℝ => coordLine x c t c) (x c) = _
    simp only [coordLine_same]
    simp
  · rw [ite_eq_right h]
    exact pderiv_of_ne h id x

/--
@isnad1 id=eq.2h5v.s7.d81f45558faf from=translated src=- shape=8ff33033 vocab=c4396709
-/
lemma pderiv_add {b : Fin n} {F G : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hF : DifferentiableAt ℝ (fun t : ℝ => F (coordLine x b t)) (x b))
    (hG : DifferentiableAt ℝ (fun t : ℝ => G (coordLine x b t)) (x b)) :
    pderiv b (fun y => F y + G y) x = pderiv b F x + pderiv b G x :=
  deriv_add hF hG

/--
@isnad1 id=eq.2h5v.s7.55adcfdd74d6 from=translated src=- shape=8ff33033 vocab=f9e7e2c7
-/
lemma pderiv_sub {b : Fin n} {F G : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hF : DifferentiableAt ℝ (fun t : ℝ => F (coordLine x b t)) (x b))
    (hG : DifferentiableAt ℝ (fun t : ℝ => G (coordLine x b t)) (x b)) :
    pderiv b (fun y => F y - G y) x = pderiv b F x - pderiv b G x :=
  deriv_sub hF hG

/--
@isnad1 id=eq.1h5v.s6.4e1e9c6a4722 from=translated src=- shape=9aa5aab0 vocab=ab8fc5b9
-/
lemma pderiv_const_mul {b : Fin n} {F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (c : ℝ)
    (hF : DifferentiableAt ℝ (fun t : ℝ => F (coordLine x b t)) (x b)) :
    pderiv b (fun y => c * F y) x = c * pderiv b F x :=
  deriv_const_mul c hF

/-- Partial derivative of a finite sum.
@isnad1 id=eq.1h6v.s7.3203692606bb from=translated src=- shape=6678c652 vocab=a0c5e331
-/
lemma pderiv_finset_sum {ι : Type*} {b : Fin n} {s : Finset ι}
    {F : ι → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun t : ℝ => F i (coordLine x b t)) (x b)) :
    pderiv b (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, pderiv b (F i) x := by
  show deriv (fun t : ℝ => ∑ i ∈ s, F i (coordLine x b t)) (x b) = _
  have hfun : (fun t : ℝ => ∑ i ∈ s, F i (coordLine x b t))
      = ∑ i ∈ s, fun t : ℝ => F i (coordLine x b t) := by
    funext t; simp
  rw [hfun, deriv_sum h]
  rfl

/-! ### Bridge to Mathlib's Fréchet derivative -/

/--
@isnad1 id=eq.0h4v.s6.159c671d17dc from=translated src=- shape=d9336401 vocab=756c8ea7
-/
lemma coordLine_eq_add_smul (x : Fin n → ℝ) (b : Fin n) (t : ℝ) :
    coordLine x b t = x + (t - x b) • (Pi.single b (1 : ℝ)) := by
  funext j
  by_cases h : j = b
  · subst h; simp [coordLine]
  · simp [coordLine, h]

/--
@isnad1 id=hasderiv.0h3v.s6.4f08f25110d4 from=translated src=- shape=ed8be73b vocab=73f17e77
-/
lemma hasDerivAt_coordLine (x : Fin n → ℝ) (b : Fin n) :
    HasDerivAt (fun t : ℝ => coordLine x b t) (Pi.single b (1 : ℝ)) (x b) := by
  have h : HasDerivAt (fun t : ℝ => x + (t - x b) • (Pi.single b (1 : ℝ)))
      (Pi.single b (1 : ℝ)) (x b) := by
    simpa using (((hasDerivAt_id (x b)).sub_const (x b)).smul_const
      (Pi.single b (1 : ℝ))).const_add x
  simpa only [coordLine_eq_add_smul] using h

/-- **Fidelity bridge.**  For a function Fréchet-differentiable at `x`, the coordinate
partial derivative is the directional derivative along the `b`-th basis vector.
@isnad1 id=eq.1h4v.s9.019d9181ceef from=translated src=- shape=48a9b795 vocab=d4460024
-/
theorem pderiv_eq_fderiv {b : Fin n} {F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hF : DifferentiableAt ℝ F x) :
    pderiv b F x = fderiv ℝ F x (Pi.single b (1 : ℝ)) := by
  have hF' : HasFDerivAt F (fderiv ℝ F x) (coordLine x b (x b)) := by
    rw [coordLine_self]; exact hF.hasFDerivAt
  have h := hF'.comp_hasDerivAt (x b) (hasDerivAt_coordLine x b)
  simpa [Function.comp_def, pderiv] using h.deriv

end GRLab
