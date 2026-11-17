import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_entire_log` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_entire_log_normalized` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_entire_log_with_val_at` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.HolomorphicLog

# Holomorphic logarithms of nowhere-vanishing entire functions

If `f : ℂ → ℂ` is entire and never zero, then `f = exp ∘ g` for some entire `g`.

Mathlib has `Complex.exists_continuousOn_eqOn_exp_comp`
(`Mathlib/Analysis/Complex/BranchLogRoot.lean`), which produces a *continuous* branch of
the logarithm on a simply connected open set. That is not enough for us: the Hadamard
factorization argument needs the branch to be *holomorphic*. This file supplies the
holomorphic upgrade on all of `ℂ` by the classical route:

1. `deriv f / f` is entire (`differentiable_logDeriv`).
2. Every entire function has an entire primitive. This is Mathlib's Morera-based
   `Differentiable.isExactOn_univ` (`Mathlib/Analysis/Complex/HasPrimitives.lean`),
   repackaged here as `exists_entire_primitive`.
3. If `G' = f'/f` then `(f · exp (-G))' = 0`, so `f · exp (-G)` is a nonzero constant `c`
   (`is_const_of_deriv_eq_zero`), and `g := G + log c` works.

## Main results

* `XiLab.exists_entire_log` : the existence statement.
* `XiLab.exists_entire_log_normalized` : the same with `g 0 = Complex.log (f 0)`.
* `XiLab.exists_entire_log_with_val_at` : a branch prescribed at an arbitrary base point.
-/

namespace XiLab

open Complex Set

/-- The logarithmic derivative of a nowhere-vanishing entire function is entire.
@isnad1 id=differen.2h1v.s7.70483d38463f from=translated src=- shape=c852af3e vocab=6eb1c82f
-/
theorem differentiable_logDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnz : ∀ z, f z ≠ 0) :
    Differentiable ℂ fun z => deriv f z / f z :=
  fun z => (hf.deriv z).div (hf z) (hnz z)

/-- **Every entire function has an entire primitive.**

This is Mathlib's `Differentiable.isExactOn_univ` (Morera on `ℂ`, from
`Mathlib/Analysis/Complex/HasPrimitives.lean`) restated in the `HasDerivAt`-everywhere
form that the rest of this file uses.
@isnad1 id=ex.1h1v.s7.8ba9d7e5d517 from=translated src=- shape=64099442 vocab=949f966c
-/
theorem exists_entire_primitive {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, HasDerivAt H (h z) z := by
  obtain ⟨H, hH⟩ := hh.isExactOn_univ
  have hH' : ∀ z, HasDerivAt H (h z) z := fun z => hH z (mem_univ z)
  exact ⟨H, fun z => (hH' z).differentiableAt, hH'⟩

/-- Auxiliary step: if `G` is a primitive of the logarithmic derivative of a
nowhere-vanishing entire `f`, then `f · exp (-G)` is constant.
@isnad1 id=eq.3h4v.s7.9516bec66f8f from=translated src=- shape=d2a93a7d vocab=639f7298
-/
theorem const_mul_exp_neg_primitive {f G : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∀ z, f z ≠ 0) (hG : ∀ z, HasDerivAt G (deriv f z / f z) z) (z w : ℂ) :
    f z * Complex.exp (-G z) = f w * Complex.exp (-G w) := by
  have key : ∀ x : ℂ, HasDerivAt (fun y => f y * Complex.exp (-G y)) 0 x := by
    intro x
    have h1 : HasDerivAt f (deriv f x) x := (hf x).hasDerivAt
    have h2 : HasDerivAt (fun y => Complex.exp (-G y))
        (Complex.exp (-G x) * -(deriv f x / f x)) x := ((hG x).neg).cexp
    have h3 := h1.mul h2
    have h4 : deriv f x * Complex.exp (-G x)
        + f x * (Complex.exp (-G x) * -(deriv f x / f x)) = 0 := by
      have hx := hnz x
      field_simp
      ring
    rwa [h4] at h3
  exact is_const_of_deriv_eq_zero (fun x => (key x).differentiableAt)
    (fun x => (key x).deriv) z w

/-- **Holomorphic logarithm.** A nowhere-vanishing entire function on `ℂ` is the
exponential of an entire function.
@isnad1 id=ex.2h1v.s7.19ada60ee86c from=translated src=- shape=a08e02d7 vocab=0225faae
-/
theorem exists_entire_log {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnz : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  obtain ⟨G, hGd, hG⟩ := exists_entire_primitive (differentiable_logDeriv hf hnz)
  have hc : f 0 * Complex.exp (-G 0) ≠ 0 := mul_ne_zero (hnz 0) (Complex.exp_ne_zero _)
  refine ⟨fun z => G z + Complex.log (f 0 * Complex.exp (-G 0)), hGd.add_const _, fun z => ?_⟩
  rw [Complex.exp_add, Complex.exp_log hc,
    ← const_mul_exp_neg_primitive hf hnz hG z 0, mul_comm, mul_assoc, ← Complex.exp_add]
  simp

/-- **Holomorphic logarithm, normalized at `0`.** The branch can be chosen so that
`g 0 = Complex.log (f 0)`; in particular `Complex.exp (g 0) = f 0`.
@isnad1 id=ex.2h1v.s7.04cc45e64deb from=translated src=- shape=2fc493d7 vocab=b086b9ed
-/
theorem exists_entire_log_normalized {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = Complex.log (f 0) ∧
      ∀ z, f z = Complex.exp (g z) := by
  obtain ⟨g₀, hg₀d, hg₀⟩ := exists_entire_log hf hnz
  refine ⟨fun z => g₀ z - g₀ 0 + Complex.log (f 0), by fun_prop, by simp, fun z => ?_⟩
  have h0 := hnz 0
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log h0, ← hg₀ z, ← hg₀ 0]
  field_simp

/-- The normalization at `0` in the form asked for by the consumer: `exp (g 0) = f 0`.
@isnad1 id=ex.2h1v.s7.9f6ad902aa31 from=translated src=- shape=561eb25c vocab=0225faae
-/
theorem exists_entire_log_exp_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ Complex.exp (g 0) = f 0 ∧
      ∀ z, f z = Complex.exp (g z) := by
  obtain ⟨g, hgd, hg⟩ := exists_entire_log hf hnz
  exact ⟨g, hgd, (hg 0).symm, hg⟩

/-- **Holomorphic logarithm with a prescribed value at an arbitrary base point.**
Given any `w` with `Complex.exp w = f z₀`, there is an entire branch `g` of `log ∘ f`
with `g z₀ = w`.
@isnad1 id=ex.3h3v.s7.882b498f679b from=translated src=- shape=63818681 vocab=0225faae
-/
theorem exists_entire_log_with_val_at {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∀ z, f z ≠ 0) (z₀ w : ℂ) (hw : Complex.exp w = f z₀) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g z₀ = w ∧ ∀ z, f z = Complex.exp (g z) := by
  obtain ⟨g₀, hg₀d, hg₀⟩ := exists_entire_log hf hnz
  refine ⟨fun z => g₀ z - g₀ z₀ + w, by fun_prop, by simp, fun z => ?_⟩
  have h0 := hnz z₀
  rw [Complex.exp_add, Complex.exp_sub, hw, ← hg₀ z, ← hg₀ z₀]
  field_simp

end XiLab
