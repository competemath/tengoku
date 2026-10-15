/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. The residue functional `resAt` and its algebra.
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.ResidueCalculus.LaurentCoeff
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.ResidueCalculus.PrincipalPart

/-!
# The residue functional (residue-calculus)

`RS.resAt f z₀` is the `(-1)`-st Laurent coefficient of `f` at `z₀` — the residue. Purely
algebraic here; the circle-integral characterization is
`RS.circleIntegral_eq_two_pi_I_mul_resAt` (`IntegralBridge.lean`).

Main exports:
* Inherited ℂ-linear algebra: `RS.resAt_congr`, `RS.resAt_add`/`_fun_add`/`_const_mul`/`_neg`/
  `_sub`/`_fun_sum`;
* `RS.resAt_of_analyticAt`, `RS.resAt_of_order_nonneg` — vanishing off the pole locus;
* `RS.resAt_zpow_monomial`, `RS.resAt_sub_inv` — monomial residues;
* `RS.MeromorphicAt.resAt_deriv` — the residue of a derivative vanishes;
* `RS.MeromorphicAt.resAt_deriv_div` — the log-derivative residue is the order (argument
  principle atom);
* `RS.resAt_tail_mul`, `RS.resAt_analyticAt_mul`, `RS.resAt_mul` — Serre-pairing atoms
  (Miranda VI.3 `Res_ω` shape `Σ c_n a_{−1−n}`).
-/

@[expose] public section

open Filter Topology Metric Function

namespace RS

variable {f g h : ℂ → ℂ} {z₀ : ℂ} {k n : ℤ}

/-- The residue of `f` at `z₀`: the `(-1)`-st Laurent coefficient. Purely algebraic; the
circle-integral characterization is `RS.circleIntegral_eq_two_pi_I_mul_resAt`. -/
noncomputable def resAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := laurentCoeffAt f z₀ (-1)

/--
@isnad1 id=eq.1h3v.s5.04d1c292e1f0 from=translated src=- shape=cba91e06 vocab=f7ded845
-/
theorem resAt_congr (hfg : f =ᶠ[𝓝[≠] z₀] g) : resAt f z₀ = resAt g z₀ :=
  laurentCoeffAt_congr hfg (-1)

/--
@isnad1 id=eq.2h3v.s6.22065909f6e1 from=translated src=- shape=5e3340b7 vocab=9170bed4
-/
theorem resAt_fun_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    resAt (fun z => f z + g z) z₀ = resAt f z₀ + resAt g z₀ :=
  laurentCoeffAt_fun_add hf hg (-1)

/--
@isnad1 id=eq.2h3v.s6.8ca5f6940d03 from=translated src=- shape=ec16d441 vocab=9170bed4
-/
theorem resAt_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    resAt (f + g) z₀ = resAt f z₀ + resAt g z₀ :=
  laurentCoeffAt_add hf hg (-1)

/--
@isnad1 id=eq.0h3v.s5.83be69f80f51 from=translated src=- shape=96d2f203 vocab=fcbccfa0
-/
theorem resAt_const_mul (c : ℂ) : resAt (fun z => c * f z) z₀ = c * resAt f z₀ :=
  laurentCoeffAt_const_mul c (-1)

/--
@isnad1 id=eq.0h2v.s4.76bd7cfcb518 from=translated src=- shape=1b3ec09f vocab=e56c9872
-/
theorem resAt_neg : resAt (fun z => -f z) z₀ = -resAt f z₀ :=
  laurentCoeffAt_neg (-1)

/--
@isnad1 id=eq.2h3v.s6.83dc5476a317 from=translated src=- shape=5e3340b7 vocab=bdc37b76
-/
theorem resAt_sub (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    resAt (fun z => f z - g z) z₀ = resAt f z₀ - resAt g z₀ :=
  laurentCoeffAt_sub hf hg (-1)

/--
@isnad1 id=eq.1h4v.s6.1f5d13c07e27 from=translated src=- shape=60f0fa9b vocab=93c1a1e4
-/
theorem resAt_fun_sum {ι : Type*} {s : Finset ι} {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ s, MeromorphicAt (F i) z₀) :
    resAt (fun z => ∑ i ∈ s, F i z) z₀ = ∑ i ∈ s, resAt (F i) z₀ :=
  laurentCoeffAt_fun_sum hF (-1)

/--
@isnad1 id=eq.0h1v.s4.df248d550e3b from=translated src=- shape=20ee5c8f vocab=2b824e75
-/
theorem resAt_zero_fun : resAt (fun _ => (0 : ℂ)) z₀ = 0 :=
  laurentCoeffAt_zero_fun (-1)

/--
@isnad1 id=eq.1h2v.s5.ab2a2ed7a2de from=translated src=- shape=64e000da vocab=0780a67c
-/
@[simp] theorem resAt_of_analyticAt (hf : AnalyticAt ℂ f z₀) : resAt f z₀ = 0 := by
  rw [resAt, laurentCoeffAt_of_analyticAt hf]
  norm_num

/--
@isnad1 id=eq.1h2v.s6.97d91d24b73a from=translated src=- shape=547e9d9a vocab=2a62514d
-/
theorem resAt_of_order_nonneg (h : 0 ≤ meromorphicOrderAt f z₀) : resAt f z₀ = 0 := by
  apply laurentCoeffAt_eq_zero_of_lt_order
  calc ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : (-1:ℤ) < 0)
    _ ≤ meromorphicOrderAt f z₀ := by exact_mod_cast h

/--
@isnad1 id=eq.0h2v.s6.926c5148ce2c from=translated src=- shape=ba87e668 vocab=0a21a401
-/
@[simp] theorem resAt_zpow_monomial (m : ℤ) :
    resAt (fun z => (z - z₀) ^ m) z₀ = if m = -1 then 1 else 0 := by
  change laurentCoeffAt (fun z => (z - z₀) ^ m) z₀ (-1) = _
  rw [laurentCoeffAt_zpow_monomial]
  split_ifs <;> first | rfl | omega

/--
@isnad1 id=eq.0h1v.s4.24aefea90715 from=translated src=- shape=2de97c6c vocab=9d120afc
-/
@[simp] theorem resAt_sub_inv : resAt (fun z => (z - z₀)⁻¹) z₀ = 1 := by
  have hfun : (fun z => (z - z₀)⁻¹) = fun z => (z - z₀) ^ (-1 : ℤ) := by
    funext z; rw [zpow_neg_one]
  rw [hfun, resAt_zpow_monomial]
  simp

/-- Derivative of a monomial factor, in closed form and UNCONDITIONALLY (no nonvanishing side
condition needed — both sides are the mathlib `deriv`/`zpow` junk values, and they agree even
at `z = z₀`). The workhorse for `resAt_deriv`.
@isnad1 id=eq.0h3v.s6.a0aac739a53f from=translated src=- shape=fe9616fb vocab=3d79ec60
-/
theorem deriv_sub_zpow (z₀ : ℂ) (m : ℤ) (z : ℂ) :
    deriv (fun w => (w - z₀) ^ m) z = (m : ℂ) * (z - z₀) ^ (m - 1) := by
  have h1 := deriv_comp_sub_const (fun v : ℂ => v ^ m) z₀ z
  rwa [deriv_zpow] at h1

/-- Residue of a derivative vanishes (Serre/Abel bookkeeping; the `k ≤ -2` engine of
change-of-variables).
@isnad1 id=eq.1h2v.s6.a25722d3966a from=translated src=- shape=8338d548 vocab=13a62d08
-/
theorem MeromorphicAt.resAt_deriv (hf : MeromorphicAt f z₀) : resAt (deriv f) z₀ = 0 := by
  obtain ⟨r, hr, _, hdecomp⟩ := MeromorphicAt.exists_principalPart_add_analyticAt hf
  have hderivEq : deriv f =ᶠ[𝓝[≠] z₀] deriv (fun z => principalPartAt f z₀ z + r z) :=
    hdecomp.nhdsNE_deriv
  have hrEventually : ∀ᶠ z in 𝓝[≠] (z₀ : ℂ), AnalyticAt ℂ r z :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hr.eventually_analyticAt
  have hsplit : deriv (fun z => principalPartAt f z₀ z + r z)
      =ᶠ[𝓝[≠] z₀] fun z => deriv (principalPartAt f z₀) z + deriv r z := by
    filter_upwards [self_mem_nhdsWithin, hrEventually] with z hzne hzan
    exact deriv_fun_add ((analyticOnNhd_principalPartAt z hzne).differentiableAt)
      hzan.differentiableAt
  have hPderiv : ∀ z, z ≠ z₀ →
      deriv (principalPartAt f z₀) z
        = ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
            laurentCoeffAt f z₀ k * ((k : ℂ) * (z - z₀) ^ (k - 1)) := by
    intro z hz
    change deriv (fun z => ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
        laurentCoeffAt f z₀ k * (z - z₀) ^ k) z = _
    rw [deriv_fun_sum (fun k _ => by
      have hzne : z - z₀ ≠ 0 := sub_ne_zero.2 hz
      have hzpow : DifferentiableAt ℂ (fun z => (z - z₀) ^ k) z :=
        (show DifferentiableAt ℂ (fun w : ℂ => w - z₀) z by fun_prop).zpow (Or.inl hzne)
      exact (differentiableAt_const _).mul hzpow)]
    exact Finset.sum_congr rfl fun k _ => by rw [deriv_const_mul_field, deriv_sub_zpow]
  have hPdEq : deriv (principalPartAt f z₀) =ᶠ[𝓝[≠] z₀]
      fun z => ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
        laurentCoeffAt f z₀ k * ((k : ℂ) * (z - z₀) ^ (k - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with z hzne using hPderiv z hzne
  have hfinal : deriv f =ᶠ[𝓝[≠] z₀]
      fun z => (∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
          laurentCoeffAt f z₀ k * ((k : ℂ) * (z - z₀) ^ (k - 1))) + deriv r z :=
    hderivEq.trans (hsplit.trans (hPdEq.add (Filter.EventuallyEq.rfl)))
  rw [resAt_congr hfinal, resAt_fun_add (MeromorphicAt.fun_sum fun k _ => by fun_prop)
    (hr.deriv.meromorphicAt), resAt_of_analyticAt hr.deriv, add_zero,
    resAt_fun_sum (fun k _ => by fun_prop)]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_Icc] at hk
  rw [resAt_const_mul, resAt_const_mul, resAt_zpow_monomial, ite_eq_right (by omega : k - 1 ≠ -1)]
  ring

/-- Log-derivative residue = order (THE argument-principle atom; meromorphic-trace input).
Junk-robust: no order hypothesis (order `⊤` gives `0 = untop₀ ⊤`).
@isnad1 id=eq.1h2v.s6.f428a28a6d34 from=translated src=- shape=a757b6fd vocab=6e689433
-/
theorem MeromorphicAt.resAt_deriv_div (hf : MeromorphicAt f z₀) :
    resAt (fun z => deriv f z / f z) z₀ = ((meromorphicOrderAt f z₀).untop₀ : ℂ) := by
  by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
  · have hf0 : f =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) := meromorphicOrderAt_eq_top_iff.1 h₂
    have hderiv0 : deriv f =ᶠ[𝓝[≠] z₀] deriv (fun _ : ℂ => (0 : ℂ)) := hf0.nhdsNE_deriv
    have hcongr : (fun z => deriv f z / f z) =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) := by
      filter_upwards [hderiv0, hf0] with z hz1 hz2
      rw [hz1, hz2]; simp
    rw [resAt_congr hcongr, resAt_zero_fun, h₂, WithTop.untop₀_top]
    norm_num
  · obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h₂
    simp only [smul_eq_mul] at h₃u
    set m := (meromorphicOrderAt f z₀).untop₀ with hm
    have huEventually : ∀ᶠ z in 𝓝[≠] (z₀ : ℂ), u z ≠ 0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (h₁u.continuousAt.eventually_ne h₂u)
    have huDiffEventually : ∀ᶠ z in 𝓝[≠] (z₀ : ℂ), DifferentiableAt ℂ u z :=
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds h₁u.eventually_analyticAt).mono
        fun z hz => hz.differentiableAt
    have hderivEq : deriv f =ᶠ[𝓝[≠] z₀] deriv (fun z => (z - z₀) ^ m * u z) := h₃u.nhdsNE_deriv
    have hquot : (fun z => deriv f z / f z) =ᶠ[𝓝[≠] z₀]
        fun z => (m : ℂ) / (z - z₀) + deriv u z / u z := by
      filter_upwards [hderivEq, h₃u, huEventually, huDiffEventually, self_mem_nhdsWithin]
        with z hz1 hz2 hune hudiff hzne
      have hzz : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
      have hfz : (z - z₀) ^ m * u z ≠ 0 := mul_ne_zero (zpow_ne_zero m hzz) hune
      have hdiffzpow : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ m) z :=
        (show DifferentiableAt ℂ (fun w : ℂ => w - z₀) z by fun_prop).zpow (Or.inl hzz)
      have hlog : logDeriv (fun w => (w - z₀) ^ m * u w) z
          = logDeriv (fun w => (w - z₀) ^ m) z + logDeriv u z :=
        logDeriv_mul z (zpow_ne_zero m hzz) hune hdiffzpow hudiff
      have hzsub : logDeriv (fun w : ℂ => w - z₀) z = 1 / (z - z₀) := by
        rw [logDeriv_apply, deriv_sub_const, deriv_id'']
      have hpow : logDeriv (fun w => (w - z₀) ^ m) z = (m : ℂ) * logDeriv (fun w => w - z₀) z :=
        logDeriv_fun_zpow (by fun_prop) m
      rw [hz1, hz2, ← logDeriv_apply]
      rw [hlog, hpow, hzsub, mul_one_div, logDeriv_apply]
    rw [resAt_congr hquot]
    have h1 : MeromorphicAt (fun z => (m : ℂ) / (z - z₀)) z₀ := by fun_prop
    have h2 : MeromorphicAt (fun z => deriv u z / u z) z₀ :=
        h₁u.deriv.meromorphicAt.div h₁u.meromorphicAt
    rw [resAt_fun_add h1 h2]
    have hterm1 : resAt (fun z => (m : ℂ) / (z - z₀)) z₀ = (m : ℂ) := by
      have : (fun z : ℂ => (m : ℂ) / (z - z₀)) = fun z => (m : ℂ) * (z - z₀)⁻¹ := by
        funext z; rw [div_eq_mul_inv]
      rw [this, resAt_const_mul, resAt_sub_inv, mul_one]
    have hterm2 : resAt (fun z => deriv u z / u z) z₀ = 0 :=
      resAt_of_analyticAt (h₁u.deriv.div h₁u h₂u)
    rw [hterm1, hterm2, add_zero]

/-- Multiplying by `(· - z₀) ^ m` shifts the residue (special case of `laurentCoeffAt_zpow_mul`
at `k = -1`).
@isnad1 id=eq.1h3v.s6.624d542a6414 from=translated src=- shape=abaec929 vocab=1e083dfb
-/
theorem resAt_zpow_mul (hg : MeromorphicAt g z₀) (m : ℤ) :
    resAt (fun z => (z - z₀) ^ m * g z) z₀ = laurentCoeffAt g z₀ (-1 - m) :=
  laurentCoeffAt_zpow_mul hg m (-1)

/-- Serre-pairing atom, tail form (Miranda VI.3 eq. shape `Σ c_n a_{−1−n}`): residue of an
explicit Laurent tail times a meromorphic germ.
@isnad1 id=eq.1h4v.s6.922ebc8a2d7d from=translated src=- shape=68ec1379 vocab=92ec9f00
-/
theorem resAt_tail_mul {c : ℤ → ℂ} {s : Finset ℤ} (hg : MeromorphicAt g z₀) :
    resAt (fun z => (∑ k ∈ s, c k * (z - z₀) ^ k) * g z) z₀
      = ∑ k ∈ s, c k * laurentCoeffAt g z₀ (-1 - k) := by
  have hfun : (fun z => (∑ k ∈ s, c k * (z - z₀) ^ k) * g z)
      = fun z => ∑ k ∈ s, c k * ((z - z₀) ^ k * g z) := by
    funext z
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hfun, resAt_fun_sum (fun k _ => by fun_prop)]
  exact Finset.sum_congr rfl fun k _ => by rw [resAt_const_mul, resAt_zpow_mul hg k]

/-- Residue of `h · (· - z₀) ^ m` for `h` analytic: computed by a single Taylor coefficient
of `h` (both cases — `m ≤ -1` genuinely picks it out, `m ≥ 0` gives an analytic product and `0`,
uniformly via the `if`).
@isnad1 id=eq.1h3v.s7.3e1f5196320d from=translated src=- shape=4ba106e2 vocab=6f90343a
-/
theorem resAt_analyticAt_mul_zpow (hh : AnalyticAt ℂ h z₀) (m : ℤ) :
    resAt (fun z => h z * (z - z₀) ^ m) z₀
      = if 0 ≤ -1 - m then taylorCoeffAt h z₀ (-1 - m).toNat else 0 := by
  have hcomm : (fun z => h z * (z - z₀) ^ m) = fun z => (z - z₀) ^ m * h z := by
    funext z; ring
  rw [resAt, hcomm, laurentCoeffAt_zpow_mul hh.meromorphicAt, laurentCoeffAt_of_analyticAt hh]

end RS
