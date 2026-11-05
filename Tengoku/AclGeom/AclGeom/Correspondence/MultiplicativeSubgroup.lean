/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Correspondence.SubgroupConnectedPrime
import Tengoku.AclGeom.AclGeom.Correspondence.TorusCoordinates
import Tengoku.AclGeom.AclGeom.Correspondence.CurveIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Connected one-dimensional subgroups of the torus

Blueprint Lemma `subgroup-classification` (b): over an algebraically closed field `k`, a closed,
connected, one-dimensional subgroup `H ≤ Gₘ² = kˣ × kˣ` whose two projections are nonconstant is
`{(u, v) : u ^ m = v ^ n}` for nonzero integers `m, n`, and its cosets are `u ^ m = c · v ^ n`
(`mulSubgroup_classification_of_connected`).

The torus is the closed subvariety `X₀X₂ = 1 = X₁X₃` of `A⁴` through
`torusEmb : (u, v) ↦ (u, v, u⁻¹, v⁻¹)`.  The coordinate ring of `H` is
`k[X₀, …, X₃] ⧸ I(H)`, with `I(H)` the vanishing ideal of `torusEmb '' H`.  Closedness means
that its zero locus is `torusEmb '' H`; connectedness is connectedness of its prime spectrum,
and dimension one is its Krull dimension.  Closedness in `A²` would be the wrong notion: when the
characteristic is not `2`, `{u = v} ∪ {u = -v}` is disconnected in `Gₘ²` but has connected
closure in `A²`.

The proof:
1. `I(H)` is prime (`isPrime_vanishingIdeal_of_connected`, with the coordinatewise group law
   realized by scalings).
2. The plane ideal `I₂ ⊆ k[X₀, X₁]` of `H` is prime of height one: it is not maximal since `H` has
   two points, and not zero since otherwise `H` is the whole torus, whose coordinate ring has
   dimension at least two.  Its prime generator `F` is fixed up to units by scaling with points
   of `H` (`monomial_prod_eq_of_span_scale_eq`), so two distinct support monomials of `F` give a
   character relation `u ^ d₁ * v ^ d₂ = 1` on `H`.
3. In the prime `I(H)`, `M ^ n - 1` forces `M - ζ`; with the nonconstant projections this makes
   both `dᵢ` nonzero and the primitive character `u ^ a * v ^ b` (`d = g • (a, b)`) trivial on `H`.
4. The kernel of this character is the image of the cocharacter `t ↦ (t ^ b, t ^ (-a))`.  If its
   preimage of `H` were proper, closedness and clearing denominators along the curve would make it
   finite, hence `H` finite, against the nonconstant projections.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C5).
-/

namespace AclGeom

open MvPolynomial
open scoped Pointwise

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Bézout parametrization of the kernel of a primitive character.-/
private theorem eq_cochar_of_mul_eq_one {G : Type*} [CommGroup G] {a b p q : ℤ}
    (hab : a * p + b * q = 1) {u v : G} (h : u ^ a * v ^ b = 1) :
    (u ^ q * v ^ (-p)) ^ b = u ∧ (u ^ q * v ^ (-p)) ^ (-a) = v := by
  have hv : v ^ b = (u ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hu : u ^ a = (v ^ b)⁻¹ := eq_inv_of_mul_eq_one_left h
  constructor
  · calc (u ^ q * v ^ (-p)) ^ b = u ^ (q * b) * (v ^ b) ^ (-p) := by
          rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul]
          ring_nf
      _ = u ^ (a * p + b * q) := by
          rw [hv, inv_zpow', neg_neg, ← zpow_mul, ← zpow_add]
          ring_nf
      _ = u := by rw [hab, zpow_one]
  · calc (u ^ q * v ^ (-p)) ^ (-a) = (u ^ a) ^ (-q) * v ^ (p * a) := by
          rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul]
          ring_nf
      _ = v ^ (a * p + b * q) := by
          rw [hu, inv_zpow', neg_neg, ← zpow_mul, ← zpow_add]
          ring_nf
      _ = v := by rw [hab, zpow_one]

/-- **Connected one-dimensional subgroups of `Gₘ²`** (blueprint Lemma `subgroup-classification`
(b)).  Over an algebraically closed field, let `H ≤ kˣ × kˣ` be a subgroup whose image under the
standard embedding into `A⁴` is Zariski-closed, whose coordinate ring has connected prime spectrum
and Krull dimension one, and whose two projections are nonconstant.  Then
`H = {(u, v) : u ^ m = v ^ n}` for nonzero integers `m, n`, and every coset `g H` is
`{(u, v) : u ^ m = c · v ^ n}` with `c = g₁ ^ m · g₂ ^ (-n)`.
@isnad1 id=ex.4h2v.s12.90d952b23af4 from=translated src=- shape=a86f49d3 vocab=838c63f4
-/
theorem mulSubgroup_classification_of_connected (H : Subgroup (kˣ × kˣ))
    (hclosed : zeroLocus k (vanishingIdeal k (torusEmb '' (H : Set (kˣ × kˣ)))) =
      torusEmb '' (H : Set (kˣ × kˣ)))
    [ConnectedSpace (PrimeSpectrum
      (MvPolynomial (Fin 4) k ⧸ vanishingIdeal k (torusEmb '' (H : Set (kˣ × kˣ)))))]
    (hdim : ringKrullDim
      (MvPolynomial (Fin 4) k ⧸ vanishingIdeal k (torusEmb '' (H : Set (kˣ × kˣ)))) = 1)
    (hproj₁ : ∃ g ∈ H, ∃ h ∈ H, g.1 ≠ h.1) (hproj₂ : ∃ g ∈ H, ∃ h ∈ H, g.2 ≠ h.2) :
    ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ (H : Set (kˣ × kˣ)) = {g | g.1 ^ m = g.2 ^ n} ∧
      ∀ g : kˣ × kˣ, g • (H : Set (kˣ × kˣ)) =
        {x | x.1 ^ m = g.1 ^ m * (g.2 ^ n)⁻¹ * x.2 ^ n} := by
  classical
  set S : Set (Fin 4 → k) := torusEmb '' (H : Set (kˣ × kˣ)) with hS
  set J := vanishingIdeal k S with hJdef
  have hJmem : ∀ f, f ∈ J ↔ ∀ h ∈ H, aeval (torusEmb h) f = 0 := fun f ↦ by
    rw [mem_vanishingIdeal_iff]
    constructor
    · intro hf h hh
      exact hf _ ⟨h, hh, rfl⟩
    · rintro hf _ ⟨h, hh, rfl⟩
      exact hf h hh
  have hSne : ∀ c ∈ S, ∀ j, c j ≠ 0 := by
    rintro _ ⟨h, -, rfl⟩ j
    exact torusEmb_ne_zero h j
  -- Step 1: the vanishing ideal is prime.
  have hJ : J.IsPrime := by
    refine isPrime_vanishingIdeal_of_connected S hclosed ⟨torusEmb 1, 1, H.one_mem, rfl⟩
      (fun c u v ↦ u * v * c⁻¹) ?_ ?_ ?_ (fun c v ↦ scale (v * c⁻¹)) ?_
      (fun c u ↦ scale (u * c⁻¹)) ?_
    · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
      exact ⟨α * β * γ⁻¹, H.mul_mem (H.mul_mem hα hβ) (H.inv_mem hγ), by
        rw [torusEmb_mul, torusEmb_mul, torusEmb_inv]⟩
    · intro c hc u
      funext j
      simp only [Pi.mul_apply, Pi.inv_apply]
      exact mul_inv_cancel_right₀ (hSne c hc j) (u j)
    · intro c hc v
      funext j
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_comm (c j), mul_inv_cancel_right₀ (hSne c hc j)]
    · intro c v u g
      have hfun : (fun j ↦ algebraMap k k ((v * c⁻¹) j) * u j) = u * v * c⁻¹ := by
        funext j
        simp only [Algebra.algebraMap_self, RingHom.id_apply, Pi.mul_apply, Pi.inv_apply]
        ring
      rw [aeval_scale, hfun]
    · intro c u v g
      have hfun : (fun j ↦ algebraMap k k ((u * c⁻¹) j) * v j) = u * v * c⁻¹ := by
        funext j
        simp only [Algebra.algebraMap_self, RingHom.id_apply, Pi.mul_apply, Pi.inv_apply]
        ring
      rw [aeval_scale, hfun]
  -- Constant values: a power of a coordinate monomial equal to one on `H` is constant on `H`.
  have hconst : ∀ (M : MvPolynomial (Fin 4) k) {n : ℕ}, n ≠ 0 →
      (∀ h ∈ H, aeval (torusEmb h) M ^ n = 1) → ∃ ζ : k, ∀ h ∈ H, aeval (torusEmb h) M = ζ := by
    intro M n hn hM
    have hmem : M ^ n - 1 ∈ J := (hJmem _).2 fun h hh ↦ by
      rw [map_sub, map_pow, map_one, hM h hh, sub_self]
    obtain ⟨ζ, hζ⟩ := exists_sub_C_mem_of_pow_sub_one_mem hJ M hn hmem
    refine ⟨ζ, fun h hh ↦ ?_⟩
    have := (hJmem _).1 hζ h hh
    rwa [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at this
  -- A coordinate of `H` cannot satisfy `xⁿ = 1`, by the nonconstant projections.
  have hfst : ∀ {n : ℕ}, n ≠ 0 → ¬ ∀ h ∈ H, h.1 ^ n = 1 := by
    intro n hn hall
    obtain ⟨ζ, hζ⟩ := hconst (X 0) hn fun h hh ↦ by
      rw [aeval_X, torusEmb_apply_zero, ← Units.val_pow_eq_pow_val, hall h hh, Units.val_one]
    obtain ⟨g, hg, h, hh, hgh⟩ := hproj₁
    refine hgh (Units.ext ?_)
    have h1 := hζ g hg
    have h2 := hζ h hh
    rw [aeval_X, torusEmb_apply_zero] at h1 h2
    rw [h1, h2]
  have hsnd : ∀ {n : ℕ}, n ≠ 0 → ¬ ∀ h ∈ H, h.2 ^ n = 1 := by
    intro n hn hall
    obtain ⟨ζ, hζ⟩ := hconst (X 1) hn fun h hh ↦ by
      rw [aeval_X, torusEmb_apply_one, ← Units.val_pow_eq_pow_val, hall h hh, Units.val_one]
    obtain ⟨g, hg, h, hh, hgh⟩ := hproj₂
    refine hgh (Units.ext ?_)
    have h1 := hζ g hg
    have h2 := hζ h hh
    rw [aeval_X, torusEmb_apply_one] at h1 h2
    rw [h1, h2]
  -- `H` is infinite.
  have hinfinite : (H : Set (kˣ × kˣ)).Infinite := by
    intro hfin
    have : Finite H := hfin.to_subtype
    refine hfst (n := Nat.card H) Nat.card_pos.ne' fun h hh ↦ ?_
    have hpow : (⟨h, hh⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val hpow
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← Prod.pow_fst]
    exact (congrArg Prod.fst h2).trans Prod.fst_one
  -- Step 2: the plane ideal.
  let ρ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 4) k := aeval ![X 0, X 1]
  have hρ : ∀ (h : kˣ × kˣ) (q : MvPolynomial (Fin 2) k),
      aeval (torusEmb h) (ρ q) = aeval ![(h.1 : k), (h.2 : k)] q := fun h q ↦ by
    have hcomp : (aeval (torusEmb h)).comp ρ = aeval ![(h.1 : k), (h.2 : k)] := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      fin_cases i <;> simp [ρ]
    exact congrArg (fun φ : MvPolynomial (Fin 2) k →ₐ[k] k ↦ φ q) hcomp
  set I₂ := J.comap ρ with hI₂def
  have hI₂prime : I₂.IsPrime := Ideal.comap_isPrime ρ J
  have hI₂mem : ∀ q, q ∈ I₂ ↔ ∀ h ∈ H, aeval ![(h.1 : k), (h.2 : k)] q = 0 := fun q ↦ by
    rw [Ideal.mem_comap, hJmem]
    simp only [hρ]
  -- `I₂` is not maximal: `H` has two points with different first coordinates.
  have hnmax : ¬ I₂.IsMaximal := fun hmax ↦ by
    obtain ⟨x, hx⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hmax
    have hpt : ∀ h ∈ H, (h.1 : k) = x 0 := fun h hh ↦ by
      have hmem : X 0 - C (x 0) ∈ I₂ := by
        rw [hx, mem_vanishingIdeal_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        simp
      have := (hI₂mem _).1 hmem h hh
      simpa [sub_eq_zero] using this
    obtain ⟨g, hg, h, hh, hgh⟩ := hproj₁
    exact hgh (Units.ext ((hpt g hg).trans (hpt h hh).symm))
  -- `I₂` is not zero: otherwise `H` is the whole torus, of dimension at least two.
  have hbot : I₂ ≠ ⊥ := by
    intro hI₂bot
    have hall : ∀ g : kˣ × kˣ, g ∈ H := fun g ↦ by
      have hg : torusEmb g ∈ zeroLocus k J := by
        intro f hf
        obtain ⟨N, q, hq⟩ := exists_plane_clear f
        have hq0 : q ∈ I₂ := (hI₂mem q).2 fun h hh ↦ by
          rw [hq h, (hJmem f).1 hf h hh, mul_zero]
        rw [hI₂bot, Ideal.mem_bot] at hq0
        have h0 := hq g
        rw [hq0, map_zero] at h0
        have hne : ((g.1 : k) * g.2) ^ N ≠ 0 :=
          pow_ne_zero _ (mul_ne_zero g.1.ne_zero g.2.ne_zero)
        exact (mul_eq_zero.1 h0.symm).resolve_left hne
      rw [hclosed] at hg
      obtain ⟨h, hh, hgh⟩ := hg
      exact torusEmb_injective hgh ▸ hh
    -- The curve `{1} × kˣ` and the point `1`.
    let e : Fin 4 → ℤ := ![0, 1, 0, -1]
    have hcurve : ∀ t : kˣ, torusEmb ((1 : kˣ), t) = fun j ↦ ((t ^ e j : kˣ) : k) := by
      intro t
      funext j
      fin_cases j <;> simp [e]
    let p₁ := vanishingIdeal k (Set.range fun t : kˣ ↦ torusEmb ((1 : kˣ), t))
    let p₂ := vanishingIdeal k ({torusEmb (1 : kˣ × kˣ)} : Set (Fin 4 → k))
    have hp₁mem : ∀ f, f ∈ p₁ ↔ ∀ t : kˣ, aeval (torusEmb ((1 : kˣ), t)) f = 0 := fun f ↦ by
      simp only [p₁, mem_vanishingIdeal_iff, Set.forall_mem_range]
    have hp₁ : p₁.IsPrime := by
      refine ⟨fun htop ↦ ?_, fun {f g} hfg ↦ ?_⟩
      · have := (hp₁mem 1).1 (htop ▸ Submodule.mem_top) 1
        simp at this
      · obtain ⟨N, φ, hφ⟩ := exists_curve_clear e f
        obtain ⟨M, ψ, hψ⟩ := exists_curve_clear e g
        have hprod : φ * ψ = 0 := by
          apply Polynomial.eq_zero_of_infinite_isRoot
          have hinf : {x : k | x ≠ 0}.Infinite := by
            convert (Set.infinite_univ (α := k)).sdiff (Set.finite_singleton (0 : k)) using 1
            ext x
            simp
          refine Set.Infinite.mono (s := {x : k | x ≠ 0}) ?_ hinf
          intro x hx
          let t : kˣ := Units.mk0 x hx
          have hfgt := (hp₁mem (f * g)).1 hfg t
          rw [map_mul, hcurve] at hfgt
          simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_mul]
          have hx' : x = (t : k) := rfl
          rw [hx', hφ, hψ]
          calc (t : k) ^ N * aeval (fun j ↦ ((t ^ e j : kˣ) : k)) f *
                ((t : k) ^ M * aeval (fun j ↦ ((t ^ e j : kˣ) : k)) g)
              = (t : k) ^ N * (t : k) ^ M * (aeval (fun j ↦ ((t ^ e j : kˣ) : k)) f *
                  aeval (fun j ↦ ((t ^ e j : kˣ) : k)) g) := by ring
            _ = 0 := by rw [hfgt, mul_zero]
        rcases mul_eq_zero.1 hprod with h0 | h0
        · left
          rw [hp₁mem]
          intro t
          have := hφ t
          rw [h0, Polynomial.eval_zero] at this
          rw [hcurve]
          exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ t.ne_zero)
        · right
          rw [hp₁mem]
          intro t
          have := hψ t
          rw [h0, Polynomial.eval_zero] at this
          rw [hcurve]
          exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ t.ne_zero)
    have hp₂ : p₂.IsPrime := (isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨_, rfl⟩).isPrime
    obtain ⟨g₀, hg₀, h₀, hh₀, hgh₀⟩ := hproj₁
    obtain ⟨g₁, hg₁, h₁, hh₁, hgh₁⟩ := hproj₂
    have hJp₁ : J < p₁ := by
      refine lt_of_le_of_ne (fun f hf ↦ (hp₁mem f).2 fun t ↦ (hJmem f).1 hf _ (hall _))
        fun heq ↦ ?_
      have hmem : X 0 - C 1 ∈ p₁ := (hp₁mem _).2 fun t ↦ by simp
      rw [← heq] at hmem
      have hu : ∃ u : kˣ, u ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hgh₀ ((hcon _).trans (hcon _).symm)
      obtain ⟨u, hu⟩ := hu
      have := (hJmem _).1 hmem (u, 1) (hall _)
      simp only [map_sub, aeval_X, aeval_C, torusEmb_apply_zero, Algebra.algebraMap_self,
        RingHom.id_apply, sub_eq_zero] at this
      exact hu (Units.ext this)
    have hp₁p₂ : p₁ < p₂ := by
      refine lt_of_le_of_ne (fun f hf ↦ ?_) fun heq ↦ ?_
      · rw [mem_vanishingIdeal_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hp₁mem f).1 hf 1
      · have hmem : X 1 - C 1 ∈ p₂ := by
          rw [mem_vanishingIdeal_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          simp
        rw [← heq] at hmem
        have hv : ∃ v : kˣ, v ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hgh₁ ((hcon _).trans (hcon _).symm)
        obtain ⟨v, hv⟩ := hv
        have := (hp₁mem _).1 hmem v
        simp only [map_sub, aeval_X, aeval_C, torusEmb_apply_one, Algebra.algebraMap_self,
          RingHom.id_apply, sub_eq_zero] at this
        exact hv (Units.ext this)
    have := two_le_ringKrullDim_quotient (P := J) hJp₁ hp₁p₂
    rw [hdim] at this
    norm_num at this
  -- Height one and the prime generator.
  have hdim2 : ringKrullDim (MvPolynomial (Fin 2) k) = 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨Mx, hMmax, hIM⟩ := Ideal.exists_le_maximal I₂ hI₂prime.ne_top
  have hIMlt : I₂ < Mx := lt_of_le_of_ne hIM fun h ↦ hnmax (h ▸ hMmax)
  have hheight : I₂.height = 1 := by
    have hM2 : (Mx.height : WithBot ℕ∞) ≤ 2 := by
      rw [← hdim2]
      exact Ideal.height_le_ringKrullDim_of_ne_top hMmax.ne_top
    have hstep : I₂.height + 1 ≤ Mx.height := Ideal.height_add_one_le_of_lt_of_isPrime hIMlt
    have hle : I₂.height + 1 ≤ 2 := by
      exact_mod_cast hstep.trans (WithBot.coe_le_coe.1 hM2)
    have hne : I₂.height ≠ 0 := fun h ↦ hbot (Ideal.height_eq_zero_iff_eq_bot.1 h)
    set ht := I₂.height with hht
    have htop : ht ≠ ⊤ := by
      intro h
      rw [h, top_add] at hle
      simp at hle
    lift ht to ℕ using htop with n hn
    have h1 : n + 1 ≤ 2 := by exact_mod_cast hle
    have h2 : n ≠ 0 := by exact_mod_cast hne
    have h3 : n = 1 := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → ℕ∞) h3
  obtain ⟨F, hFI, hFp⟩ := hI₂prime.exists_mem_prime_of_ne_bot hbot
  have hIF : I₂ = Ideal.span {F} := Ideal.eq_span_singleton_of_height_eq_one hheight hFI hFp
  -- Scaling by a point of `H` fixes the ideal `(F)`.
  have hscale : ∀ h ∈ H,
      Ideal.span {scale ![(h.1 : k), (h.2 : k)] F} = Ideal.span {F} := fun h hh ↦ by
    set c : Fin 2 → k := ![(h.1 : k), (h.2 : k)] with hc
    have hc0 : ∀ j, c j ≠ 0 := by
      intro j
      fin_cases j <;> simp [c]
    have hmem : scale c F ∈ I₂ := (hI₂mem _).2 fun h' hh' ↦ by
      have hfun : (fun j ↦ algebraMap k k (c j) * ![(h'.1 : k), (h'.2 : k)] j) =
          ![((h' * h).1 : k), ((h' * h).2 : k)] := by
        funext j
        fin_cases j <;> simp [c, mul_comm]
      rw [aeval_scale, hfun]
      exact (hI₂mem F).1 hFI _ (H.mul_mem hh' hh)
    have hcc : c * c⁻¹ = 1 := by
      funext j
      simp [hc0 j]
    have hcc' : c⁻¹ * c = 1 := by
      rw [mul_comm, hcc]
    let T : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
      AlgEquiv.ofAlgHom (scale c) (scale c⁻¹)
        (AlgHom.ext fun g ↦ by rw [AlgHom.comp_apply, AlgHom.id_apply, scale_scale, hcc,
          scale_one])
        (AlgHom.ext fun g ↦ by rw [AlgHom.comp_apply, AlgHom.id_apply, scale_scale, hcc',
          scale_one])
    have hprime : Prime (scale c F) := (MulEquiv.prime_iff T).2 hFp
    rw [hIF, Ideal.mem_span_singleton] at hmem
    exact Ideal.span_singleton_eq_span_singleton.2 (Prime.associated_of_dvd hFp hprime hmem).symm
  -- Two distinct support monomials of `F`.
  have hsupp : ∃ m ∈ F.support, ∃ m' ∈ F.support, m ≠ m' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m₀, hm₀⟩ := Finset.nonempty_iff_ne_empty.2 fun h ↦
      hFp.ne_zero (MvPolynomial.support_eq_empty.1 h)
    have hsing : F.support = {m₀} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hm₀, fun m hm ↦ hcon m hm m₀ hm₀⟩
    have h1 := (hI₂mem F).1 hFI 1 H.one_mem
    have h11 : ![((1 : kˣ × kˣ).1 : k), ((1 : kˣ × kˣ).2 : k)] = fun _ ↦ (1 : k) := by
      funext j
      fin_cases j <;> simp
    rw [h11] at h1
    change MvPolynomial.eval (fun _ ↦ (1 : k)) F = 0 at h1
    rw [MvPolynomial.eval_eq, hsing, Finset.sum_singleton] at h1
    simp only [one_pow, Finset.prod_const_one, mul_one] at h1
    exact (MvPolynomial.mem_support_iff.1 hm₀) h1
  obtain ⟨m, hm, m', hm', hmm'⟩ := hsupp
  -- Step 3: the character relation.
  set d₁ : ℤ := (m 0 : ℤ) - m' 0 with hd₁
  set d₂ : ℤ := (m 1 : ℤ) - m' 1 with hd₂
  have hrel : ∀ h ∈ H, h.1 ^ d₁ * h.2 ^ d₂ = 1 := fun h hh ↦ by
    have hc0 : ∀ j, (![(h.1 : k), (h.2 : k)] : Fin 2 → k) j ≠ 0 := by
      intro j
      fin_cases j <;> simp
    have hk := monomial_prod_eq_of_span_scale_eq hc0 hFp.ne_zero (hscale h hh) m hm m' hm'
    rw [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _),
      Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _), Fin.prod_univ_two, Fin.prod_univ_two]
      at hk
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hk
    have hu : h.1 ^ (m 0) * h.2 ^ (m 1) = h.1 ^ (m' 0) * h.2 ^ (m' 1) :=
      Units.ext (by push_cast; exact hk)
    rw [hd₁, hd₂, zpow_sub, zpow_sub, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
      mul_mul_mul_comm, ← mul_inv, hu, mul_inv_cancel]
  have hd : d₁ ≠ 0 ∨ d₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hmm'
    ext j
    fin_cases j
    · have := hcon.1
      simp only [hd₁, sub_eq_zero] at this
      exact_mod_cast this
    · have := hcon.2
      simp only [hd₂, sub_eq_zero] at this
      exact_mod_cast this
  -- A power of a unit equal to one gives a natural power equal to one.
  have hnat : ∀ {x : kˣ} {z : ℤ}, x ^ z = 1 → x ^ z.natAbs = 1 := by
    intro x z hz
    rcases Int.natAbs_eq z with h | h
    · rw [h, zpow_natCast] at hz
      exact hz
    · rw [h, zpow_neg, zpow_natCast, inv_eq_one] at hz
      exact hz
  have hd₁0 : d₁ ≠ 0 := by
    intro h0
    have hd₂0 : d₂ ≠ 0 := hd.resolve_left (not_not.2 h0)
    refine hsnd (Int.natAbs_ne_zero.2 hd₂0) fun h hh ↦ hnat ?_
    simpa [h0] using hrel h hh
  have hd₂0 : d₂ ≠ 0 := by
    intro h0
    refine hfst (Int.natAbs_ne_zero.2 hd₁0) fun h hh ↦ hnat ?_
    simpa [h0] using hrel h hh
  -- The primitive character.
  set g := Int.gcd d₁ d₂ with hgdef
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_left _ hd₁0
  set a : ℤ := d₁ / g with ha
  set b : ℤ := d₂ / g with hb
  have hcop : Int.gcd a b = 1 := Int.gcd_div_gcd_div_gcd hgpos
  have hd₁a : d₁ = a * g := (Int.ediv_mul_cancel (Int.gcd_dvd_left d₁ d₂)).symm
  have hd₂b : d₂ = b * g := (Int.ediv_mul_cancel (Int.gcd_dvd_right d₁ d₂)).symm
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hd₁a
    exact hd₁0 hd₁a
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hd₂b
    exact hd₂0 hd₂b
  have hchar : ∀ h ∈ H, h.1 ^ a * h.2 ^ b = 1 := by
    obtain ⟨ζ, hζ⟩ := hconst (charMono a b) hgpos.ne' fun h hh ↦ by
      rw [aeval_charMono, ← Units.val_pow_eq_pow_val, ← zpow_natCast, mul_zpow, ← zpow_mul,
        ← zpow_mul, ← hd₁a, ← hd₂b, hrel h hh, Units.val_one]
    have h1 := hζ 1 H.one_mem
    rw [aeval_charMono] at h1
    simp only [Prod.fst_one, Prod.snd_one, one_zpow, mul_one, Units.val_one] at h1
    intro h hh
    have := hζ h hh
    rw [aeval_charMono, ← h1] at this
    exact Units.ext this
  -- Step 4: the cocharacter.
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, a * p + b * q = 1 :=
    ⟨Int.gcdA a b, Int.gcdB a b, by rw [← Int.gcd_eq_gcd_ab, hcop, Nat.cast_one]⟩
  let lam : kˣ →* kˣ × kˣ := (zpowGroupHom b).prod (zpowGroupHom (-a))
  have hlam : ∀ t : kˣ, lam t = (t ^ b, t ^ (-a)) := fun t ↦ rfl
  have hker : ∀ x : kˣ × kˣ, x.1 ^ a * x.2 ^ b = 1 → x = lam (x.1 ^ q * x.2 ^ (-p)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := eq_cochar_of_mul_eq_one hpq hx
    rw [hlam]
    exact Prod.ext h1.symm h2.symm
  let L := H.comap lam
  have hL : ∀ t : kˣ, t ∈ L := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀⟩ := hcon
    have hnot : torusEmb (lam t₀) ∉ zeroLocus k J := by
      rw [hclosed]
      rintro ⟨h, hh, hht⟩
      apply ht₀
      change lam t₀ ∈ H
      rw [← torusEmb_injective hht]
      exact hh
    rw [mem_zeroLocus_iff] at hnot
    push Not at hnot
    obtain ⟨f, hfJ, hf0⟩ := hnot
    let e : Fin 4 → ℤ := ![b, -a, -b, a]
    have hcurve : ∀ t : kˣ, torusEmb (lam t) = fun j ↦ ((t ^ e j : kˣ) : k) := by
      intro t
      funext j
      fin_cases j <;> simp [e, hlam, zpow_neg]
    obtain ⟨N, φ, hφ⟩ := exists_curve_clear e f
    have hφ0 : φ ≠ 0 := by
      intro h0
      have := hφ t₀
      rw [h0, Polynomial.eval_zero, ← hcurve] at this
      exact hf0 ((mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ t₀.ne_zero))
    have hfinL : (L : Set kˣ).Finite := by
      refine ((Polynomial.finite_setOfPred_isRoot hφ0).preimage
        Units.val_injective.injOn).subset fun t ht ↦ ?_
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot.def]
      rw [hφ, ← hcurve, (hJmem f).1 hfJ _ ht, mul_zero]
    apply hinfinite
    refine (hfinL.image lam).subset fun h hh ↦ ?_
    refine ⟨h.1 ^ q * h.2 ^ (-p), ?_, (hker h (hchar h hh)).symm⟩
    change lam (h.1 ^ q * h.2 ^ (-p)) ∈ H
    rw [← hker h (hchar h hh)]
    exact hh
  -- Conclusion.
  have hH : (H : Set (kˣ × kˣ)) = {x | x.1 ^ a * x.2 ^ b = 1} := by
    ext x
    constructor
    · exact hchar x
    · intro hx
      rw [Set.mem_ofPred_eq] at hx
      rw [SetLike.mem_coe, hker x hx]
      exact hL _
  have hH' : (H : Set (kˣ × kˣ)) = {x | x.1 ^ a = x.2 ^ (-b)} := by
    rw [hH]
    ext y
    simp only [Set.mem_ofPred_eq, zpow_neg]
    exact mul_eq_one_iff_eq_inv
  refine ⟨a, -b, ha0, neg_ne_zero.2 hb0, hH', fun x ↦ ?_⟩
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, hH']
  simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
    mul_zpow, inv_zpow]
  rw [inv_mul_eq_iff_eq_mul, mul_assoc]

end AclGeom
