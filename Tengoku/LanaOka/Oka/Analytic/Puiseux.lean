/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.LanaOka.Oka.Analysis.Complex.KummerCover
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension
import Tengoku.LanaOka.Oka.Analytic.SimpleRootCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Puiseux expansions with parameters

Let `G` be a convex open subset of a finite-dimensional complex normed space `E` and let
`P = w ^ d + a₁ w ^ (d - 1) + ⋯ + a_d` be a monic polynomial in `w` whose coefficients are
holomorphic functions on `G × Δ`, where `Δ` is the open unit disc. Suppose that `P(y, x, ·)` is
separable whenever `x ≠ 0`, i.e. the discriminant of `P` vanishes at most along `x = 0`. Then
there is `s ≥ 1` such that after the base change `x = t ^ s`, `P` splits into linear factors
`w - φⱼ(y, t)` with `φⱼ` holomorphic on `G × Δ` (`Puiseux.exists_prod_eq`).

Over `G × Δ*` the roots form a finite covering (`Polynomial.isCoveringMap_fst_zeroLocus`), which
is a disjoint union of Kummer coverings (`IsCoveringMap.exists_homeomorph_sigma_kummer`). After
pulling back along `t ↦ t ^ s` with `s` divisible by all the degrees of these Kummer coverings,
every root becomes a single-valued function of `(y, t)`; it is holomorphic since simple roots
depend holomorphically on the coefficients, and it extends across `t = 0` by the Riemann
extension theorem since the roots of a monic polynomial are bounded by its coefficients.

## Main results

- `Puiseux.exists_prod_eq_of_mem_base`: the splitting over `G × Δ*`.
- `Puiseux.exists_prod_eq`: the splitting over `G × Δ`, together with the description of the
  zero set of `P` after base change as the union of the graphs of the `φⱼ`.
- `Puiseux.exists_prod_eq_of_radius`: the same over `G × Δ_r` for a disc of any radius `r`.

## References

- H. Grauert, R. Remmert, *Komplexe Räume*, Math. Ann. 136 (1958), §11, Hilfssatz 6.
-/

open Polynomial Set Metric Filter Topology Kummer

namespace Puiseux

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set E}

/-- A complex polynomial which is a product of linear factors vanishes exactly at the roots of
these factors. -/
theorem isRoot_iff_of_eq_prod {ι : Type*} [Fintype ι] {q : ℂ[X]} {a : ι → ℂ}
    (h : q = ∏ i, (X - C (a i))) (w : ℂ) : q.IsRoot w ↔ ∃ i, w = a i := by
  simp [h, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- The coefficients of `∏ (X - C (fᵢ z))` depend continuously on `z` where the `fᵢ` do. -/
theorem continuousOn_coeff_prod {Z ι : Type*} [TopologicalSpace Z] (s : Finset ι)
    {f : ι → Z → ℂ} {U : Set Z} (hf : ∀ i ∈ s, ContinuousOn (f i) U) (n : ℕ) :
    ContinuousOn (fun z ↦ (∏ i ∈ s, (X - C (f i z))).coeff n) U := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp only [Finset.prod_empty]; exact continuousOn_const
  | insert i s hi ih =>
    have hs : ∀ i ∈ s, ContinuousOn (f i) U := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    simp_rw [Finset.prod_insert hi, sub_mul, coeff_sub, coeff_C_mul]
    refine ContinuousOn.sub ?_ ((hf i (Finset.mem_insert_self i s)).mul (ih hs n))
    cases n with
    | zero => simp only [coeff_X_mul_zero]; exact continuousOn_const
    | succ n => simp only [coeff_X_mul]; exact ih hs n

/-- **Puiseux expansions over the punctured disc.** Let `P` be a monic polynomial whose
coefficients are holomorphic on `G × Δ*` and which is separable at every point of `G × Δ*`.
Then for some `s ≥ 1`, `P(y, t ^ s, ·)` is the product of `X - φⱼ(y, t)` over `G × Δ*`, with
holomorphic and pairwise distinct `φⱼ`. -/
theorem exists_prod_eq_of_mem_base (hG : Convex ℝ G) (hGo : IsOpen G)
    {P : (E × ℂ → ℂ)[X]} (hP : P.Monic)
    (hdiff : ∀ i, DifferentiableOn ℂ (P.coeff i) (base G))
    (hsep : ∀ z ∈ base G, (P.map (Pi.evalRingHom _ z)).Separable) :
    ∃ (s : ℕ+) (φ : Fin P.natDegree → E × ℂ → ℂ),
      (∀ j, DifferentiableOn ℂ (φ j) (base G)) ∧
      ∀ z ∈ base G, P.map (Pi.evalRingHom _ (z.1, z.2 ^ (s : ℕ))) =
        ∏ j, (X - C (φ j z)) ∧ Function.Injective fun j ↦ φ j z := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · exact ⟨1, 0, fun j ↦ by simp [base], fun z hz ↦ by simp [base] at hz⟩
  set q : E × ℂ → ℂ[X] := fun z ↦ P.map (Pi.evalRingHom _ z) with hq
  have hqc (z : E × ℂ) (i : ℕ) : (q z).coeff i = P.coeff i z := by simp [q]
  have hqm (z : E × ℂ) : (q z).Monic := hP.map _
  have hqd (z : E × ℂ) : (q z).natDegree = P.natDegree := hP.natDegree_map _
  have hbo : IsOpen (base G) := isOpen_base hGo
  -- The covering of `G × Δ*` by the roots.
  let pZ : base G → ℂ[X] := fun z ↦ q z
  have hc (i : ℕ) : Continuous fun z ↦ (pZ z).coeff i := by
    simp only [pZ, hqc]
    exact continuousOn_iff_continuous_domRestrict.1 (hdiff i).continuousOn
  have hcov := isCoveringMap_fst_zeroLocus (p := pZ) (fun z ↦ hqm z) (fun z ↦ hqd z) hc
    (fun z ↦ hsep z.1 z.2)
  have hfin := finite_preimage_fst_zeroLocus (p := pZ) (fun z ↦ hqm z)
  let Cm := ZerothHomotopy {x : base G × ℂ // (pZ x.1).eval x.2 = 0}
  obtain ⟨hC, k, Φ, hΦ⟩ : Finite Cm ∧ ∃ (k : Cm → ℕ+)
      (Φ : (Σ _ : Cm, base G) ≃ₜ {x : base G × ℂ // (pZ x.1).eval x.2 = 0}),
      ∀ c y, (Φ ⟨c, y⟩ : base G × ℂ).1 = cover G (k c) y :=
    hcov.exists_homeomorph_sigma_kummer hG hGo hfin
  letI : Fintype Cm := Fintype.ofFinite Cm
  -- The degree of the base change.
  set s : ℕ := ∏ c, (k c : ℕ) with hs
  have hs0 : 0 < s := Finset.prod_pos fun c _ ↦ (k c).pos
  have hks (c : Cm) : (k c : ℕ) ∣ s := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  set m : Cm → ℕ := fun c ↦ s / k c
  have hkm (c : Cm) : (k c : ℕ) * m c = s := Nat.mul_div_cancel' (hks c)
  have hm0 (c : Cm) : m c ≠ 0 := by
    intro h
    have := hkm c
    rw [h, mul_zero] at this
    omega
  set ζ : Cm → ℂ := fun c ↦ Complex.exp (2 * Real.pi * Complex.I / (k c : ℕ))
  have hζ (c : Cm) : IsPrimitiveRoot (ζ c) (k c) := Complex.isPrimitiveRoot_exp _ (k c).ne_zero
  have hζn (c : Cm) : ‖ζ c‖ = 1 := (hζ c).norm'_eq_one (k c).ne_zero
  -- The root functions on the components of the covering.
  let g : Cm → E × ℂ → ℂ := fun c z ↦ if h : z ∈ base G then (Φ ⟨c, ⟨z, h⟩⟩).1.2 else 0
  have hg (c : Cm) {z : E × ℂ} (hz : z ∈ base G) : g c z = (Φ ⟨c, ⟨z, hz⟩⟩).1.2 := dite_eq_left hz
  have hΦ₁ (c : Cm) {z : E × ℂ} (hz : z ∈ base G) :
      ((Φ ⟨c, ⟨z, hz⟩⟩).1.1 : E × ℂ) = (z.1, z.2 ^ (k c : ℕ)) := by
    rw [hΦ c ⟨z, hz⟩, cover_apply]
  have hgroot (c : Cm) {z : E × ℂ} (hz : z ∈ base G) :
      (q (z.1, z.2 ^ (k c : ℕ))).IsRoot (g c z) := by
    rw [hg c hz, ← hΦ₁ c hz]
    exact (Φ ⟨c, ⟨z, hz⟩⟩).2
  have hgcont (c : Cm) : ContinuousOn (g c) (base G) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (base G).domRestrict (g c) = fun z ↦ (Φ ⟨c, z⟩).1.2 := funext fun z ↦ hg c z.2
    rw [this]
    exact continuous_snd.comp (continuous_subtype_val.comp (Φ.continuous.comp continuous_sigmaMk))
  have hmemk (c : Cm) {z : E × ℂ} (hz : z ∈ base G) : (z.1, z.2 ^ (k c : ℕ)) ∈ base G := by
    rw [← preimage_prodMap_pow_base G (k c)] at hz
    exact hz
  have hgdiff (c : Cm) : DifferentiableOn ℂ (g c) (base G) := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine differentiableAt_of_isRoot_of_differentiableAt_coeff
      (p := fun z : E × ℂ ↦ q (z.1, z.2 ^ (k c : ℕ))) (n := P.natDegree)
      (fun z ↦ (hqd _).le) (fun i ↦ ?_) ((hgcont c).continuousAt (hbo.mem_nhds hz)) ?_ ?_
    · simp only [hqc]
      exact ((hdiff i).differentiableAt (hbo.mem_nhds (hmemk c hz))).comp z (by fun_prop)
    · filter_upwards [hbo.mem_nhds hz] with z' hz' using hgroot c hz'
    · exact (hsep _ (hmemk c hz)).eval₂_derivative_ne_zero (RingHom.id ℂ) (hgroot c hz)
  -- The branches after the base change `t ↦ t ^ s`.
  let ι := Σ c : Cm, Fin (k c)
  let u : ι → E × ℂ → E × ℂ := fun i z ↦ (z.1, ζ i.1 ^ (i.2 : ℕ) * z.2 ^ m i.1)
  have hu (i : ι) {z : E × ℂ} (hz : z ∈ base G) : u i z ∈ base G := by
    obtain ⟨h1, h2, h3⟩ := mem_base.1 hz
    refine mem_base.2 ⟨h1, mul_ne_zero (pow_ne_zero _ (by simp [ζ])) (pow_ne_zero _ h2), ?_⟩
    rw [norm_mul, norm_pow, norm_pow, hζn, one_pow, one_mul]
    exact pow_lt_one₀ (norm_nonneg _) h3 (hm0 _)
  have hupow (i : ι) (z : E × ℂ) : (u i z).2 ^ (k i.1 : ℕ) = z.2 ^ s := by
    simp only [u, mul_pow, ← pow_mul, ← hkm i.1]
    rw [mul_comm (i.2 : ℕ), pow_mul, (hζ i.1).pow_eq_one, one_pow, one_mul, mul_comm]
  let φ₀ : ι → E × ℂ → ℂ := fun i z ↦ g i.1 (u i z)
  have hφ₀diff (i : ι) : DifferentiableOn ℂ (φ₀ i) (base G) :=
    (hgdiff i.1).comp (by fun_prop) fun z hz ↦ hu i hz
  have hφ₀root (i : ι) {z : E × ℂ} (hz : z ∈ base G) : (q (z.1, z.2 ^ s)).IsRoot (φ₀ i z) := by
    have := hgroot i.1 (hu i hz)
    rwa [hupow] at this
  have hφ₀inj {z : E × ℂ} (hz : z ∈ base G) : Function.Injective fun i ↦ φ₀ i z := by
    rintro ⟨c, j⟩ ⟨c', j'⟩ h
    simp only [φ₀, hg _ (hu _ hz)] at h
    have hfst : (Φ ⟨c, ⟨u ⟨c, j⟩ z, hu ⟨c, j⟩ hz⟩⟩).1.1 =
        (Φ ⟨c', ⟨u ⟨c', j'⟩ z, hu ⟨c', j'⟩ hz⟩⟩).1.1 := by
      apply Subtype.ext
      rw [hΦ₁ _ (hu _ hz), hΦ₁ _ (hu _ hz), hupow ⟨c, j⟩, hupow ⟨c', j'⟩]
    have hΦeq := Φ.injective (Subtype.ext (Prod.ext hfst h))
    rw [Sigma.mk.inj_iff] at hΦeq
    obtain ⟨rfl, hh⟩ := hΦeq
    have hh' := congrArg (fun x : base G ↦ (x : E × ℂ).2) (eq_of_heq hh)
    simp only [u] at hh'
    have hz2 : z.2 ^ m c ≠ 0 := pow_ne_zero _ (mem_base.1 hz).2.1
    have hj := (hζ c).pow_inj j.2 j'.2 (mul_right_cancel₀ hz2 hh')
    obtain rfl : j = j' := Fin.ext hj
    rfl
  have hmems {z : E × ℂ} (hz : z ∈ base G) : (z.1, z.2 ^ s) ∈ base G := by
    rw [← preimage_prodMap_pow_base G ⟨s, hs0⟩] at hz
    exact hz
  have hφ₀surj {z : E × ℂ} (hz : z ∈ base G) {w : ℂ} (hw : (q (z.1, z.2 ^ s)).IsRoot w) :
      ∃ i, φ₀ i z = w := by
    obtain ⟨⟨c, v⟩, hv⟩ := Φ.surjective ⟨(⟨(z.1, z.2 ^ s), hmems hz⟩, w), hw⟩
    have h1 : ((v : E × ℂ).1, (v : E × ℂ).2 ^ (k c : ℕ)) = (z.1, z.2 ^ s) := by
      have := congrArg (fun y : base G × ℂ ↦ (y.1 : E × ℂ)) (congrArg Subtype.val hv)
      simpa only [hΦ c v, cover_apply] using this
    obtain ⟨hv1, hv2⟩ := Prod.mk.injEq _ _ _ _ ▸ h1
    have hz2 : z.2 ^ m c ≠ 0 := pow_ne_zero _ (mem_base.1 hz).2.1
    have hpow : ((v : E × ℂ).2 / z.2 ^ m c) ^ (k c : ℕ) = 1 := by
      rw [div_pow, hv2, ← pow_mul, mul_comm, hkm, div_self (pow_ne_zero _ (mem_base.1 hz).2.1)]
    obtain ⟨j, hj, hζj⟩ := (hζ c).eq_pow_of_pow_eq_one hpow
    refine ⟨⟨c, ⟨j, hj⟩⟩, ?_⟩
    have hvu : (⟨c, ⟨u ⟨c, ⟨j, hj⟩⟩ z, hu _ hz⟩⟩ : Σ _ : Cm, base G) = ⟨c, v⟩ := by
      refine congrArg (Sigma.mk c) (Subtype.ext (Prod.ext hv1.symm ?_))
      change ζ c ^ j * z.2 ^ m c = (v : E × ℂ).2
      rw [hζj, div_mul_cancel₀ _ hz2]
    change g c (u ⟨c, ⟨j, hj⟩⟩ z) = w
    rw [hg c (hu _ hz), hvu, hv]
  have himg {z : E × ℂ} (hz : z ∈ base G) :
      Finset.univ.image (fun i ↦ φ₀ i z) = (q (z.1, z.2 ^ s)).roots.toFinset := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_roots (hqm _).ne_zero]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ hφ₀root i hz, fun hw ↦ hφ₀surj hz hw⟩
  have hz₀ : ((y₀, 1 / 2) : E × ℂ) ∈ base G := mem_base.2 ⟨hy₀, by norm_num, by norm_num⟩
  have hcard : Fintype.card ι = P.natDegree := by
    rw [← Finset.card_univ, ← Finset.card_image_of_injective _ (hφ₀inj hz₀), himg hz₀,
      card_roots_toFinset_of_separable (hsep _ (hmems hz₀)), hqd]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨s, hs0⟩, fun j ↦ φ₀ (e.symm j), fun j ↦ hφ₀diff _,
    fun z hz ↦ ⟨?_, (hφ₀inj hz).comp e.symm.injective⟩⟩
  rw [Equiv.prod_comp e.symm (fun i ↦ X - C (φ₀ i z)),
    ← Finset.prod_image (f := fun w ↦ X - C w) fun i _ i' _ h ↦ hφ₀inj hz h, himg hz]
  exact (prod_roots_toFinset_of_separable (hqm _) (hsep _ (hmems hz))).symm

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Removing `t = 0` from `G × Δ` leaves `G × Δ*`. -/
lemma diff_preimage_snd_zero : G ×ˢ ball (0 : ℂ) 1 \ Prod.snd ⁻¹' {0} = base G := by
  ext z
  simp [mem_base, and_assoc, and_comm (a := z.2 ≠ 0)]

omit [NormedSpace ℂ E] in
/-- The locus `t = 0` has empty interior in `G × Δ`. -/
lemma interior_inter_preimage_snd_zero :
    interior (G ×ˢ ball (0 : ℂ) 1 ∩ Prod.snd ⁻¹' {0}) = ∅ := by
  refine eq_empty_of_subset_empty ((interior_mono inter_subset_right).trans ?_)
  rw [← univ_prod, interior_prod_eq, interior_singleton, prod_empty]

variable [FiniteDimensional ℂ E]

/-- **Puiseux expansions with parameters.** Let `G` be convex and open and let `P` be a monic
polynomial whose coefficients are holomorphic on `G × Δ`, `Δ` the open unit disc, such that
`P(y, x, ·)` is separable whenever `x ≠ 0`. Then for some `s ≥ 1` there are holomorphic
functions `φⱼ` on `G × Δ` with `P(y, t ^ s, ·) = ∏ⱼ (X - φⱼ(y, t))`. The `φⱼ(y, t)` are pairwise
distinct for `t ≠ 0`, and the zero set of `P(y, t ^ s, ·)` is the union of the graphs of the
`φⱼ`. -/
theorem exists_prod_eq (hG : Convex ℝ G) (hGo : IsOpen G) {P : (E × ℂ → ℂ)[X]} (hP : P.Monic)
    (hdiff : ∀ i, DifferentiableOn ℂ (P.coeff i) (G ×ˢ ball 0 1))
    (hsep : ∀ y ∈ G, ∀ x : ℂ, x ≠ 0 → ‖x‖ < 1 → (P.map (Pi.evalRingHom _ (y, x))).Separable) :
    ∃ (s : ℕ+) (φ : Fin P.natDegree → E × ℂ → ℂ),
      (∀ j, DifferentiableOn ℂ (φ j) (G ×ˢ ball 0 1)) ∧
      (∀ y ∈ G, ∀ t ∈ ball (0 : ℂ) 1,
        P.map (Pi.evalRingHom _ (y, t ^ (s : ℕ))) = ∏ j, (X - C (φ j (y, t)))) ∧
      (∀ y ∈ G, ∀ t ∈ ball (0 : ℂ) 1, ∀ w : ℂ,
        (P.map (Pi.evalRingHom _ (y, t ^ (s : ℕ)))).IsRoot w ↔ ∃ j, w = φ j (y, t)) ∧
      ∀ y ∈ G, ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → Function.Injective fun j ↦ φ j (y, t) := by
  set U := G ×ˢ ball (0 : ℂ) 1
  have hU : IsOpen U := hGo.prod isOpen_ball
  have hbU : base G ⊆ U := by rw [← diff_preimage_snd_zero]; exact sdiff_subset
  obtain ⟨s, φ, hφd, hφ⟩ := exists_prod_eq_of_mem_base hG hGo hP
    (fun i ↦ (hdiff i).mono hbU) fun z hz ↦ hsep z.1 (mem_base.1 hz).1 z.2
      (mem_base.1 hz).2.1 (mem_base.1 hz).2.2
  set q : E × ℂ → ℂ[X] := fun z ↦ P.map (Pi.evalRingHom _ (z.1, z.2 ^ (s : ℕ))) with hq
  have hqc (z : E × ℂ) (i : ℕ) : (q z).coeff i = P.coeff i (z.1, z.2 ^ (s : ℕ)) := by simp [q]
  have hmaps : MapsTo (fun z : E × ℂ ↦ (z.1, z.2 ^ (s : ℕ))) U U := by
    rintro z ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mem_ball_zero_iff] at h2 ⊢
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) h2 s.ne_zero
  have hqcont (i : ℕ) : ContinuousOn (fun z ↦ (q z).coeff i) U := by
    simp only [hqc]
    exact (hdiff i).continuousOn.comp (by fun_prop) hmaps
  have hZ := interior_inter_preimage_snd_zero (G := G)
  have hsnd : DifferentiableOn ℂ (Prod.snd : E × ℂ → ℂ) U := differentiable_snd.differentiableOn
  -- Extend the roots across `t = 0`.
  have hext (j : Fin P.natDegree) :
      ∃ F : E × ℂ → ℂ, DifferentiableOn ℂ F U ∧ EqOn F (φ j) (U \ Prod.snd ⁻¹' {0}) := by
    refine exists_differentiableOn_eqOn_of_isBoundedUnder hU hsnd hZ
      (by rw [diff_preimage_snd_zero]; exact hφd j) fun z hz ↦ ?_
    set β : E × ℂ → ℝ := fun z ↦ monicRootBound P.natDegree (q z)
    have hβ : ContinuousAt β z := by
      refine ContinuousOn.continuousAt ?_ (hU.mem_nhds hz)
      exact (continuousOn_finsetSum _ fun i _ ↦ (hqcont i).norm).add continuousOn_const
    refine isBoundedUnder_of_eventually_le (a := β z + 1) ?_
    filter_upwards [nhdsWithin_le_nhds (hβ.eventually (eventually_lt_nhds (lt_add_one (β z)))),
      self_mem_nhdsWithin] with w hw hwU
    rw [diff_preimage_snd_zero] at hwU
    refine (IsRoot.norm_le_monicRootBound (hP.map _) (hP.natDegree_map _) ?_).trans hw.le
    exact (isRoot_iff_of_eq_prod (hφ w hwU).1 _).2 ⟨j, rfl⟩
  choose F hFd hFφ using hext
  have hprod : EqOn q (fun z ↦ ∏ j, (X - C (F j z))) U := by
    intro z hz
    ext n
    refine Set.EqOn.of_eqOn_diff_zero hU hZ (hqcont n)
      (continuousOn_coeff_prod _ (fun j _ ↦ (hFd j).continuousOn) n) (fun w hw ↦ ?_) hz
    have hw' := hw
    rw [diff_preimage_snd_zero] at hw'
    simp only [q, (hφ w hw').1, fun j ↦ hFφ j hw]
  refine ⟨s, F, hFd, fun y hy t ht ↦ hprod (show (y, t) ∈ U from ⟨hy, ht⟩), fun y hy t ht w ↦
    isRoot_iff_of_eq_prod (hprod (show (y, t) ∈ U from ⟨hy, ht⟩)) w, fun y hy t ht0 ht ↦ ?_⟩
  have hmem : (y, t) ∈ base G := mem_base.2 ⟨hy, ht0, ht⟩
  have hU' : (y, t) ∈ U \ Prod.snd ⁻¹' {0} := by rw [diff_preimage_snd_zero]; exact hmem
  convert (hφ _ hmem).2 using 2 with j
  exact hFφ j hU'

/-- **Puiseux expansions with parameters over a disc of radius `r`.** The version of
`Puiseux.exists_prod_eq` for `G × Δ_r`: the roots of `P(y, t ^ s, ·)` are holomorphic on
`G × Δ_ρ` where `ρ ^ s = r`. -/
theorem exists_prod_eq_of_radius (hG : Convex ℝ G) (hGo : IsOpen G) {r : ℝ} (hr : 0 < r)
    {P : (E × ℂ → ℂ)[X]} (hP : P.Monic)
    (hdiff : ∀ i, DifferentiableOn ℂ (P.coeff i) (G ×ˢ ball 0 r))
    (hsep : ∀ y ∈ G, ∀ x : ℂ, x ≠ 0 → ‖x‖ < r → (P.map (Pi.evalRingHom _ (y, x))).Separable) :
    ∃ (s : ℕ+) (ρ : ℝ) (φ : Fin P.natDegree → E × ℂ → ℂ), 0 < ρ ∧ ρ ^ (s : ℕ) = r ∧
      (∀ j, DifferentiableOn ℂ (φ j) (G ×ˢ ball 0 ρ)) ∧
      (∀ y ∈ G, ∀ t ∈ ball (0 : ℂ) ρ,
        P.map (Pi.evalRingHom _ (y, t ^ (s : ℕ))) = ∏ j, (X - C (φ j (y, t)))) ∧
      (∀ y ∈ G, ∀ t ∈ ball (0 : ℂ) ρ, ∀ w : ℂ,
        (P.map (Pi.evalRingHom _ (y, t ^ (s : ℕ)))).IsRoot w ↔ ∃ j, w = φ j (y, t)) ∧
      ∀ y ∈ G, ∀ t : ℂ, t ≠ 0 → ‖t‖ < ρ → Function.Injective fun j ↦ φ j (y, t) := by
  -- Rescale the disc of radius `r` to the unit disc.
  let σ : E × ℂ → E × ℂ := fun z ↦ (z.1, (r : ℂ) * z.2)
  let R : (E × ℂ → ℂ) →+* (E × ℂ → ℂ) := RingHom.pi fun z ↦ Pi.evalRingHom _ (σ z)
  set P' := P.map R
  have hP' : P'.Monic := hP.map R
  have hdeg : P'.natDegree = P.natDegree := hP.natDegree_map R
  have hev (z : E × ℂ) :
      P'.map (Pi.evalRingHom _ z) = P.map (Pi.evalRingHom _ (σ z)) := by
    rw [Polynomial.map_map]
    rfl
  have hσ : MapsTo σ (G ×ˢ ball 0 1) (G ×ˢ ball 0 r) := by
    rintro z ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mem_ball_zero_iff] at h2 ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_lt_of_lt_one_right hr h2
  have hdiff' (i : ℕ) : DifferentiableOn ℂ (P'.coeff i) (G ×ˢ ball 0 1) := by
    have : P'.coeff i = P.coeff i ∘ σ := by
      ext z
      simp only [P', R, coeff_map]
      rfl
    rw [this]
    exact (hdiff i).comp (by fun_prop) hσ
  have hsep' (y : E) (hy : y ∈ G) (x : ℂ) (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
      (P'.map (Pi.evalRingHom _ (y, x))).Separable := by
    rw [hev]
    refine hsep y hy _ (mul_ne_zero (by exact_mod_cast hr.ne') hx) ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_lt_of_lt_one_right hr hx1
  obtain ⟨s, φ, hφd, hφ, hroot, hinj⟩ := exists_prod_eq hG hGo hP' hdiff' hsep'
  -- Undo the rescaling.
  set ρ : ℝ := r ^ (1 / (s : ℝ))
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hr _
  have hρs : ρ ^ (s : ℕ) = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, one_div_mul_cancel (by positivity),
      Real.rpow_one]
  let τ : E × ℂ → E × ℂ := fun z ↦ (z.1, z.2 / ρ)
  have hτ : MapsTo τ (G ×ˢ ball 0 ρ) (G ×ˢ ball 0 1) := by
    rintro z ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mem_ball_zero_iff] at h2 ⊢
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_lt_one hρ]
    exact h2
  have hστ (y : E) (t : ℂ) : σ (y, (τ (y, t)).2 ^ (s : ℕ)) = (y, t ^ (s : ℕ)) := by
    simp only [σ, τ, div_pow]
    congr 1
    rw [← Complex.ofReal_pow, hρs, mul_div_cancel₀ _ (by exact_mod_cast hr.ne')]
  have hfac (y : E) (hy : y ∈ G) (t : ℂ) (ht : t ∈ ball (0 : ℂ) ρ) :
      P.map (Pi.evalRingHom _ (y, t ^ (s : ℕ))) =
        (P'.map (Pi.evalRingHom _ ((τ (y, t)).1, (τ (y, t)).2 ^ (s : ℕ)))) := by
    rw [hev, hστ]
  refine ⟨s, ρ, fun j ↦ φ (Fin.cast hdeg.symm j) ∘ τ, hρ, hρs,
    fun j ↦ (hφd _).comp (by fun_prop) hτ, fun y hy t ht ↦ ?_, fun y hy t ht w ↦ ?_,
    fun y hy t ht0 ht ↦ ?_⟩
  · rw [hfac y hy t ht, hφ _ hy _ (hτ ⟨hy, ht⟩).2]
    exact (Fintype.prod_equiv (finCongr hdeg) _ _ fun j ↦ rfl)
  · rw [hfac y hy t ht, hroot _ hy _ (hτ ⟨hy, ht⟩).2]
    exact (finCongr hdeg).exists_congr fun j ↦ Iff.rfl
  · have h0 : (τ (y, t)).2 ≠ 0 := div_ne_zero ht0 (by exact_mod_cast hρ.ne')
    have h1 : ‖(τ (y, t)).2‖ < 1 := hτ ⟨hy, mem_ball_zero_iff.2 ht⟩ |>.2 |> mem_ball_zero_iff.1
    exact (hinj y hy _ h0 h1).comp (finCongr hdeg.symm).injective

end

end Puiseux
