/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.Etale.StandardEtale
import Tengoku.Seed.RingTheory.RingHom.Etale
import Tengoku.Seed.RingTheory.KrullDimension.Field
import Tengoku.Seed.RingTheory.KrullDimension.Polynomial
import Tengoku.LanaOka.Oka.Analytification.RET.ConnectedZeroLocus
import Tengoku.LanaOka.Oka.RingTheory.FiniteNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generic étaleness and Noether normalisation of curves

- `ComplexAnalytic.exists_etale_localizationAway`: a finite extension `A` of domains of
  `R = ℂ[x₁, …, x_d]` is étale over `R` after inverting a nonzero `e ∈ R`. With the presentation of
  `ComplexAnalytic.exists_primitive_presentation`, `A_e` is the standard étale algebra
  `R[X][Y] ⧸ (P, Y e P' - 1)`.
- `ComplexAnalytic.ringKrullDim_le_of_isIntegral_of_injective`: the Krull dimension does not
  decrease along an injective integral ring map (going up).
- `ComplexAnalytic.exists_finite_injective_of_ringKrullDim_eq_one`: a domain of finite type and
  of dimension one over a field `k` is finite over `k[x]`.
-/

open Polynomial

namespace ComplexAnalytic

noncomputable section

/-! ### Generic étaleness -/

section Etale

variable {d : ℕ} {A : Type*} [CommRing A] [IsDomain A] [Algebra (MvPolynomial (Fin d) ℂ) A]
  [Module.Finite (MvPolynomial (Fin d) ℂ) A] [FaithfulSMul (MvPolynomial (Fin d) ℂ) A]

/-- The quotient map `R[X][Y] → R[X][Y] ⧸ (f, Y g - 1)`. -/
abbrev _root_.StandardEtalePair.π {R : Type*} [CommRing R] (Q : StandardEtalePair R) :
    R[X][X] →+* Q.Ring :=
  Ideal.Quotient.mk (Ideal.span {C Q.f, X * C Q.g - 1})

set_option backward.isDefEq.respectTransparency false in
lemma _root_.StandardEtalePair.π_C {R : Type*} [CommRing R] (Q : StandardEtalePair R) (a : R[X]) :
    Q.π (C a) = aeval Q.X a := by
  have : aeval (R := R) Q.X = (Ideal.Quotient.mkₐ R _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  rfl

lemma _root_.StandardEtalePair.π_X_mul {R : Type*} [CommRing R] (Q : StandardEtalePair R) :
    Q.π X * aeval Q.X Q.g = 1 := by
  rw [mul_comm]
  exact Q.aeval_X_g_mul_mk_X

lemma _root_.StandardEtalePair.exists_mul_pow_eq_aeval {R : Type*} [CommRing R]
    (Q : StandardEtalePair R) (z : Q.Ring) :
    ∃ (H : R[X]) (K : ℕ), z * aeval Q.X Q.g ^ K = aeval Q.X H := by
  obtain ⟨F, rfl⟩ : ∃ F, Q.π F = z := Ideal.Quotient.mk_surjective z
  induction F using Polynomial.induction_on' with
  | add F₁ F₂ h₁ h₂ =>
    obtain ⟨H₁, K₁, e₁⟩ := h₁
    obtain ⟨H₂, K₂, e₂⟩ := h₂
    refine ⟨H₁ * Q.g ^ K₂ + H₂ * Q.g ^ K₁, K₁ + K₂, ?_⟩
    simp only [map_add, map_mul, map_pow, ← e₁, ← e₂]
    ring
  | monomial n a =>
    refine ⟨a, n, ?_⟩
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, StandardEtalePair.π_C, mul_assoc,
      ← mul_pow, Q.π_X_mul, one_pow, mul_one]

lemma _root_.RingHom.Etale.comp_of_bijective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T} (hf : Function.Bijective f) (hg : g.Etale) :
    (g.comp f).Etale := by
  have hf' := RingHom.Etale.of_bijective hf
  rw [RingHom.etale_iff_formallyUnramified_and_smooth] at hf' hg ⊢
  exact ⟨hf'.1.comp hg.1, hf'.2.comp hg.2⟩

/-- **Generic étaleness.** A finite extension `A` of domains of `R = ℂ[x₁, …, x_d]` becomes étale
over `R` after inverting a suitable nonzero `e ∈ R`. -/
theorem exists_etale_localizationAway :
    ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧ ∀ (A' : Type*) [CommRing A'] [Algebra A A']
      [IsLocalization.Away (algebraMap (MvPolynomial (Fin d) ℂ) A e) A'],
      ((algebraMap A A').comp (algebraMap (MvPolynomial (Fin d) ℂ) A)).Etale := by
  classical
  set R := MvPolynomial (Fin d) ℂ
  obtain ⟨t, P, c, δ, hPm, -, hPt, hPdvd, hc, hcA, hδ, U, V, hUV⟩ :=
    exists_primitive_presentation (d := d) (A := A)
  refine ⟨c * δ, mul_ne_zero hc hδ, fun A' _ _ _ ↦ ?_⟩
  letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Q : StandardEtalePair R :=
    { f := P, monic_f := hPm, g := C (c * δ) * derivative P,
      cond := ⟨C (c * δ), 0, 1, by ring⟩ }
  set x : A' := algebraMap A A' t
  have hPx : aeval x P = 0 := by rw [aeval_algebraMap_apply, hPt, map_zero]
  have he : IsUnit (algebraMap R A' (c * δ)) := by
    rw [IsScalarTower.algebraMap_apply R A A']
    exact IsLocalization.Away.algebraMap_isUnit _
  have hδx : aeval x V * aeval x (derivative P) = algebraMap R A' δ := by
    have := congrArg (aeval x) hUV
    rwa [map_add, map_mul, map_mul, hPx, mul_zero, zero_add, aeval_C] at this
  have hδu : IsUnit (algebraMap R A' δ) := by
    rw [map_mul] at he
    exact isUnit_of_mul_isUnit_right he
  have hP'u : IsUnit (aeval x (derivative P)) :=
    isUnit_of_mul_isUnit_right (hδx ▸ hδu)
  have hgx : aeval x Q.g = algebraMap R A' (c * δ) * aeval x (derivative P) := by
    change aeval x (C (c * δ) * derivative P) = _
    rw [map_mul, aeval_C]
  have hmap : Q.HasMap x := ⟨hPx, hgx ▸ he.mul hP'u⟩
  let Φ := Q.lift x hmap
  have hΦ : ∀ H : R[X], Φ (aeval Q.X H) = aeval x H := fun H ↦ by
    rw [← aeval_algHom_apply, StandardEtalePair.lift_X]
  have hgu : IsUnit (aeval Q.X Q.g) := StandardEtalePair.hasMap_X.2
  set w : Q.Ring := ↑hgu.unit⁻¹
  have hw : w * aeval Q.X Q.g = 1 := hgu.val_inv_mul
  have hΦw : Φ w * (algebraMap R A' (c * δ) * aeval x (derivative P)) = 1 := by
    rw [← hgx, ← hΦ, ← map_mul, hw, map_one]
  have hu : Φ w * aeval x (derivative P) * algebraMap R A' (c * δ) = 1 := by
    rw [← hΦw]
    ring
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (algebraMap R A (c * δ))) y
    obtain ⟨H, hH⟩ := hcA a
    refine ⟨algebraMap R Q.Ring δ * w * aeval Q.X (derivative P) * aeval Q.X H *
      (w * aeval Q.X (derivative P)) ^ k, ?_⟩
    have h1 : aeval x H = algebraMap R A' c * algebraMap A A' a := by
      rw [aeval_algebraMap_apply, hH, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    have ha : algebraMap A A' a = algebraMap R A' δ * Φ w * aeval x (derivative P) *
        aeval x H := by
      rw [h1]
      rw [map_mul] at hΦw
      linear_combination (-(algebraMap A A' a)) * hΦw
    have e1 : Φ (algebraMap R Q.Ring δ * w * aeval Q.X (derivative P) * aeval Q.X H *
        (w * aeval Q.X (derivative P)) ^ k) =
        algebraMap A A' a * (Φ w * aeval x (derivative P)) ^ k := by
      simp only [map_mul, map_pow, AlgHom.commutes, hΦ]
      rw [ha]
    rw [e1, eq_comm, IsLocalization.mk'_eq_iff_eq_mul, map_pow,
      ← IsScalarTower.algebraMap_apply, mul_assoc, ← mul_pow, hu, one_pow, mul_one]
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun z hz ↦ ?_
    obtain ⟨H, K, hHK⟩ := Q.exists_mul_pow_eq_aeval z
    have h0 : aeval x H = 0 := by rw [← hΦ, ← hHK, map_mul, hz, zero_mul]
    rw [aeval_algebraMap_apply] at h0
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A (c * δ))) A' _).1 h0
    have hne : algebraMap R A (c * δ) ^ n ≠ 0 := pow_ne_zero _
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).2 (mul_ne_zero hc hδ))
    obtain ⟨G, rfl⟩ := hPdvd H ((mul_eq_zero.1 hn).resolve_left hne)
    have hQP : aeval Q.X P = 0 := StandardEtalePair.hasMap_X.1
    rw [map_mul (aeval Q.X) P G, hQP, zero_mul] at hHK
    exact (hgu.pow K).mul_left_eq_zero.1 hHK
  haveI : Algebra.Etale R A' := Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩)
  exact RingHom.etale_algebraMap.2 this

end Etale

/-! ### Dimension -/

section Dimension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

/-- **Going up for chains**: along an injective integral ring map every chain of primes of the
base lifts to a chain of the same length. -/
lemma exists_ltSeries_of_isIntegral (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      L.last.asIdeal.comap (algebraMap R S) = l.last.asIdeal := by
  induction l using RelSeries.inductionOn' with
  | singleton p =>
    obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal S)
      (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
          exact bot_le)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, hQp⟩
  | snoc l p hlp ih =>
    obtain ⟨L, hL, hLl⟩ := ih
    obtain ⟨Q, hQL, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      p.asIdeal L.last.asIdeal (by rw [hLl]; exact le_of_lt hlp)
    have hlp' : l.last < p := hlp
    have hlt : L.last < ⟨Q, hQ⟩ := lt_of_le_of_ne hQL fun h ↦ hlp'.ne (PrimeSpectrum.ext
      (hLl.symm.trans ((congrArg (fun P : PrimeSpectrum S ↦ P.asIdeal.comap (algebraMap R S))
        h).trans hQp)))
    exact ⟨L.snoc ⟨Q, hQ⟩ hlt, by simp [hL], by simpa using hQp⟩

/-- **The Krull dimension does not decrease along an injective integral ring map.** -/
theorem ringKrullDim_le_of_isIntegral_of_injective (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  refine iSup_le fun l ↦ ?_
  obtain ⟨L, hL, -⟩ := exists_ltSeries_of_isIntegral hinj l
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- **Noether normalisation of a curve**: a ring of finite type and of dimension one over a
field `k` is finite over a polynomial ring in one variable. -/
theorem exists_finite_injective_of_ringKrullDim_eq_one {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) :
    ∃ g : MvPolynomial (Fin 1) k →ₐ[k] A, Function.Injective g ∧ g.Finite := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have hdimP : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have h1 := ringKrullDim_le_of_isIntegral (R := MvPolynomial (Fin s) k) (S := A)
  have h2 := ringKrullDim_le_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) (S := A)
    hinj
  rw [hdim, hdimP] at h1 h2
  obtain rfl : s = 1 := by exact_mod_cast le_antisymm h2 h1
  exact ⟨g, hinj, hfin⟩

end Dimension

end

end ComplexAnalytic
