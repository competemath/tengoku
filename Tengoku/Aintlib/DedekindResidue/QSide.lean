/-
DedekindResidue: the ℚ-side facts for the relative (K/ℚ) Lemma 4.

Belabas–Friedman's Lemma 4 is applied at `k = ℚ`, so the σ-display must be
instantiated at the rationals: `ζ_ℚ` is the Riemann zeta on `Re s > 1` (there is one
ideal of `ℤ` per positive norm), the completed Riemann zeta is a completed Dedekind
zeta for `ℚ` (so mathlib's `RiemannHypothesis` transfers to our
`GeneralizedRiemannHypothesis ℚ`), and `κ_ℚ = 1`.
-/
module

public import Tengoku
public import Tengoku.Aintlib.DedekindResidue.CompletedZeta.GRH

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace DedekindResidue

open NumberField

/-- `ℤ⧸(n)` has `n` elements, so the principal ideal `(n)` has absolute norm `n`.
@isnad1 id=eq.0h1v.s7.94b4e5d38ead from=translated src=- shape=26325799 vocab=b86362c2
-/
theorem absNorm_span_natCast (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : ℤ)}) = n := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (Int.quotientSpanEquivZMod n).toEquiv]
  exact Nat.card_zmod n

/-- **There is exactly one ideal of `ℤ` of each positive norm.**
@isnad1 id=eq.0h1v.s7.8096d5982688 from=translated src=- shape=27b7a447 vocab=e4666392
-/
theorem card_int_ideal_absNorm_eq (n : ℕ) :
    Nat.card {J : Ideal ℤ // Ideal.absNorm J = n} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · -- uniqueness: `ℤ` is a PID and the generator is pinned up to sign by the norm
    refine ⟨fun ⟨J₁, hJ₁⟩ ⟨J₂, hJ₂⟩ => ?_⟩
    obtain ⟨g₁, rfl⟩ := (IsPrincipalIdealRing.principal J₁).principal
    obtain ⟨g₂, rfl⟩ := (IsPrincipalIdealRing.principal J₂).principal
    have e₁ : (Submodule.span ℤ {g₁} : Ideal ℤ) = Ideal.span {g₁} := rfl
    have e₂ : (Submodule.span ℤ {g₂} : Ideal ℤ) = Ideal.span {g₂} := rfl
    have h₁ : Ideal.span ({g₁} : Set ℤ) = Ideal.span {(g₁.natAbs : ℤ)} :=
      (Int.span_natAbs g₁).symm
    have h₂ : Ideal.span ({g₂} : Set ℤ) = Ideal.span {(g₂.natAbs : ℤ)} :=
      (Int.span_natAbs g₂).symm
    have hn₁ : g₁.natAbs = n := by
      rwa [e₁, h₁, absNorm_span_natCast] at hJ₁
    have hn₂ : g₂.natAbs = n := by
      rwa [e₂, h₂, absNorm_span_natCast] at hJ₂
    refine Subtype.ext ?_
    change (Submodule.span ℤ {g₁} : Ideal ℤ) = Submodule.span ℤ {g₂}
    rw [e₁, e₂, h₁, h₂, hn₁, hn₂]
  · exact ⟨⟨Ideal.span {(n : ℤ)}, absNorm_span_natCast n⟩⟩

/-- The absolute ideal norm is invariant under a ring isomorphism (the quotients are
isomorphic).
@isnad1 id=eq.0h4v.s9.7edbc70a9dd9 from=translated src=- shape=176096b8 vocab=4ae6975c
-/
theorem absNorm_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    [Module.Free ℤ S] [Module.Finite ℤ S] (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (I.map (e : R →+* S)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map (e : R →+* S)) e rfl).toEquiv).symm

/-- **There is exactly one ideal of `𝓞 ℚ` of each norm** (transport along
`𝓞 ℚ ≃+* ℤ`).
@isnad1 id=eq.0h1v.s8.50cbfdbb47a9 from=translated src=- shape=8a38b8a1 vocab=78476fa4
-/
theorem card_rat_ideal_absNorm_eq (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  have e := Rat.ringOfIntegersEquiv
  have hEquiv : {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n}
      ≃ {J : Ideal ℤ // Ideal.absNorm J = n} :=
    { toFun := fun I => ⟨I.1.map (e : 𝓞 ℚ →+* ℤ), by
        rw [absNorm_map_ringEquiv]
        exact I.2⟩
      invFun := fun J => ⟨J.1.map (e.symm : ℤ →+* 𝓞 ℚ), by
        rw [absNorm_map_ringEquiv]
        exact J.2⟩
      left_inv := fun I => Subtype.ext (Ideal.map_of_equiv e)
      right_inv := fun J => by
        refine Subtype.ext ?_
        have h1 := Ideal.map_of_equiv (I := J.1) e.symm
        rwa [RingEquiv.symm_symm] at h1 }
  rw [Nat.card_congr hEquiv]
  exact card_int_ideal_absNorm_eq n

/-- **`ζ_ℚ` is the Riemann zeta function** on `Re s > 1`.
@isnad1 id=eq.1h1v.s4.dcb78be8ac93 from=translated src=- shape=b76b296a vocab=b72e82e0
-/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  rw [NumberField.dedekindZeta, ← LSeries_one_eq_riemannZeta hs]
  refine LSeries_congr (fun {n} _hn => ?_) s
  rw [card_rat_ideal_absNorm_eq n]
  simp

/-- The completed-zeta prefactor of `ℚ` is `Γ_ℝ` (discriminant `1`, one real place).
@isnad1 id=eq.0h1v.s3.92efbb0cd620 from=translated src=- shape=25ac9e83 vocab=38b4e472
-/
theorem completedZetaPrefactor_rat (s : ℂ) :
    completedZetaPrefactor ℚ s = Complex.Gammaℝ s := by
  rw [completedZetaPrefactor, gammaFactor,
    NumberField.InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one
      (Module.finrank_self ℚ),
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one
      (Module.finrank_self ℚ),
    Rat.numberField_discr]
  norm_num

/-- **`completedRiemannZeta` is a completed Dedekind zeta function for `ℚ`.**
@isnad1 id=iscomple.0h0v.s2.5c42ce728e30 from=translated src=- shape=25b03439 vocab=45a3f32d
-/
theorem isCompletedDedekindZeta_rat :
    IsCompletedDedekindZeta ℚ completedRiemannZeta := by
  constructor
  · intro s hs
    have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    rw [completedZetaPrefactor_rat, dedekindZeta_rat_eq_riemannZeta hs,
      riemannZeta_def_of_ne_zero hs0,
      mul_div_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))]
  · refine ⟨fun s => s * (s - 1) * completedRiemannZeta₀ s + 1, ?_, ?_⟩
    · exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
        differentiable_completedZeta₀).add_const 1
    · intro s hs0 hs1
      rw [completedRiemannZeta_eq]
      have h1 : (1:ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
      field_simp
      ring

/-- **The Riemann Hypothesis transfers to `GeneralizedRiemannHypothesis ℚ`**: any
completed Dedekind zeta function for `ℚ` agrees with `completedRiemannZeta` away
from the poles, whose zeros off the critical line RH excludes.
@isnad1 id=generali.1h0v.s2.4ffbc9175ee5 from=translated src=- shape=ffc494c5 vocab=562e7bb5
-/
theorem generalizedRiemannHypothesis_rat (hRH : RiemannHypothesis) :
    GeneralizedRiemannHypothesis ℚ := by
  intro Λ hΛ s hs hs1 hzero
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hΛs : Λ s = completedRiemannZeta s :=
    hΛ.eqOn isCompletedDedekindZeta_rat hs0 hs1
  have hcz : completedRiemannZeta s = 0 := by rwa [← hΛs]
  have hζ : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hcz, zero_div]
  have hnottriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have h1 : ((-2 * ((n:ℂ) + 1)).re) = -2 * ((n:ℝ) + 1) := by
      simp
    rw [h1] at hs
    have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith
  have := hRH s hζ hnottriv hs1
  linarith [this ▸ hs]

/-! ### `κ_ℚ = 1` (Q4) -/

/-- The unit group of `ℤ` has rank `0`, so the regulator of `ℚ` is the empty
determinant.
@isnad1 id=eq.0h0v.s3.e178c7cb18bd from=translated src=- shape=b0ae1d2b vocab=fef14c19
-/
theorem regulator_rat_eq_one : NumberField.Units.regulator ℚ = 1 := by
  classical
  have : IsEmpty {w : NumberField.InfinitePlace ℚ //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    ⟨fun w => w.2 (Subsingleton.elim _ _)⟩
  rw [NumberField.Units.regulator_eq_det']
  simp

/-- The torsion of `ℚ` is `{±1}`.
@isnad1 id=eq.0h0v.s3.38770086ba5f from=translated src=- shape=b0ae1d2b vocab=16a47cda
-/
theorem torsionOrder_rat_eq_two : NumberField.Units.torsionOrder ℚ = 2 :=
  NumberField.Units.torsionOrder_eq_two_of_odd_finrank
    (by rw [Module.finrank_self]; exact odd_one)

/-- **`κ_ℚ = 1`**: the residue of the Riemann zeta at `1` through the class number
formula: `(2¹·(2π)⁰·1·1)/(2·√1) = 1`.
@isnad1 id=eq.0h0v.s3.fcd89a8b0f92 from=translated src=- shape=b0ae1d2b vocab=c3c3d806
-/
theorem dedekindZeta_residue_rat_eq_one : NumberField.dedekindZeta_residue ℚ = 1 := by
  rw [NumberField.dedekindZeta_residue_def,
    NumberField.InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one
      (Module.finrank_self ℚ),
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one
      (Module.finrank_self ℚ),
    Rat.classNumber_eq, regulator_rat_eq_one, torsionOrder_rat_eq_two,
    Rat.numberField_discr]
  norm_num

end DedekindResidue

end
