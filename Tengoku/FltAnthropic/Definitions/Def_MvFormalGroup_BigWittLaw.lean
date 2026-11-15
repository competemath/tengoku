import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace BigWittLaw

open MvPolynomial

def addPoly (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ :=
  X (0, n) + X (1, n) + ∑ i ∈ Finset.range n, X (0, i) * X (1, n - 1 - i)

/--
@isnad1 id=eq.0h3v.s8.31b5fb170421 from=translated src=- shape=cd035385 vocab=7012d2e0
-/
theorem aeval_addPoly {A : Type*} [CommRing A] (g : Fin 2 × ℕ → A) (n : ℕ) :
    aeval g (addPoly n) = g (0, n) + g (1, n) + ∑ i ∈ Finset.range n, g (0, i) * g (1, n - 1 - i) := by
  simp [addPoly, map_add, map_sum, map_mul]

/--
@isnad1 id=eq.2h4v.s10.8f71eeb18586 from=translated src=- shape=313eedfe vocab=2a97b462
-/
theorem coeff_succ_mul {A : Type*} [CommRing A] {F G : PowerSeries A}
    (hF : PowerSeries.constantCoeff F = 1) (hG : PowerSeries.constantCoeff G = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1) (F * G) =
      PowerSeries.coeff (n + 1) F + PowerSeries.coeff (n + 1) G +
        ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n - 1 - i + 1) G := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_self, tsub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF, hG,
    mul_one, one_mul]
  have hsum : ∑ i ∈ Finset.range n,
      PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n + 1 - (i + 1)) G =
      ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n - 1 - i + 1) G := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    have h2 : n + 1 - (i + 1) = n - 1 - i + 1 := by omega
    rw [h2]
  rw [hsum]
  ring

/--
@isnad1 id=eq.2h4v.s9.f4f2f4c93a02 from=translated src=- shape=27b8d155 vocab=3176e092
-/
theorem coeff_succ_mul_eq_aeval {A : Type*} [CommRing A] {F G : PowerSeries A}
    (hF : PowerSeries.constantCoeff F = 1) (hG : PowerSeries.constantCoeff G = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1) (F * G) =
      aeval (fun im : Fin 2 × ℕ =>
        (![fun m => PowerSeries.coeff (m + 1) F, fun m => PowerSeries.coeff (m + 1) G] :
          Fin 2 → ℕ → A) im.1 im.2) (addPoly n) := by
  rw [coeff_succ_mul hF hG, aeval_addPoly]
  simp

/--
@isnad1 id=eq.0h1v.s7.23b1eb056b15 from=translated src=- shape=119c3abb vocab=d78e9d9e
-/
theorem constantCoeff_addPoly (n : ℕ) : constantCoeff (addPoly n) = 0 := by
  simp [addPoly, constantCoeff_X]

/--
@isnad1 id=isweight.0h1v.s5.015c0d1d15ea from=translated src=- shape=98ec06db vocab=10b66c99
-/
theorem isWeightedHomogeneous_addPoly (n : ℕ) :
    IsWeightedHomogeneous (fun im : Fin 2 × ℕ => im.2 + 1) (addPoly n) (n + 1) := by
  refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.add ?_ ?_) ?_
  · exact isWeightedHomogeneous_X ℤ _ _
  · exact isWeightedHomogeneous_X ℤ _ _
  · refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    have h := (isWeightedHomogeneous_X ℤ (fun im : Fin 2 × ℕ => im.2 + 1) ((0 : Fin 2), i)).mul
      (isWeightedHomogeneous_X ℤ (fun im : Fin 2 × ℕ => im.2 + 1) ((1 : Fin 2), n - 1 - i))
    have hw : (i + 1) + (n - 1 - i + 1) = n + 1 := by omega
    rwa [hw] at h

variable (R : Type u) [CommRing R]

def addFam (n : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  ↑(MvPolynomial.map (Int.castRingHom R) (addPoly n))

/--
@isnad1 id=eq.0h2v.s8.60a3f34ab529 from=translated src=- shape=b534780b vocab=f972001d
-/
theorem addFam_eq (n : ℕ) :
    addFam R n = MvPowerSeries.X (0, n) + MvPowerSeries.X (1, n) +
      ∑ i ∈ Finset.range n, MvPowerSeries.X (0, i) * MvPowerSeries.X (1, n - 1 - i) := by
  have hc : ∀ P : MvPolynomial (Fin 2 × ℕ) R,
      (P : MvPowerSeries (Fin 2 × ℕ) R) = MvPolynomial.coeToMvPowerSeries.ringHom P := fun _ => rfl
  rw [addFam, hc]
  simp [addPoly, map_add, map_sum, map_mul]

/--
@isnad1 id=eq.0h2v.s7.e5ad4a32b425 from=translated src=- shape=aba7675c vocab=0a9db59f
-/
theorem constantCoeff_addFam (n : ℕ) : MvPowerSeries.constantCoeff (addFam R n) = 0 := by
  rw [addFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    coeff_map, ← constantCoeff_eq, constantCoeff_addPoly, map_zero]

/--
@isnad1 id=eq.1h3v.s8.8f4c9fbf9d54 from=translated src=- shape=4ce67a24 vocab=ef11614a
-/
theorem weight_eq_of_coeff_addFam_ne_zero {n : ℕ} {e : Fin 2 × ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff e (addFam R n) ≠ 0) :
    Finsupp.weight (fun im : Fin 2 × ℕ => im.2 + 1) e = n + 1 := by
  rw [addFam, MvPolynomial.coeff_coe, coeff_map] at h
  have h' : coeff e (addPoly n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_addPoly n h'

/--
@isnad1 id=hassubst.0h1v.s4.5b85322500e5 from=translated src=- shape=a5e51930 vocab=7efb908a
-/
theorem hasSubst_addFam : MvPowerSeries.HasSubst (addFam R) := by
  refine ⟨fun n => by rw [constantCoeff_addFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun im : Fin 2 × ℕ => im.2 + 1) e)).subset ?_
  intro n hn
  have hw := weight_eq_of_coeff_addFam_ne_zero R hn
  show n < Finsupp.weight (fun im : Fin 2 × ℕ => im.2 + 1) e
  omega

variable {R}

/--
@isnad1 id=eq.0h4v.s9.49481d09465c from=translated src=- shape=e59d5c6f vocab=684e518c
-/
theorem subst_coe_addFam {τ : Type*} (g : Fin 2 × ℕ → MvPolynomial τ ℤ) (n : ℕ) :
    MvPowerSeries.subst (fun im => ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) :
      MvPowerSeries τ R)) (addFam R n) =
      ((MvPolynomial.map (Int.castRingHom R) (aeval g (addPoly n)) : MvPolynomial τ R) :
        MvPowerSeries τ R) := by
  rw [addFam, MvPowerSeries.subst_coe]
  set G : Fin 2 × ℕ → MvPowerSeries τ R := fun im =>
    ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) : MvPowerSeries τ R)
  let ψ₁ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (aeval G).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp (C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
        (ψ₂.comp (C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))) r
    · simp [ψ₁, ψ₂, G]
  exact RingHom.congr_fun hψ (addPoly n)

/--
@isnad1 id=eq.1h5v.s8.877b8e63b1d6 from=translated src=- shape=a69c9b7c vocab=9a525de7
-/
theorem subst_addFam {τ : Type*} {S : Type*} [CommRing S] [Algebra R S]
    {u : Fin 2 × ℕ → MvPowerSeries τ S} (hu : MvPowerSeries.HasSubst u) (n : ℕ) :
    MvPowerSeries.subst u (addFam R n) =
      u (0, n) + u (1, n) + ∑ i ∈ Finset.range n, u (0, i) * u (1, n - 1 - i) := by
  rw [addFam_eq, ← MvPowerSeries.coe_substAlgHom hu]
  simp only [map_add, map_sum, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hu]

end BigWittLaw

end MvFormalGroup

end
