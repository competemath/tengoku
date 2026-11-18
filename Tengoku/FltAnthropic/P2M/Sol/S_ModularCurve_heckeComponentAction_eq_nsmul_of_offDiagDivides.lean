import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroupHecke

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_heckeComponentAction_eq_nsmul_of_offDiagDivides.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_heckeComponentAction_eq_nsmul_of_offDiagDivides

open ModularCurve Finset

noncomputable section

section Helpers
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
@isnad1 id=subsingl.1h1v.s6.aa1a5e6c7713 from=translated src=- shape=724e1fdd vocab=1788fca6
-/
theorem characterLattice_subsingleton (hι : Fintype.card ι ≤ 1) :
    Subsingleton (characterLattice ι) := by
  constructor
  rintro ⟨D, hD⟩ ⟨D', hD'⟩
  rw [mem_characterLattice] at hD hD'
  ext x
  have hx : ∀ y : ι, y = x := fun y => Fintype.card_le_one_iff.mp hι y x
  have hsum : ∀ E : ι → ℤ, ∑ y : ι, E y = E x := fun E => by
    rw [Finset.sum_eq_single x (fun y _ hy => absurd (hx y) hy)
        (fun h => absurd (Finset.mem_univ x) h)]
  simp only [hsum] at hD hD'
  simp [hD, hD']

omit [DecidableEq ι] in
/--
@isnad1 id=surjecti.0h2v.s13.03762c42518c from=translated src=- shape=d3930f95 vocab=50c6e06a
-/
theorem componentGroupProj_surjective (e : ι → ℕ) :
    Function.Surjective (componentGroupProj e) :=
  Submodule.mkQ_surjective _

/--
@isnad1 id=dvd.2h5v.s5.ccabf7cb581d from=translated src=- shape=ec5520ae vocab=9d2907ae
-/
theorem dvd_diag_sub_of_offDiagDivides {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (hrow : HeckeRowSums B n) (hdiv : HeckeOffDiagDivides e B) (i : ι) :
    (e i : ℤ) ∣ (B i i - n) := by
  have hsum : B i i - n = -∑ j ∈ univ.erase i, B i j := by
    have hrow_i := hrow i
    rw [← Finset.sum_erase_add _ _ (mem_univ i)] at hrow_i
    linarith
  rw [hsum]
  exact dvd_neg.mpr <|
    Finset.dvd_sum fun j hj => hdiv i j (Finset.ne_of_mem_erase hj).symm

def etaWitness (e : ι → ℕ) (B : Matrix ι ι ℤ) (n : ℤ) (i : ι) : ι → ℤ :=
  fun k => (B i k - if k = i then n else 0) / (e i : ℤ)

/--
@isnad1 id=eq.2h6v.s6.9bac4cbf248b from=translated src=- shape=45781b68 vocab=a8eddce7
-/
theorem etaWitness_spec {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (hrow : HeckeRowSums B n) (hdiv : HeckeOffDiagDivides e B) (i k : ι) :
    (e i : ℤ) * etaWitness e B n i k = B i k - if k = i then n else 0 := by
  refine Int.mul_ediv_cancel' ?_
  rcases eq_or_ne k i with rfl | hki
  · simpa using dvd_diag_sub_of_offDiagDivides hrow hdiv k
  · simpa [hki] using hdiv i k (Ne.symm hki)

/--
@isnad1 id=mem.3h5v.s7.b93a229fad83 from=translated src=- shape=abb1bb95 vocab=0f00938e
-/
theorem etaWitness_mem_characterLattice {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (he : ∀ x, 0 < e x) (hrow : HeckeRowSums B n) (hdiv : HeckeOffDiagDivides e B)
    (i : ι) : etaWitness e B n i ∈ characterLattice ι := by
  rw [mem_characterLattice]
  have hei : (e i : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (he i).ne'
  refine mul_left_cancel₀ hei ?_
  rw [mul_zero, Finset.mul_sum]
  calc ∑ k, (e i : ℤ) * etaWitness e B n i k
      = ∑ k, (B i k - if k = i then n else 0) :=
        Finset.sum_congr rfl fun k _ => etaWitness_spec hrow hdiv i k
    _ = (∑ k, B i k) - n := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' univ i (fun _ => n),
          ite_eq_left (mem_univ i)]
    _ = 0 := by rw [hrow i]; ring

/--
@isnad1 id=eq.4h6v.s6.3b6c54e0c751 from=translated src=- shape=7a6ce855 vocab=ddae4ed2
-/
theorem etaWitness_gram_spec {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (he : ∀ x, 0 < e x) (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (hdiv : HeckeOffDiagDivides e B) (i k : ι) :
    (e k : ℤ) * etaWitness e B n i k = B k i - if k = i then n else 0 := by
  have hei : (e i : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (he i).ne'
  have hspec := etaWitness_spec hrow hdiv i k
  rcases eq_or_ne k i with rfl | hki
  · exact hspec
  · rw [ite_eq_right hki, sub_zero] at hspec
    rw [ite_eq_right hki, sub_zero]
    refine mul_left_cancel₀ hei ?_
    calc (e i : ℤ) * ((e k : ℤ) * etaWitness e B n i k)
        = (e k : ℤ) * ((e i : ℤ) * etaWitness e B n i k) := by ring
      _ = (e k : ℤ) * B i k := by rw [hspec]
      _ = (e i : ℤ) * B k i := hsym i k

def coordFunctional (j : ι) : Module.Dual ℤ (characterLattice ι) :=
  (LinearMap.proj j).domRestrict (characterLattice ι)

omit [DecidableEq ι] in
/--
@isnad1 id=eq.0h3v.s9.430e23f6cb20 from=translated src=- shape=cf28107f vocab=4051c384
-/
@[scoped simp] theorem coordFunctional_apply (j : ι) (D : characterLattice ι) :
    coordFunctional j D = D.1 j := rfl

def basisDiff (i₀ k : ι) : characterLattice ι :=
  ⟨Pi.single k 1 - Pi.single i₀ 1, by
    rw [mem_characterLattice]
    simp⟩

theorem eq_sum_smul_basisDiff (i₀ : ι) (D : characterLattice ι) :
    D = ∑ k, D.1 k • basisDiff i₀ k := by
  have hdeg : ∑ k, D.1 k = 0 := (mem_characterLattice).mp D.2
  refine Subtype.ext (funext fun j => ?_)
  simp only [basisDiff, Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, Pi.single_apply]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ k, D.1 k * if j = k then (1 : ℤ) else 0) = D.1 j := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq univ j, ite_eq_left (mem_univ j)]
  have h2 : (∑ k, D.1 k * if j = i₀ then (1 : ℤ) else 0) = 0 := by
    rw [← Finset.sum_mul, hdeg, zero_mul]
  rw [h1, h2, sub_zero]

/--
@isnad1 id=eq.0h1v.s12.b0118323617c from=translated src=- shape=18ef16f2 vocab=3baf5380
-/
theorem span_coordFunctional_eq_top :
    Submodule.span ℤ (Set.range (coordFunctional (ι := ι))) = ⊤ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [eq_top_iff]
    intro φ _
    have hφ : φ = 0 := by
      ext D
      have hD : D = 0 := Subsingleton.elim
        (h := characterLattice_subsingleton (by simp [Fintype.card_eq_zero])) D 0
      simp [hD]
    exact hφ ▸ Submodule.zero_mem _
  · obtain ⟨i₀⟩ := hι
    rw [eq_top_iff]
    intro φ _
    have hφ : φ = ∑ k, φ (basisDiff i₀ k) • coordFunctional k := by
      ext D
      conv_lhs => rw [eq_sum_smul_basisDiff i₀ D, map_sum]
      simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        coordFunctional_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hφ]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/--
@isnad1 id=eq.4h5v.s13.f0897e9f5a31 from=translated src=- shape=df724a56 vocab=dcc81af3
-/
theorem gramMap_etaWitness {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (he : ∀ x, 0 < e x) (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (hdiv : HeckeOffDiagDivides e B) (i : ι) :
    gramMap e ⟨etaWitness e B n i, etaWitness_mem_characterLattice he hrow hdiv i⟩ =
      (heckeCharacterAction B hrow).dualMap (coordFunctional i) -
        n • coordFunctional i := by
  ext D'
  rw [gramMap_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.dualMap_apply', LinearMap.comp_apply, coordFunctional_apply,
    coordFunctional_apply, heckeCharacterAction_coe, heckeDivisorAction_apply,
    smul_eq_mul]
  calc ∑ k, (e k : ℤ) * (etaWitness e B n i k * D'.1 k)
      = ∑ k, (B k i - if k = i then n else 0) * D'.1 k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, etaWitness_gram_spec he hrow hsym hdiv i k]
    _ = (∑ k, B k i * D'.1 k) - n * D'.1 i := by
        simp only [sub_mul]
        rw [Finset.sum_sub_distrib]
        congr 1
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq' univ i, ite_eq_left (mem_univ i)]

/--
@isnad1 id=mem.4h5v.s13.0a04b0eeb60e from=translated src=- shape=be833203 vocab=65fce729
-/
theorem etaDual_mem_range_gramMap {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (he : ∀ x, 0 < e x) (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (hdiv : HeckeOffDiagDivides e B) (φ : Module.Dual ℤ (characterLattice ι)) :
    (heckeCharacterAction B hrow).dualMap φ - n • φ ∈ LinearMap.range (gramMap e) := by
  have hφ : φ ∈ Submodule.span ℤ (Set.range (coordFunctional (ι := ι))) := by
    rw [span_coordFunctional_eq_top]; exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, gramMap_etaWitness he hrow hsym hdiv i⟩
  · simp only [map_zero, smul_zero, sub_zero]
    exact Submodule.zero_mem _
  · intro ψ₁ ψ₂ _ _ h₁ h₂
    have hadd : (heckeCharacterAction B hrow).dualMap (ψ₁ + ψ₂) - n • (ψ₁ + ψ₂) =
        ((heckeCharacterAction B hrow).dualMap ψ₁ - n • ψ₁) +
        ((heckeCharacterAction B hrow).dualMap ψ₂ - n • ψ₂) := by
      rw [map_add, smul_add]; abel
    rw [hadd]; exact Submodule.add_mem _ h₁ h₂
  · intro c ψ _ hψ
    have hsmul : (heckeCharacterAction B hrow).dualMap (c • ψ) - n • (c • ψ) =
        c • ((heckeCharacterAction B hrow).dualMap ψ - n • ψ) := by
      rw [map_smul, smul_sub, smul_comm]
    rw [hsmul]; exact Submodule.smul_mem _ c hψ

/--
@isnad1 id=eq.4h5v.s14.f6de79ea8392 from=translated src=- shape=e4a275e8 vocab=f444553c
-/
theorem heckeComponentAction_eq_nsmul_of_offDiagDivides {e : ι → ℕ} {B : Matrix ι ι ℤ}
    {n : ℤ} (he : ∀ x, 0 < e x) (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (hdiv : HeckeOffDiagDivides e B) (x : componentGroup e) :
    heckeComponentAction e B hrow hsym x = n • x := by
  obtain ⟨φ, rfl⟩ := componentGroupProj_surjective e x
  rw [componentGroupProj_heckeComponentAction hrow hsym, ← map_smul,
    ← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (etaDual_mem_range_gramMap he hrow hsym hdiv φ)

end Helpers

/--
@isnad1 id=eq.4h5v.s14.f6de79ea8392 from=translated src=- shape=e4a275e8 vocab=f444553c
-/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → ℕ} {B : Matrix ι ι ℤ}
    {n : ℤ} (he : ∀ x, 0 < e x) (hrow : ModularCurve.HeckeRowSums B n)
    (hsym : ModularCurve.HeckeWeightSymm e B)
    (hdiv : ModularCurve.HeckeOffDiagDivides e B) (x : ModularCurve.componentGroup e) :
    ModularCurve.heckeComponentAction e B hrow hsym x = n • x :=
  heckeComponentAction_eq_nsmul_of_offDiagDivides he hrow hsym hdiv x
