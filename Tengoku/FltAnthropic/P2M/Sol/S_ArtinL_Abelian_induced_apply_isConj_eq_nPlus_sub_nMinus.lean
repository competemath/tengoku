import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ArtinL_Abelian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ArtinL_Abelian_induced_apply_isConj_eq_nPlus_sub_nMinus.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ArtinL_Abelian_induced_apply_isConj_eq_nPlus_sub_nMinus

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace
open scoped Classical

universe u

namespace ArtinArchProof

variable {F : Type u} [Field F] [NumberField F] [IsGalois ℚ F]

/--
@isnad1 id=bijectiv.0h2v.s7.640777d35097 from=translated src=- shape=2e12342a vocab=db3a4d28
-/
theorem comp_bijective (φ : F →+* ℂ) :
    Function.Bijective fun y : F ≃ₐ[ℚ] F => φ.comp (y : F →+* F) := by
  have hinj : Function.Injective fun y : F ≃ₐ[ℚ] F => φ.comp (y : F →+* F) := by
    intro y y' h
    apply AlgEquiv.ext
    intro z
    exact φ.injective (RingHom.congr_fun h z)
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, NumberField.Embeddings.card]

/--
@isnad1 id=ex.0h3v.s7.d532a3eb4534 from=translated src=- shape=2c843148 vocab=017c05be
-/
theorem exists_eq_comp (φ φ' : F →+* ℂ) : ∃ y : F ≃ₐ[ℚ] F, φ' = φ.comp (y : F →+* F) := by
  obtain ⟨y, hy⟩ := (comp_bijective φ).2 φ'
  exact ⟨y, hy.symm⟩

omit [IsGalois ℚ F] in

/--
@isnad1 id=eq.1h3v.s9.152d628246b4 from=translated src=- shape=03e8e573 vocab=c86ad069
-/
theorem mul_self_eq_one_of_isConj {φ : F →+* ℂ} {σ : F ≃ₐ[ℚ] F}
    (hσ : ComplexEmbedding.IsConj φ σ) : σ * σ = 1 := by
  apply AlgEquiv.ext
  intro z
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  exact ComplexEmbedding.isConj_apply_apply hσ z

variable (H : Subgroup (F ≃ₐ[ℚ] F))

abbrev fixK : IntermediateField ℚ F := IntermediateField.fixedField H

def emb (φ : F →+* ℂ) (x : F ≃ₐ[ℚ] F) : fixK H →+* ℂ :=
  (φ.comp (x : F →+* F)).comp (algebraMap (fixK H) F)

omit [IsGalois ℚ F] in
/--
@isnad1 id=eq.0h5v.s9.ecc4ded3a3a9 from=translated src=- shape=6158442b vocab=6dd946ae
-/
theorem emb_apply (φ : F →+* ℂ) (x : F ≃ₐ[ℚ] F) (k : fixK H) : emb H φ x k = φ (x k) := rfl

omit [IsGalois ℚ F] in
/--
@isnad1 id=iff.0h3v.s9.4626e877c39a from=translated src=- shape=d5192ee2 vocab=891cf919
-/
theorem mem_iff_forall_apply (g : F ≃ₐ[ℚ] F) : g ∈ H ↔ ∀ k : fixK H, g k = k := by
  constructor
  · intro hg k
    exact k.2 ⟨g, hg⟩
  · intro hg
    rw [← IntermediateField.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    exact hg ⟨z, hz⟩

omit [IsGalois ℚ F] in
/--
@isnad1 id=iff.0h5v.s10.a7fd2af9396f from=translated src=- shape=c88b4179 vocab=be7eba03
-/
theorem emb_eq_iff (φ : F →+* ℂ) (x y : F ≃ₐ[ℚ] F) : emb H φ x = emb H φ y ↔ x⁻¹ * y ∈ H := by
  rw [mem_iff_forall_apply]
  constructor
  · intro h k
    have hk := RingHom.congr_fun h k
    rw [emb_apply, emb_apply] at hk
    have hk' : x k = y k := φ.injective hk
    rw [AlgEquiv.mul_apply, ← hk']
    exact x.symm_apply_apply _
  · intro h
    apply RingHom.ext
    intro k
    rw [emb_apply, emb_apply]
    congr 1
    have hk := h k
    rw [AlgEquiv.mul_apply] at hk
    have := congrArg x hk
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
    exact this.symm

omit [IsGalois ℚ F] in
/--
@isnad1 id=iff.1h5v.s10.d7ecee03fa14 from=translated src=- shape=21388730 vocab=e40dc0c6
-/
theorem isReal_emb_iff {φ : F →+* ℂ} {σ : F ≃ₐ[ℚ] F} (hσ : ComplexEmbedding.IsConj φ σ)
    (x : F ≃ₐ[ℚ] F) : ComplexEmbedding.IsReal (emb H φ x) ↔ x⁻¹ * σ * x ∈ H := by
  have hx := hσ.comp x
  rw [mem_iff_forall_apply]
  constructor
  · intro hreal k
    apply (φ.comp (x : F →+* F)).injective
    rw [hx.eq]
    exact RingHom.congr_fun hreal k
  · intro h
    apply RingHom.ext
    intro k
    have h1 := hx.eq (k : F)
    rw [h k] at h1
    exact h1.symm

omit [IsGalois ℚ F] in

/--
@isnad1 id=le.0h4v.s10.baf3f8877e8d from=translated src=- shape=f364473c vocab=d60ed431
-/
theorem card_fiber_le (φ : F →+* ℂ) (ρ : fixK H →+* ℂ) :
    (Finset.univ.filter fun x : F ≃ₐ[ℚ] F => emb H φ x = ρ).card ≤ Fintype.card H := by
  set S := Finset.univ.filter fun x : F ≃ₐ[ℚ] F => emb H φ x = ρ with hS
  rcases S.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · rw [Finset.mem_filter] at hx₀
    have hmem : ∀ y ∈ S, x₀⁻¹ * y ∈ H := fun y hy => by
      rw [Finset.mem_filter] at hy
      exact (emb_eq_iff H φ x₀ y).mp (hx₀.2.trans hy.2.symm)
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun y => if hy : y ∈ S then ⟨x₀⁻¹ * y, hmem y hy⟩ else 1)
      (fun _ _ => Finset.mem_univ _) ?_
    intro y hy y' hy' h
    have hyS : y ∈ S := hy
    have hy'S : y' ∈ S := hy'
    simp only [dite_eq_left hyS, dite_eq_left hy'S, Subtype.mk.injEq] at h
    exact mul_left_cancel h

/--
@isnad1 id=eq.0h2v.s10.ec9b8f91830a from=translated src=- shape=f2bbf680 vocab=9cb5ee8e
-/
theorem card_gal_eq : Fintype.card (F ≃ₐ[ℚ] F) = Fintype.card (fixK H →+* ℂ) * Fintype.card H := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, NumberField.Embeddings.card,
    ← Nat.card_eq_fintype_card (α := H), ← IntermediateField.finrank_fixedField_eq_card H,
    Module.finrank_mul_finrank]

/--
@isnad1 id=eq.0h4v.s10.6e63b505026e from=translated src=- shape=0241adb5 vocab=70ac3183
-/
theorem card_fiber_eq (φ : F →+* ℂ) (ρ : fixK H →+* ℂ) :
    (Finset.univ.filter fun x : F ≃ₐ[ℚ] F => emb H φ x = ρ).card = Fintype.card H := by
  have hsum : ∑ ρ' : fixK H →+* ℂ, (Finset.univ.filter fun x : F ≃ₐ[ℚ] F => emb H φ x = ρ').card =
      ∑ _ρ' : fixK H →+* ℂ, Fintype.card H := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (emb H φ x)),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.card_univ]
    exact card_gal_eq H
  exact (Finset.sum_eq_sum_iff_of_le fun ρ' _ => card_fiber_le H φ ρ').mp hsum ρ (Finset.mem_univ ρ)

/--
@isnad1 id=eq.0h4v.s10.df5e5fd8495a from=translated src=- shape=b33e5c1f vocab=4cf2f8a7
-/
theorem sum_comp_emb (φ : F →+* ℂ) (g : (fixK H →+* ℂ) → ℂ) :
    ∑ x : F ≃ₐ[ℚ] F, g (emb H φ x) = (Nat.card H : ℂ) * ∑ ρ : fixK H →+* ℂ, g ρ := by
  rw [← Finset.sum_fiberwise_of_maps_to' (g := emb H φ) (t := Finset.univ)
    (fun x _ => Finset.mem_univ (emb H φ x)) g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_const, card_fiber_eq H φ ρ, nsmul_eq_mul, Nat.card_eq_fintype_card]

variable (χ : H →* ℂˣ)

abbrev ψχ : (F ≃ₐ[fixK H] F) →* ℂˣ := ArtinL.Abelian.ofSubgroup H χ

def toGalK (g : F ≃ₐ[ℚ] F) (hg : g ∈ H) : F ≃ₐ[fixK H] F :=
  IntermediateField.fixingSubgroupEquiv (fixK H)
    ⟨g, by rw [IntermediateField.fixingSubgroup_fixedField H]; exact hg⟩

omit [IsGalois ℚ F] in
/--
@isnad1 id=eq.1h3v.s9.2b3123082088 from=translated src=- shape=28ce8bc7 vocab=decfc675
-/
theorem coe_toGalK (g : F ≃ₐ[ℚ] F) (hg : g ∈ H) : ((toGalK H g hg : F ≃ₐ[fixK H] F) : F →+* F) =
    (g : F →+* F) := RingHom.ext fun _ => rfl

omit [IsGalois ℚ F] in
/--
@isnad1 id=eq.1h4v.s12.c6fe16a5aec0 from=translated src=- shape=5b62ae16 vocab=5b5a015e
-/
theorem ψχ_toGalK (g : F ≃ₐ[ℚ] F) (hg : g ∈ H) : ψχ H χ (toGalK H g hg) = χ ⟨g, hg⟩ :=
  ArtinL.Abelian.ofSubgroup_fixingSubgroupEquiv H χ ⟨g, hg⟩

omit [IsGalois ℚ F] in

/--
@isnad1 id=eq.2h6v.s10.16c4b74291d4 from=translated src=- shape=06bd82b4 vocab=bd1e8b3d
-/
theorem restrictScalars_eq_of_isConj {φ : F →+* ℂ} {σ : F ≃ₐ[ℚ] F}
    (hσ : ComplexEmbedding.IsConj φ σ) (y : F ≃ₐ[ℚ] F) (τ : F ≃ₐ[fixK H] F)
    (hτ : ComplexEmbedding.IsConj (φ.comp (y : F →+* F)) τ) :
    τ.restrictScalars ℚ = y⁻¹ * σ * y := by
  have h1 : ComplexEmbedding.IsConj (φ.comp (y : F →+* F)) (τ.restrictScalars ℚ) := by
    unfold ComplexEmbedding.IsConj at hτ ⊢
    rw [hτ]
    rfl
  exact h1.ext (hσ.comp y)

/--
@isnad1 id=iff.2h6v.s12.75f589f48662 from=translated src=- shape=0c1c837e vocab=546eaade
-/
theorem isPlusAt_iff {φ : F →+* ℂ} {σ : F ≃ₐ[ℚ] F} (hσ : ComplexEmbedding.IsConj φ σ)
    (x : F ≃ₐ[ℚ] F) (hx : x⁻¹ * σ * x ∈ H) :
    ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk (emb H φ x)) ↔ χ ⟨x⁻¹ * σ * x, hx⟩ = 1 := by
  constructor
  · intro hplus
    have hw : (mk (φ.comp (x : F →+* F))).comap (algebraMap (fixK H) F) = mk (emb H φ x) :=
      comap_mk _ _
    have hτ : toGalK H (x⁻¹ * σ * x) hx ∈
        MulAction.stabilizer (F ≃ₐ[fixK H] F) (mk (φ.comp (x : F →+* F))) := by
      rw [mem_stabilizer_mk_iff]
      right
      unfold ComplexEmbedding.IsConj
      rw [coe_toGalK]
      exact hσ.comp x
    have := hplus _ hw _ hτ
    rwa [ψχ_toGalK] at this
  · intro hχ w hw τ hτ
    obtain ⟨y, hy⟩ := exists_eq_comp φ w.embedding
    rw [← mk_embedding w, hy] at hτ hw
    rw [mem_stabilizer_mk_iff] at hτ
    rcases hτ with hτ | hτ
    · rw [hτ, map_one]
    ·
      have hreal : ComplexEmbedding.IsReal (emb H φ y) := hτ.isReal_comp
      rw [comap_mk] at hw
      change mk (emb H φ y) = mk (emb H φ x) at hw
      rw [mk_eq_iff] at hw
      have hxy : emb H φ y = emb H φ x := by
        rcases hw with hw | hw
        · exact hw
        · rw [← hw]
          exact hreal.symm
      have hh' : x⁻¹ * y ∈ H := (emb_eq_iff H φ x y).mp hxy.symm
      have hτeq : τ.restrictScalars ℚ = y⁻¹ * σ * y := restrictScalars_eq_of_isConj H hσ y τ hτ
      rw [ArtinL.Abelian.ofSubgroup_apply]
      have key : ∀ (g : F ≃ₐ[ℚ] F) (hg : g ∈ H), (∀ z, g z = (y⁻¹ * σ * y) z) → χ ⟨g, hg⟩ = 1 := by
        intro g hg hgz
        have hgeq : g = y⁻¹ * σ * y := AlgEquiv.ext hgz
        have hsub : (⟨g, hg⟩ : H) = ⟨x⁻¹ * y, hh'⟩⁻¹ * ⟨x⁻¹ * σ * x, hx⟩ * ⟨x⁻¹ * y, hh'⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgeq]
          group
        rw [hsub, map_mul, map_mul, map_inv, hχ, mul_one, inv_mul_cancel]
      refine key _ _ fun z => ?_
      rw [← hτeq]
      rfl

omit [IsGalois ℚ F] in
/--
@isnad1 id=or.2h6v.s13.e2ecbdf68d73 from=translated src=- shape=37a6e9e4 vocab=c00ab028
-/
theorem coe_apply_eq_one_or {φ : F →+* ℂ} {σ : F ≃ₐ[ℚ] F} (hσ : ComplexEmbedding.IsConj φ σ)
    (x : F ≃ₐ[ℚ] F) (hx : x⁻¹ * σ * x ∈ H) :
    ((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ) = 1 ∨ ((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ) = -1 := by
  have hsq : (⟨x⁻¹ * σ * x, hx⟩ : H) * ⟨x⁻¹ * σ * x, hx⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    calc x⁻¹ * σ * x * (x⁻¹ * σ * x) = x⁻¹ * (σ * σ) * x := by group
      _ = 1 := by rw [mul_self_eq_one_of_isConj hσ]; group
  have h : ((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ) * ((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hsq, map_one, Units.val_one]
  exact mul_self_eq_one_iff.mp h

def gAux (ρ : fixK H →+* ℂ) : ℂ :=
  if ComplexEmbedding.IsReal ρ then
    (if ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk ρ) then 1 else -1)
  else 0

/--
@isnad1 id=eq.1h6v.s13.622790bbbe11 from=translated src=- shape=bce505ae vocab=0c4ec6de
-/
theorem summand_eq {φ : F →+* ℂ} {σ : F ≃ₐ[ℚ] F} (hσ : ComplexEmbedding.IsConj φ σ)
    (x : F ≃ₐ[ℚ] F) :
    (if hx : x⁻¹ * σ * x ∈ H then (((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ)) else 0) =
      gAux H χ (emb H φ x) := by
  unfold gAux
  by_cases hx : x⁻¹ * σ * x ∈ H
  · rw [dite_eq_left hx, ite_eq_left ((isReal_emb_iff H hσ x).mpr hx)]
    by_cases hplus : ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk (emb H φ x))
    · rw [ite_eq_left hplus, (isPlusAt_iff H χ hσ x hx).mp hplus, Units.val_one]
    · rw [ite_eq_right hplus]
      have hne : χ ⟨x⁻¹ * σ * x, hx⟩ ≠ 1 := fun h => hplus ((isPlusAt_iff H χ hσ x hx).mpr h)
      rcases coe_apply_eq_one_or H χ hσ x hx with h | h
      · exact absurd (Units.val_eq_one.mp h) hne
      · exact h
  · rw [dite_eq_right hx, ite_eq_right (fun h => hx ((isReal_emb_iff H hσ x).mp h))]

omit [IsGalois ℚ F] in

/--
@isnad1 id=eq.0h3v.s11.906f56ee0d3e from=translated src=- shape=7c3e2d3b vocab=56ec7bd6
-/
theorem natCard_real_and (P : InfinitePlace (fixK H) → Prop) :
    Nat.card {v : InfinitePlace (fixK H) // v.IsReal ∧ P v} =
      (Finset.univ.filter fun ρ : fixK H →+* ℂ => ComplexEmbedding.IsReal ρ ∧ P (mk ρ)).card := by
  let e₁ : {ρ : fixK H →+* ℂ // ComplexEmbedding.IsReal ρ ∧ P (mk ρ)} ≃
      {a : {ρ : fixK H →+* ℂ // ComplexEmbedding.IsReal ρ} // P (mk a.1)} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun ρ : fixK H →+* ℂ => ComplexEmbedding.IsReal ρ)
      (fun ρ => P (mk ρ))).symm
  let e₂ : {a : {ρ : fixK H →+* ℂ // ComplexEmbedding.IsReal ρ} // P (mk a.1)} ≃
      {b : {v : InfinitePlace (fixK H) // v.IsReal} // P b.1} :=
    Equiv.subtypeEquiv mkReal fun a => by rw [mkReal_coe]
  let e₃ : {b : {v : InfinitePlace (fixK H) // v.IsReal} // P b.1} ≃
      {v : InfinitePlace (fixK H) // v.IsReal ∧ P v} :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun v : InfinitePlace (fixK H) => v.IsReal) P
  rw [← Nat.card_congr (e₁.trans (e₂.trans e₃)), Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [IsGalois ℚ F] in
/--
@isnad1 id=eq.0h3v.s11.168a33de4c11 from=translated src=- shape=df24101e vocab=7fbfdd51
-/
theorem nPlus_eq :
    ArtinL.Abelian.nPlus (ψχ H χ) = (Finset.univ.filter fun ρ : fixK H →+* ℂ =>
      ComplexEmbedding.IsReal ρ ∧ ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk ρ)).card :=
  natCard_real_and H _

omit [IsGalois ℚ F] in
/--
@isnad1 id=eq.0h3v.s11.d8e8b6d6690d from=translated src=- shape=812b1f23 vocab=f5ab72f9
-/
theorem nMinus_eq :
    ArtinL.Abelian.nMinus (ψχ H χ) = (Finset.univ.filter fun ρ : fixK H →+* ℂ =>
      ComplexEmbedding.IsReal ρ ∧ ¬ ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk ρ)).card := by
  rw [ArtinL.Abelian.nMinus, nPlus_eq, ← card_real_embeddings, Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun ρ : fixK H →+* ℂ => ComplexEmbedding.IsReal ρ)
    (fun ρ : fixK H →+* ℂ => ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk ρ))
  rw [Finset.filter_filter, Finset.filter_filter] at h
  omega

omit [IsGalois ℚ F] in
/--
@isnad1 id=eq.0h3v.s11.6202ab6f8e55 from=translated src=- shape=96e100f0 vocab=30b9843a
-/
theorem sum_gAux :
    ∑ ρ : fixK H →+* ℂ, gAux H χ ρ =
      (ArtinL.Abelian.nPlus (ψχ H χ) : ℂ) - ArtinL.Abelian.nMinus (ψχ H χ) := by
  have h : ∀ ρ : fixK H →+* ℂ, gAux H χ ρ =
      (if ComplexEmbedding.IsReal ρ ∧ ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk ρ) then (1 : ℂ) else 0) -
      (if ComplexEmbedding.IsReal ρ ∧ ¬ ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk ρ) then (1 : ℂ)
        else 0) := by
    intro ρ
    unfold gAux
    by_cases h1 : ComplexEmbedding.IsReal ρ
    · by_cases h2 : ArtinL.Abelian.IsPlusAt (ψχ H χ) (mk ρ)
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, nPlus_eq, nMinus_eq]

/--
@isnad1 id=eq.1h5v.s13.93d9266ffc1e from=translated src=- shape=9f270b4d vocab=f87686e8
-/
theorem main {φ : F →+* ℂ} {σ : F ≃ₐ[ℚ] F} (hσ : ComplexEmbedding.IsConj φ σ) :
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F, (if hx : x⁻¹ * σ * x ∈ H then (((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ)) else 0) =
      (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup H χ) : ℂ) -
        ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup H χ) := by
  simp_rw [summand_eq H χ hσ]
  rw [sum_comp_emb H φ (gAux H χ), ← mul_assoc, inv_mul_cancel₀, one_mul, sum_gAux]
  have : 0 < Nat.card H := Nat.card_pos
  exact_mod_cast this.ne'

end ArtinArchProof

open scoped Classical in

/--
@isnad1 id=eq.1h5v.s13.80aae7d17a2a from=translated src=- shape=ca0d1c67 vocab=f87686e8
-/
theorem solution
    {F : Type u} [Field F] [NumberField F] [IsGalois ℚ F]
    (φ : F →+* ℂ) (σ : F ≃ₐ[ℚ] F) (hσ : ComplexEmbedding.IsConj φ σ)
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) :
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F, (if hx : x⁻¹ * σ * x ∈ H then (((χ ⟨x⁻¹ * σ * x, hx⟩ : ℂˣ) : ℂ)) else 0) =
      (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup H χ) : ℂ) -
        ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup H χ) :=
  ArtinArchProof.main H χ hσ

end
