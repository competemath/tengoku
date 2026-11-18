import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_conj_smul_sub_mul_pow_mem_sq_of_frobenius.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_conj_smul_sub_mul_pow_mem_sq_of_frobenius.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_conj_smul_sub_mul_pow_mem_sq_of_frobenius
set_option autoImplicit false

universe u v

namespace GaloisRep
namespace TameKernel

section Core
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]

theorem smul_mem_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓) : σ • z ∈ 𝔓 := by
  have h : σ • z - z ∈ 𝔓 := hσ z
  have : σ • z = (σ • z - z) + z := by ring
  rw [this]; exact 𝔓.add_mem h hz

theorem smul_mem_sq_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓 ^ 2) :
    σ • z ∈ 𝔓 ^ 2 := by

  let f : B →+* B := MulSemiringAction.toRingHom G B σ
  have hmap : 𝔓.map f ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz'
    exact smul_mem_of_mem_inertia 𝔓 hσ hz'
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap 2
  exact h2 (Ideal.mem_map_of_mem f hz)

end Core

section TameChar
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B) [𝔓.IsMaximal]
variable {ϖ : B}

theorem exists_tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : ∃ t : B, σ • ϖ - ϖ * t ∈ 𝔓 ^ 2 :=
  hgen (σ • ϖ) (smul_mem_of_mem_inertia 𝔓 hσ hϖP)

noncomputable def tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : B := (exists_tameCoeff 𝔓 hϖP hgen hσ).choose

theorem tameCoeff_spec (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 :=
  (exists_tameCoeff 𝔓 hϖP hgen hσ).choose_spec

theorem tameCoeff_unique (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {z t t' : B} (ht : z - ϖ * t ∈ 𝔓 ^ 2) (ht' : z - ϖ * t' ∈ 𝔓 ^ 2) : t - t' ∈ 𝔓 := by
  apply hreg
  have : (t - t') * ϖ = (z - ϖ * t') - (z - ϖ * t) := by ring
  rw [this]
  exact (𝔓 ^ 2).sub_mem ht' ht

theorem tameCoeff_not_mem (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : tameCoeff 𝔓 hϖP hgen hσ ∉ 𝔓 := by
  intro ht

  have h1 : σ • ϖ ∈ 𝔓 ^ 2 := by
    have h := tameCoeff_spec 𝔓 hϖP hgen hσ
    have h2 : ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hϖP ht
    have : σ • ϖ = (σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ) + ϖ * tameCoeff 𝔓 hϖP hgen hσ := by ring
    rw [this]; exact (𝔓 ^ 2).add_mem h h2
  have h2 : ϖ ∈ 𝔓 ^ 2 := by
    have := smul_mem_sq_of_mem_inertia 𝔓 (Subgroup.inv_mem _ hσ) h1
    rwa [inv_smul_smul] at this
  have h3 : (1 : B) ∈ 𝔓 := hreg 1 (by rwa [one_mul])
  exact Ideal.IsPrime.one_notMem (by infer_instance) h3 |> absurd <| by trivial

noncomputable def tameCharFun (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) : (B ⧸ 𝔓)ˣ :=
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  Units.mk0 (Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2))
    (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact tameCoeff_not_mem 𝔓 hϖP hgen hreg σ.2)

theorem val_tameCharFun (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) :
    ((tameCharFun 𝔓 hϖP hgen hreg σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl

noncomputable def tameChar (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) : (𝔓.inertia G) →* (B ⧸ 𝔓)ˣ where
  toFun := tameCharFun 𝔓 hϖP hgen hreg
  map_one' := by
    apply Units.ext
    rw [val_tameCharFun, Units.val_one, ← map_one (Ideal.Quotient.mk 𝔓), Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_
    simp
  map_mul' := by
    intro σ τ
    apply Units.ext
    rw [Units.val_mul, val_tameCharFun, val_tameCharFun, val_tameCharFun, ← map_mul, Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_

    set tσ := tameCoeff 𝔓 hϖP hgen σ.2
    set tτ := tameCoeff 𝔓 hϖP hgen τ.2
    have hτ := tameCoeff_spec 𝔓 hϖP hgen τ.2
    have hσ := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have e1 : ((σ * τ : 𝔓.inertia G) : G) • ϖ = (σ : G) • ((τ : G) • ϖ) := mul_smul _ _ _

    have e2 : (σ : G) • ((τ : G) • ϖ) = (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + ((σ : G) • ϖ) * ((σ : G) • tτ) := by
      rw [← smul_mul', ← smul_add]; congr 1; ring
    have hA : (σ : G) • ((τ : G) • ϖ - ϖ * tτ) ∈ 𝔓 ^ 2 := smul_mem_sq_of_mem_inertia 𝔓 σ.2 hτ

    have e3 : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
        = ((σ : G) • ϖ - ϖ * tσ) * ((σ : G) • tτ) + ϖ * (tσ * ((σ : G) • tτ - tτ)) := by ring
    have hB : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ) ∈ 𝔓 ^ 2 := by
      rw [e3]
      refine (𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ hσ) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hϖP (Ideal.mul_mem_left _ _ (σ.2 tτ))
    rw [e1, e2]
    have : (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
        = (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + (((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)) := by ring
    rw [this]
    exact (𝔓 ^ 2).add_mem hA hB

variable (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
  (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓)

end TameChar

section Higher
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)

end Higher

section FrobeniusRelation
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)

theorem smul_sub_mul_mem_sq_of_uniformizer {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {x : B} (hx : x ∈ 𝔓) : σ • x - t * x ∈ 𝔓 ^ 2 := by
  obtain ⟨y, hy⟩ := hgen x hx
  set p₂ := x - ϖ * y with hp
  have hx' : x = ϖ * y + p₂ := by rw [hp]; ring
  have e : σ • x - t * x = (σ • ϖ - ϖ * t) * (σ • y) + t * ϖ * (σ • y - y) + (σ • p₂ - t * p₂) := by
    conv_lhs => rw [hx']
    rw [smul_add, smul_mul']; ring
  rw [e]
  refine (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ ht) ?_) ?_
  · rw [pow_two]; exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖP) (hσ y)
  · exact (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) (Ideal.mul_mem_left _ _ hy)

theorem smul_mem_sq_of_forall_smul_mem {φ : G} (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) {z : B} (hz : z ∈ 𝔓 ^ 2) :
    φ • z ∈ 𝔓 ^ 2 := by
  let f : B →+* B := MulSemiringAction.toRingHom G B φ
  have hmap : 𝔓.map f ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hφP x hx
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap 2
  exact h2 (Ideal.mem_map_of_mem f hz)

theorem conj_smul_sub_mul_pow_mem_sq {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {q : ℕ} {φ : G} (hφ : ∀ x : B, φ • x - x ^ q ∈ 𝔓)
    (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) (hφP' : ∀ x ∈ 𝔓, φ⁻¹ • x ∈ 𝔓) :
    (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 := by
  set ϖ₁ := φ⁻¹ • ϖ with hϖ₁
  have hϖ₁P : ϖ₁ ∈ 𝔓 := hφP' ϖ hϖP
  have h1 : σ • ϖ₁ - t * ϖ₁ ∈ 𝔓 ^ 2 := smul_sub_mul_mem_sq_of_uniformizer 𝔓 hϖP hgen hσ ht hϖ₁P
  have h2 : φ • (σ • ϖ₁ - t * ϖ₁) ∈ 𝔓 ^ 2 := smul_mem_sq_of_forall_smul_mem 𝔓 hφP h1
  have e1 : (φ * σ * φ⁻¹) • ϖ = φ • (σ • ϖ₁) := by rw [hϖ₁, mul_smul, mul_smul]
  have e2 : φ • (σ • ϖ₁ - t * ϖ₁) = (φ * σ * φ⁻¹) • ϖ - (φ • t) * ϖ := by
    rw [smul_sub, smul_mul', e1, hϖ₁, smul_inv_smul]
  rw [e2] at h2

  have h3 : (φ • t) * ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 := by
    have : (φ • t) * ϖ - ϖ * t ^ q = (φ • t - t ^ q) * ϖ := by ring
    rw [this, pow_two]; exact Ideal.mul_mem_mul (hφ t) hϖP
  have : (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q = ((φ * σ * φ⁻¹) • ϖ - (φ • t) * ϖ) + ((φ • t) * ϖ - ϖ * t ^ q) := by ring
  rw [this]; exact (𝔓 ^ 2).add_mem h2 h3

end FrobeniusRelation

end GaloisRep.TameKernel

open GaloisRep.TameKernel in
theorem solution {B : Type u} [CommRing B] {G : Type v} [Group G]
    [MulSemiringAction G B] (𝔓 : Ideal B) {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {q : ℕ} {φ : G} (hφ : ∀ x : B, φ • x - x ^ q ∈ 𝔓)
    (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) (hφP' : ∀ x ∈ 𝔓, φ⁻¹ • x ∈ 𝔓) :
    (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 :=
  GaloisRep.TameKernel.conj_smul_sub_mul_pow_mem_sq 𝔓 hϖP hgen hσ ht hφ hφP hφP'
