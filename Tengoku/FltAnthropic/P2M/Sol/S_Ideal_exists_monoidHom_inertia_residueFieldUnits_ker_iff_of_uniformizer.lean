import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer
set_option autoImplicit false

universe u v

namespace GaloisRep
namespace TameKernel

section Core
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]

/--
@isnad1 id=mem.2h5v.s7.48d0ab0f2fc2 from=translated src=- shape=55e5eea4 vocab=db64b554
-/
theorem smul_mem_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓) : σ • z ∈ 𝔓 := by
  have h : σ • z - z ∈ 𝔓 := hσ z
  have : σ • z = (σ • z - z) + z := by ring
  rw [this]; exact 𝔓.add_mem h hz

/--
@isnad1 id=mem.2h5v.s8.c284607e1cf9 from=translated src=- shape=3a7baf2b vocab=cac09bc3
-/
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

/--
@isnad1 id=mem.3h5v.s8.a8b9704d3c45 from=translated src=- shape=03fc7848 vocab=bddda5d5
-/
theorem pow_sub_pow_mem_sq (𝔓 : Ideal B) {a b : B} (hab : a - b ∈ 𝔓) {N : ℕ} (hN : (N : B) ∈ 𝔓) (hN0 : N ≠ 0) :
    a ^ N - b ^ N ∈ 𝔓 ^ 2 := by
  set m := a - b with hm
  have ha : a = b + m := by rw [hm]; ring
  rw [ha, add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  rcases Nat.lt_or_ge (N - k) 2 with hlt | hge
  ·
    have hk1 : N - k = 1 := by omega
    have hkN : k = N - 1 := by omega
    have hch : (N.choose k : B) = N := by
      rw [hkN, Nat.choose_symm (by omega : 1 ≤ N), Nat.choose_one_right]
    rw [hk1, pow_one, hch, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hab) hN
  ·
    have : m ^ (N - k) ∈ 𝔓 ^ 2 := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      rw [hj, pow_add]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hab 2)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ this)

/--
@isnad1 id=mem.4h6v.s9.32ba9be9ce19 from=translated src=- shape=7c900547 vocab=d63f60d2
-/
theorem smul_sub_mem_sq_of_mem_inertia (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)]
    {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hϖ : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    {σ : G} (hσ : σ ∈ 𝔓.inertia G) (hσϖ : σ • ϖ - ϖ ∈ 𝔓 ^ 2) (x : B) :
    σ • x - x ∈ 𝔓 ^ 2 := by
  classical
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  letI : Fintype (B ⧸ 𝔓) := Fintype.ofFinite _
  set N := Fintype.card (B ⧸ 𝔓) with hNdef

  have hN : (N : B) ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hNdef]
    exact Nat.cast_card_eq_zero (B ⧸ 𝔓)
  have hN0 : N ≠ 0 := Fintype.card_ne_zero

  have hF : x ^ N - x ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hNdef, FiniteField.pow_card, sub_self]

  obtain ⟨y, hy⟩ := hϖ (x - x ^ N) (by rw [← neg_sub]; exact 𝔓.neg_mem hF)
  set e := x - x ^ N - ϖ * y with he
  have hx : x = x ^ N + ϖ * y + e := by rw [he]; ring

  have h1 : σ • (x ^ N) - x ^ N ∈ 𝔓 ^ 2 := by
    rw [smul_pow']
    exact pow_sub_pow_mem_sq 𝔓 (hσ x) hN hN0
  have h2 : σ • (ϖ * y) - ϖ * y ∈ 𝔓 ^ 2 := by
    have : σ • (ϖ * y) - ϖ * y = (σ • ϖ - ϖ) * (σ • y) + ϖ * (σ • y - y) := by
      rw [smul_mul']; ring
    rw [this]
    refine 𝔓 ^ 2 |>.add_mem (Ideal.mul_mem_right _ _ hσϖ) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hϖP (hσ y)
  have h3 : σ • e - e ∈ 𝔓 ^ 2 := (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) hy
  have : σ • x - x = (σ • (x ^ N) - x ^ N) + (σ • (ϖ * y) - ϖ * y) + (σ • e - e) := by
    conv_lhs => rw [hx]
    rw [smul_add, smul_add]; ring
  rw [this]
  exact (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem h1 h2) h3

end Core

section TameChar
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B) [𝔓.IsMaximal]
variable {ϖ : B}

/--
@isnad1 id=ex.3h5v.s9.ff3bf562d6cd from=translated src=- shape=14c155d4 vocab=0159ffe0
-/
theorem exists_tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : ∃ t : B, σ • ϖ - ϖ * t ∈ 𝔓 ^ 2 :=
  hgen (σ • ϖ) (smul_mem_of_mem_inertia 𝔓 hσ hϖP)

noncomputable def tameCoeff (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : B := (exists_tameCoeff 𝔓 hϖP hgen hσ).choose

/--
@isnad1 id=mem.3h5v.s9.cb21d594ce26 from=translated src=- shape=c373a2bb vocab=4b1f274a
-/
theorem tameCoeff_spec (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) : σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 :=
  (exists_tameCoeff 𝔓 hϖP hgen hσ).choose_spec

/--
@isnad1 id=mem.3h6v.s9.5ac5d50a70bf from=translated src=- shape=66681869 vocab=377380f6
-/
theorem tameCoeff_unique (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {z t t' : B} (ht : z - ϖ * t ∈ 𝔓 ^ 2) (ht' : z - ϖ * t' ∈ 𝔓 ^ 2) : t - t' ∈ 𝔓 := by
  apply hreg
  have : (t - t') * ϖ = (z - ϖ * t') - (z - ϖ * t) := by ring
  rw [this]
  exact (𝔓 ^ 2).sub_mem ht' ht

/--
@isnad1 id=not.4h5v.s9.fd1cce3e3b7f from=translated src=- shape=77fbe550 vocab=e203b480
-/
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

/--
@isnad1 id=eq.3h5v.s9.3584c57e5244 from=translated src=- shape=54af1813 vocab=4f4e0f79
-/
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

/--
@isnad1 id=eq.3h5v.s10.354174c1e8bd from=translated src=- shape=c4d861df vocab=c7214fe0
-/
theorem tameChar_apply (σ : 𝔓.inertia G) :
    ((tameChar (G := G) 𝔓 hϖP hgen hreg σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl

/--
@isnad1 id=iff.3h5v.s10.c5914e19edb6 from=translated src=- shape=79fccec3 vocab=c86d24cc
-/
theorem tameChar_eq_one_iff (σ : 𝔓.inertia G) :
    tameChar 𝔓 hϖP hgen hreg σ = 1 ↔ (σ : G) • ϖ - ϖ ∈ 𝔓 ^ 2 := by
  rw [← Units.val_eq_one, tameChar_apply, ← map_one (Ideal.Quotient.mk 𝔓), Ideal.Quotient.eq]
  constructor
  · intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have : (σ : G) • ϖ - ϖ = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2) + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - 1) := by
      ring
    rw [this]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; exact Ideal.mul_mem_mul hϖP h
  · intro h
    exact tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2) (by rwa [mul_one])

/--
@isnad1 id=iff.3h5v.s10.a9264c678ae4 from=translated src=- shape=ed31d2fe vocab=4b0cd59a
-/
theorem tameChar_eq_one_iff_forall [Finite (B ⧸ 𝔓)] (σ : 𝔓.inertia G) :
    tameChar 𝔓 hϖP hgen hreg σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2 := by
  rw [tameChar_eq_one_iff]
  exact ⟨fun h x => smul_sub_mem_sq_of_mem_inertia 𝔓 hϖP hgen σ.2 h x, fun h => h ϖ⟩

/--
@isnad1 id=iscyclic.3h4v.s10.eb8e8378e2a3 from=translated src=- shape=594c637e vocab=7029c948
-/
theorem isCyclic_range_tameChar [Finite (B ⧸ 𝔓)] : IsCyclic (tameChar (G := G) 𝔓 hϖP hgen hreg).range := by
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  exact isCyclic_of_injective_ringHom ((Units.coeHom (B ⧸ 𝔓)).comp (tameChar (G := G) 𝔓 hϖP hgen hreg).range.subtype)
    (Units.val_injective.comp Subtype.val_injective)

end TameChar

section Higher
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)

end Higher

section FrobeniusRelation
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)

/--
@isnad1 id=ex.3h4v.s12.5045802db7f8 from=translated src=- shape=290c71ad vocab=d264f356
-/
theorem exists_tameChar [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B), ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
        (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧ IsCyclic θ.range := by
  refine ⟨tameChar 𝔓 hϖP hgen hreg, fun σ t => ?_, fun σ => tameChar_eq_one_iff_forall 𝔓 hϖP hgen hreg σ,
    isCyclic_range_tameChar 𝔓 hϖP hgen hreg⟩
  rw [tameChar_apply, Ideal.Quotient.eq]
  constructor
  · intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have : (σ : G) • ϖ - ϖ * t = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2) + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - t) := by
      ring
    rw [this]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; exact Ideal.mul_mem_mul hϖP h
  · intro h
    exact tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2) h

end FrobeniusRelation

end GaloisRep.TameKernel

open GaloisRep.TameKernel in
/--
@isnad1 id=ex.3h4v.s12.5045802db7f8 from=translated src=- shape=290c71ad vocab=d264f356
-/
theorem solution {B : Type u} [CommRing B] {G : Type v} [Group G]
    [MulSemiringAction G B] (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B), ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
        (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧ IsCyclic θ.range :=
  GaloisRep.TameKernel.exists_tameChar 𝔓 hϖP hgen hreg
