import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_TateLocal_exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_TateLocal_exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace R1V30MonoFourier

noncomputable section

open LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)

/--
@isnad1 id=ne.0h3v.s8.c5f5a536a425 from=translated src=- shape=d460c066 vocab=491523cf
-/
theorem val_units_ne_zero (u : (v.adicCompletion K)ˣ) :
    Valued.v (u : v.adicCompletion K) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr u.ne_zero

def higherUnitsSubgroup (b : ℕ) : Subgroup (v.adicCompletion K)ˣ where
  carrier := higherUnitsAt K v b
  one_mem' := one_mem_higherUnitsAt K v b
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    refine ⟨by simp [Units.val_mul, map_mul, hx1, hy1], ?_⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact Or.inl hb
    · right
      have hx2' : Valued.v ((x : v.adicCompletion K) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
        rcases hx2 with h | h
        · omega
        · exact h
      have hy2' : Valued.v ((y : v.adicCompletion K) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
        rcases hy2 with h | h
        · omega
        · exact h
      have hsplit : ((x * y : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          (x : v.adicCompletion K) * ((y : v.adicCompletion K) - 1) + ((x : v.adicCompletion K) - 1) := by
        push_cast; ring
      rw [hsplit]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ hx2')
      rw [map_mul, hx1, one_mul]
      exact hy2'
  inv_mem' := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have hinv : Valued.v ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx1, inv_one]
    refine ⟨hinv, ?_⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact Or.inl hb
    · right
      have hx2' : Valued.v ((x : v.adicCompletion K) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
        rcases hx2 with h | h
        · omega
        · exact h
      have hsplit : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          -(((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * ((x : v.adicCompletion K) - 1)) := by
        rw [mul_sub, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        ring
      rw [hsplit, Valuation.map_neg, map_mul, hinv, one_mul]
      exact hx2'

/--
@isnad1 id=iff.0h4v.s10.ee6273006afb from=translated src=- shape=aff1a0a8 vocab=9d18ac56
-/
theorem mem_higherUnitsSubgroup_iff (b : ℕ) (u : (v.adicCompletion K)ˣ) :
    u ∈ higherUnitsSubgroup K v b ↔ u ∈ higherUnitsAt K v b := Iff.rfl

/--
@isnad1 id=mem.2h4v.s10.3284f54e0878 from=translated src=- shape=0038edc8 vocab=cc59728e
-/
theorem mem_higherUnitsAt_of_le (b : ℕ) (u : (v.adicCompletion K)ˣ)
    (h1 : Valued.v (u : v.adicCompletion K) = 1)
    (h2 : Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(b : ℤ))) :
    u ∈ higherUnitsAt K v b :=
  ⟨h1, Or.inr h2⟩

/--
@isnad1 id=ex.0h2v.s8.7cbf3163ff8b from=translated src=- shape=b7e3e0a4 vocab=1fd751c4
-/
theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  refine ⟨((WithVal.equiv (v.valuation K)).symm π : v.adicCompletion K), ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hπ

section WithUniformizer

variable {K v}
variable (ϖu : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖu : v.adicCompletion K) = WithZero.exp (-1 : ℤ))

def retract : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ where
  toFun x := x * ϖu ^ (WithZero.log (Valued.v (x : v.adicCompletion K)))
  map_one' := by simp
  map_mul' x y := by
    have hx := val_units_ne_zero K v x
    have hy := val_units_ne_zero K v y
    rw [Units.val_mul, map_mul, WithZero.log_mul hx hy, zpow_add]
    simp only [mul_mul_mul_comm]

/--
@isnad1 id=eq.0h4v.s11.b6deae86737c from=translated src=- shape=d11fa688 vocab=be23f338
-/
theorem retract_apply (x : (v.adicCompletion K)ˣ) :
    retract ϖu x = x * ϖu ^ (WithZero.log (Valued.v (x : v.adicCompletion K))) := rfl

include hϖ in
/--
@isnad1 id=eq.1h4v.s11.b11f0d9eda6a from=translated src=- shape=6fed34f0 vocab=8f19cd9e
-/
theorem val_retract (x : (v.adicCompletion K)ˣ) :
    Valued.v ((retract ϖu x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  have hx := val_units_ne_zero K v x
  rw [retract_apply]
  set n : ℤ := WithZero.log (Valued.v (x : v.adicCompletion K)) with hn
  have hvx : Valued.v (x : v.adicCompletion K) = WithZero.exp n := by
    rw [hn, WithZero.exp_log hx]
  rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul,
    smul_neg, zsmul_eq_mul, mul_one, Int.cast_id, hvx, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/--
@isnad1 id=eq.1h4v.s11.a662ea24c574 from=translated src=- shape=f21aa711 vocab=f723fcbc
-/
theorem retract_of_val_eq_one (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    retract ϖu u = u := by
  rw [retract_apply, hu, WithZero.log_one, zpow_zero, mul_one]

include hϖ in
/--
@isnad1 id=eq.1h3v.s11.f60d229d5883 from=translated src=- shape=31ad1c80 vocab=8f19cd9e
-/
theorem retract_uniformizer : retract ϖu ϖu = 1 := by
  rw [retract_apply, hϖ, WithZero.log_exp]
  simp

def bigSubgroup (b : ℕ) : Subgroup (v.adicCompletion K)ˣ :=
  higherUnitsSubgroup K v b ⊔ Subgroup.zpowers ϖu

/--
@isnad1 id=mem.1h5v.s10.8a5c021114ce from=translated src=- shape=bf407245 vocab=ae7fea20
-/
theorem mem_bigSubgroup_of_mem_higherUnitsAt (b : ℕ) {h : (v.adicCompletion K)ˣ}
    (hh : h ∈ higherUnitsAt K v b) : h ∈ bigSubgroup ϖu b :=
  Subgroup.mem_sup_left ((mem_higherUnitsSubgroup_iff K v b h).mpr hh)

/--
@isnad1 id=mem.0h4v.s9.576aa0dd663f from=translated src=- shape=1d60e0c5 vocab=36a534a5
-/
theorem uniformizer_mem_bigSubgroup (b : ℕ) : ϖu ∈ bigSubgroup ϖu b :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers ϖu)

/--
@isnad1 id=iff.0h3v.s8.30f1a22e0ed4 from=translated src=- shape=53317f01 vocab=e150e977
-/
theorem val_eq_one_iff_norm_eq_one (x : v.adicCompletion K) :
    Valued.v x = 1 ↔ ‖x‖ = 1 := by
  constructor
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mpr h.le
    · exact Valued.toNormedField.one_le_norm_iff.mpr h.ge
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mp h.le
    · exact Valued.toNormedField.one_le_norm_iff.mp h.ge

include hϖ in
/--
@isnad1 id=finite.1h4v.s9.95643c50dfe4 from=translated src=- shape=ab2b2ee2 vocab=06949f2b
-/
theorem finite_quotient_bigSubgroup (b : ℕ) :
    Finite ((v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b) := by

  have hS : IsCompact (Metric.sphere (0 : v.adicCompletion K) 1) := isCompact_sphere _ _

  have hϖ0 : (ϖu : v.adicCompletion K) ≠ 0 := ϖu.ne_zero
  set r : ℝ := ‖(ϖu : v.adicCompletion K) ^ b‖ with hr
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr (pow_ne_zero _ hϖ0)
  obtain ⟨t, htS, htfin, hcover⟩ := hS.finite_cover_balls hrpos

  have htne : ∀ x ∈ t, x ≠ 0 := by
    intro x hx h0
    have := htS hx
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
    exact zero_ne_one this

  let f : t → (v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b := fun x =>
    QuotientGroup.mk (Units.mk0 (x : v.adicCompletion K) (htne x x.2))
  haveI : Finite t := htfin.to_subtype
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>

    set u := retract ϖu x with hu
    have hu1 : Valued.v (u : v.adicCompletion K) = 1 := val_retract ϖu hϖ x
    have huS : (u : v.adicCompletion K) ∈ Metric.sphere (0 : v.adicCompletion K) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact (val_eq_one_iff_norm_eq_one (u : v.adicCompletion K)).mp hu1
    obtain ⟨y, hy, hyball⟩ : ∃ y ∈ t, (u : v.adicCompletion K) ∈ Metric.ball y r := by
      have := hcover huS
      simpa only [Set.mem_iUnion, exists_prop] using this
    refine ⟨⟨y, hy⟩, ?_⟩

    have hy0 : y ≠ 0 := htne y hy
    have hy1 : Valued.v y = 1 := by
      have := htS hy
      rw [mem_sphere_zero_iff_norm] at this
      exact (val_eq_one_iff_norm_eq_one y).mpr this

    have hxu : (QuotientGroup.mk x : (v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b) = QuotientGroup.mk u := by
      rw [QuotientGroup.eq, hu, retract_apply, ← mul_assoc, inv_mul_cancel, one_mul]
      exact Subgroup.zpow_mem _ (uniformizer_mem_bigSubgroup ϖu b) _
    change (QuotientGroup.mk (Units.mk0 y hy0) : (v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b) = QuotientGroup.mk x
    rw [hxu, QuotientGroup.eq]
    apply mem_bigSubgroup_of_mem_higherUnitsAt
    apply mem_higherUnitsAt_of_le
    · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_mk0, hy1, inv_one, one_mul, hu1]
    ·
      have hsplit : (((Units.mk0 y hy0)⁻¹ * u : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          y⁻¹ * ((u : v.adicCompletion K) - y) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, mul_sub, inv_mul_cancel₀ hy0]
      rw [hsplit, map_mul, map_inv₀, hy1, inv_one, one_mul]
      have hlt : ‖(u : v.adicCompletion K) - y‖ < ‖(ϖu : v.adicCompletion K) ^ b‖ := by
        rw [← dist_eq_norm]; exact hyball
      have hlt' := Valued.toNormedField.norm_lt_iff.mp hlt
      rw [map_pow, hϖ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one] at hlt'
      exact hlt'.le

/--
@isnad1 id=ex.1h4v.s10.243d3e0ea688 from=translated src=- shape=2cc2d18a vocab=bd059683
-/
theorem exists_hasConductorExponentAt_le (b : ℕ) (η : (v.adicCompletion K)ˣ →* ℂˣ)
    (hη : ∀ h ∈ higherUnitsAt K v b, η h = 1) :
    ∃ m ≤ b, HasConductorExponentAt K v η m := by
  classical
  have hex : ∃ m, ∀ h ∈ higherUnitsAt K v m, η h = 1 := ⟨b, hη⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hη, Nat.find_spec hex, ?_⟩
  intro m hm
  have := Nat.find_min hex hm
  push Not at this
  exact this

end WithUniformizer

section Abstract

variable {G : Type*} [CommGroup G]

def charHom {Q : Type*} [CommGroup Q] (θ : AddChar (Additive Q) ℂ) : Q →* ℂ where
  toFun q := θ (Additive.ofMul q)
  map_one' := θ.map_zero_eq_one
  map_mul' a c := θ.map_add_eq_mul (Additive.ofMul a) (Additive.ofMul c)

def pullChar (P : Subgroup G) (θ : AddChar (Additive (G ⧸ P)) ℂ) : G →* ℂˣ :=
  (charHom θ).toHomUnits.comp (QuotientGroup.mk' P)

/--
@isnad1 id=eq.0h4v.s8.dda32571e6f7 from=translated src=- shape=11578e1d vocab=015bbb75
-/
theorem pullChar_apply (P : Subgroup G) (θ : AddChar (Additive (G ⧸ P)) ℂ) (x : G) :
    ((pullChar P θ x : ℂˣ) : ℂ) = θ (Additive.ofMul (QuotientGroup.mk x : G ⧸ P)) :=
  rfl

/--
@isnad1 id=eq.1h4v.s7.3e86e503a39b from=translated src=- shape=4ca0b96a vocab=adf6b45d
-/
theorem pullChar_eq_one_of_mem (P : Subgroup G) (θ : AddChar (Additive (G ⧸ P)) ℂ)
    {h : G} (hh : h ∈ P) : pullChar P θ h = 1 := by
  apply Units.ext
  rw [pullChar_apply, Units.val_one]
  have : (QuotientGroup.mk h : G ⧸ P) = 1 := (QuotientGroup.eq_one_iff h).mpr hh
  rw [this, ofMul_one, AddChar.map_zero_eq_one]

/--
@isnad1 id=eq.0h4v.s7.5e858faa84de from=translated src=- shape=d673581b vocab=a19a4334
-/
theorem norm_pullChar (P : Subgroup G) [Finite (G ⧸ P)] (θ : AddChar (Additive (G ⧸ P)) ℂ) (x : G) :
    ‖((pullChar P θ x : ℂˣ) : ℂ)‖ = 1 := by
  rw [pullChar_apply]
  exact AddChar.norm_apply θ _

/--
@isnad1 id=injectiv.0h2v.s6.0537f7e398f2 from=translated src=- shape=50692f4a vocab=22d22278
-/
theorem pullChar_injective (P : Subgroup G) : Function.Injective (pullChar P) := by
  intro θ₁ θ₂ h12
  apply AddChar.ext
  intro a
  obtain ⟨x, hx⟩ : ∃ x : G, (QuotientGroup.mk x : G ⧸ P) = Additive.toMul a :=
    QuotientGroup.mk_surjective (Additive.toMul a)
  have := congr_arg (fun η : G →* ℂˣ => ((η x : ℂˣ) : ℂ)) h12
  simp only [pullChar_apply, hx, ofMul_toMul] at this
  exact this

/--
@isnad1 id=ex.2h3v.s9.a5d38b7929e8 from=translated src=- shape=46d669c3 vocab=dc27cab1
-/
theorem abstract_expansion (P : Subgroup G) (hP : Finite (G ⧸ P)) (f : G → ℂ)
    (hf : ∀ x p : G, p ∈ P → f (x * p) = f x) :
    ∃ (S : Finset (G →* ℂˣ)) (c : (G →* ℂˣ) → ℂ),
      (∀ η ∈ S, ∀ p ∈ P, η p = 1) ∧
      (∀ η ∈ S, ∀ x : G, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ x : G, f x = ∑ η ∈ S, c η * ((η x : ℂˣ) : ℂ) := by
  classical
  haveI := hP

  have hfbar_mk : ∀ x : G, f ((QuotientGroup.mk x : G ⧸ P).out) = f x := by
    intro x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P x
    rw [hp]
    exact hf x p p.2

  set B := AddChar.complexBasis (Additive (G ⧸ P)) with hB
  set fa : Additive (G ⧸ P) → ℂ := fun a => f (Additive.toMul a).out with hfa
  have hexp : ∀ q : G ⧸ P,
      f q.out = ∑ θ : AddChar (Additive (G ⧸ P)) ℂ, B.repr fa θ * θ (Additive.ofMul q) := by
    intro q
    have h := congr_fun (B.sum_repr fa) (Additive.ofMul q)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hB, AddChar.complexBasis_apply] at h
    rw [hB]
    exact h.symm
  refine ⟨Finset.univ.image (pullChar P),
    fun η => if h : ∃ θ, pullChar P θ = η then B.repr fa h.choose else 0, ?_, ?_, ?_⟩
  · intro η hη
    rw [Finset.mem_image] at hη
    obtain ⟨θ, -, rfl⟩ := hη
    exact fun p hp => pullChar_eq_one_of_mem P θ hp
  · intro η hη x
    rw [Finset.mem_image] at hη
    obtain ⟨θ, -, rfl⟩ := hη
    exact norm_pullChar P θ x
  · intro x
    rw [Finset.sum_image (fun θ₁ _ θ₂ _ h => pullChar_injective P h), ← hfbar_mk x, hexp]
    refine Finset.sum_congr rfl fun θ _ => ?_
    have hex : ∃ θ', pullChar P θ' = pullChar P θ := ⟨θ, rfl⟩
    simp only [dite_eq_left hex]
    rw [pullChar_injective P hex.choose_spec, pullChar_apply]

end Abstract

section Final

variable {K v}
variable (ϖu : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖu : v.adicCompletion K) = WithZero.exp (-1 : ℤ))

include hϖ in
/--
@isnad1 id=ex.2h5v.s13.6149cbbf98d3 from=translated src=- shape=8c96ba5a vocab=fa48297d
-/
theorem expansion (b : ℕ) (g : (v.adicCompletion K)ˣ → ℂ)
    (hg : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ h ∈ higherUnitsAt K v b, g (u * h) = g u) :
    ∃ (S : Finset ((v.adicCompletion K)ˣ →* ℂˣ)) (c : ((v.adicCompletion K)ˣ →* ℂˣ) → ℂ),
      (∀ η ∈ S, ∃ m ≤ b, HasConductorExponentAt K v η m) ∧
      (∀ η ∈ S, ∀ x : (v.adicCompletion K)ˣ, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        g u = ∑ η ∈ S, c η * ((η u : ℂˣ) : ℂ) := by

  have hg'inv : ∀ (x p : (v.adicCompletion K)ˣ), p ∈ bigSubgroup ϖu b →
      g (retract ϖu (x * p)) = g (retract ϖu x) := by
    intro x p hp
    rw [bigSubgroup, Subgroup.mem_sup] at hp
    obtain ⟨h, hh, z, hz, rfl⟩ := hp
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    have hh' : h ∈ higherUnitsAt K v b := (mem_higherUnitsSubgroup_iff K v b h).mp hh
    rw [map_mul, map_mul, map_zpow, retract_uniformizer ϖu hϖ, one_zpow, mul_one,
      retract_of_val_eq_one ϖu h hh'.1]
    exact hg _ (val_retract ϖu hϖ x) h hh'
  obtain ⟨S, c, hS1, hS2, hS3⟩ := abstract_expansion (bigSubgroup ϖu b)
    (finite_quotient_bigSubgroup ϖu hϖ b) (fun x => g (retract ϖu x)) hg'inv
  refine ⟨S, c, ?_, hS2, ?_⟩
  · intro η hη
    exact exists_hasConductorExponentAt_le b η
      (fun h hh => hS1 η hη h (mem_bigSubgroup_of_mem_higherUnitsAt ϖu b hh))
  · intro u hu
    have := hS3 u
    rwa [retract_of_val_eq_one ϖu u hu] at this

end Final

end

end R1V30MonoFourier

open LanglandsTunnell.TateLocal in
/--
@isnad1 id=ex.1h4v.s13.6d08bc4dffc0 from=translated src=- shape=7319862f vocab=dd4c6f3a
-/
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (b : ℕ)
    (g : (v.adicCompletion K)ˣ → ℂ)
    (hg : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v b, g (u * h) = g u) :
    ∃ (S : Finset ((v.adicCompletion K)ˣ →* ℂˣ)) (c : ((v.adicCompletion K)ˣ →* ℂˣ) → ℂ),
      (∀ η ∈ S, ∃ m ≤ b, LanglandsTunnell.TateLocal.HasConductorExponentAt K v η m) ∧
      (∀ η ∈ S, ∀ x : (v.adicCompletion K)ˣ, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        g u = ∑ η ∈ S, c η * ((η u : ℂˣ) : ℂ) := by
  obtain ⟨ϖ, hϖ⟩ := R1V30MonoFourier.exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  exact R1V30MonoFourier.expansion (Units.mk0 ϖ hϖ0) (by simpa using hϖ) b g hg
