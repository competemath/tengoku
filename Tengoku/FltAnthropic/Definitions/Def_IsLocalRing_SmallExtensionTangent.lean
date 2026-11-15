import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace IsLocalRing.SmallExtension

variable {T S : Type} [CommRing T] [CommRing S] (σ : T →+* S)

def fibreProd : Subring (T × T) :=
  RingHom.eqLocus (σ.comp (RingHom.fst T T)) (σ.comp (RingHom.snd T T))

/--
@isnad1 id=iff.0h4v.s7.d214e18fd4d2 from=translated src=- shape=10e44c90 vocab=c5eba6d5
-/
theorem mem_fibreProd {x : T × T} : x ∈ fibreProd σ ↔ σ x.1 = σ x.2 := Iff.rfl

def fst : fibreProd σ →+* T := (RingHom.fst T T).comp (fibreProd σ).subtype

def snd : fibreProd σ →+* T := (RingHom.snd T T).comp (fibreProd σ).subtype

/--
@isnad1 id=eq.0h4v.s9.a553a842de45 from=translated src=- shape=b7781cf7 vocab=62c79b7f
-/
@[simp] theorem fst_apply (x : fibreProd σ) : fst σ x = (x : T × T).1 := rfl
/--
@isnad1 id=eq.0h4v.s9.68f7092b1eaa from=translated src=- shape=b7781cf7 vocab=b8897e1c
-/
@[simp] theorem snd_apply (x : fibreProd σ) : snd σ x = (x : T × T).2 := rfl

/--
@isnad1 id=eq.0h4v.s10.cd06c2e25352 from=translated src=- shape=fb901736 vocab=145f6141
-/
theorem apply_fst_eq_apply_snd (x : fibreProd σ) : σ (fst σ x) = σ (snd σ x) := x.2

def diag : T →+* fibreProd σ :=
  ((RingHom.id T).prod (RingHom.id T)).codRestrict (fibreProd σ) (fun _ => rfl)

/--
@isnad1 id=eq.0h4v.s9.ae7652d3602c from=translated src=- shape=411f2952 vocab=062de40c
-/
@[simp] theorem coe_diag (a : T) : ((diag σ a : fibreProd σ) : T × T) = (a, a) := rfl

/--
@isnad1 id=eq.0h4v.s10.419f85649a69 from=translated src=- shape=6c67ce27 vocab=25eb1e84
-/
theorem fst_diag (a : T) : fst σ (diag σ a) = a := rfl
/--
@isnad1 id=eq.0h4v.s10.1f1d1a10e46e from=translated src=- shape=6c67ce27 vocab=4015e6d2
-/
theorem snd_diag (a : T) : snd σ (diag σ a) = a := rfl

def pair (a b : T) (h : σ a = σ b) : fibreProd σ := ⟨(a, b), h⟩

/--
@isnad1 id=eq.1h5v.s9.eaddcdb0e636 from=translated src=- shape=c55b9ec1 vocab=3daa7c98
-/
@[simp] theorem fst_pair (a b : T) (h : σ a = σ b) : fst σ (pair σ a b h) = a := rfl
/--
@isnad1 id=eq.1h5v.s9.06a940cddcc8 from=translated src=- shape=393ea4fd vocab=135d3499
-/
@[simp] theorem snd_pair (a b : T) (h : σ a = σ b) : snd σ (pair σ a b h) = b := rfl

/--
@isnad1 id=iff.0h5v.s11.1a853aafe467 from=translated src=- shape=2fbc1e0b vocab=145f6141
-/
theorem ext_iff {x y : fibreProd σ} : x = y ↔ fst σ x = fst σ y ∧ snd σ x = snd σ y := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; exact Subtype.ext (Prod.ext h1 h2)

/--
@isnad1 id=mem.0h4v.s10.3ffe1ec46f16 from=translated src=- shape=38cd0e96 vocab=e6e1d1f4
-/
theorem snd_sub_fst_mem_ker (x : fibreProd σ) : snd σ x - fst σ x ∈ RingHom.ker σ := by
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]; exact (apply_fst_eq_apply_snd σ x).symm

instance algebra {A : Type} [CommRing A] [Algebra A T] : Algebra A (fibreProd σ) :=
  ((diag σ).comp (algebraMap A T)).toAlgebra

/--
@isnad1 id=eq.0h5v.s10.78b57d864417 from=translated src=- shape=6590318c vocab=bd34bead
-/
theorem algebraMap_eq {A : Type} [CommRing A] [Algebra A T] (a : A) :
    algebraMap A (fibreProd σ) a = diag σ (algebraMap A T a) := rfl

section Local

variable [IsLocalRing T]

def diagMax : Ideal (fibreProd σ) := Ideal.span (diag σ '' (maximalIdeal T : Set T))

/--
@isnad1 id=iff.1h4v.s11.5aec1fe9681c from=translated src=- shape=5cb9fd62 vocab=ea7a89d2
-/
theorem mem_diagMax_iff (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) (x : fibreProd σ) :
    x ∈ diagMax σ ↔ fst σ x = snd σ x ∧ fst σ x ∈ maximalIdeal T := by
  constructor
  · intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨m, hm, rfl⟩; exact ⟨rfl, hm⟩
    · exact ⟨by simp, by simp⟩
    · rintro y z - - ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
      exact ⟨by rw [map_add, map_add, hy1, hz1], by rw [map_add]; exact Ideal.add_mem _ hy2 hz2⟩
    · rintro c y - ⟨hy1, hy2⟩
      refine ⟨?_, by rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hy2⟩
      rw [smul_eq_mul, map_mul, map_mul, ← hy1]
      have : (snd σ c - fst σ c) * fst σ y = 0 := by
        have := Ideal.mul_mem_mul (snd_sub_fst_mem_ker σ c) hy2
        rwa [hsmall, Ideal.mem_bot] at this
      linear_combination -this
  · rintro ⟨h1, h2⟩
    have : x = diag σ (fst σ x) := (ext_iff σ).mpr ⟨rfl, h1.symm⟩
    rw [this]
    exact Ideal.subset_span ⟨_, h2, rfl⟩

abbrev Tangent : Type := fibreProd σ ⧸ diagMax σ

def mk : fibreProd σ →+* Tangent σ := Ideal.Quotient.mk _

/--
@isnad1 id=surjecti.0h3v.s10.4c1bde0e858a from=translated src=- shape=fd55057b vocab=222a7389
-/
theorem mk_surjective : Function.Surjective (mk σ) := Ideal.Quotient.mk_surjective

/--
@isnad1 id=iff.1h5v.s12.d418db9abd81 from=translated src=- shape=0786dac2 vocab=bb5ef7eb
-/
theorem mk_eq_mk_iff (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) (x y : fibreProd σ) :
    mk σ x = mk σ y ↔ fst σ x - fst σ y ∈ maximalIdeal T ∧ snd σ x - snd σ y = fst σ x - fst σ y := by
  rw [mk, Ideal.Quotient.eq, mem_diagMax_iff σ hsmall, map_sub, map_sub]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩⟩

/--
@isnad1 id=eq.0h5v.s11.1bee130f89c5 from=translated src=- shape=e16b30c3 vocab=0ec71bf0
-/
theorem algebraMap_tangent {A : Type} [CommRing A] [Algebra A T] (a : A) :
    algebraMap A (Tangent σ) a = mk σ (diag σ (algebraMap A T a)) := rfl

def res : Tangent σ →+* ResidueField T :=
  Ideal.Quotient.lift (diagMax σ) ((residue T).comp (fst σ)) (fun x hx => by
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    have hx' : x ∈ Ideal.span (diag σ '' (maximalIdeal T : Set T)) := hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨m, hm, rfl⟩; exact hm
    · simp
    · rintro y z - - hy hz; rw [map_add]; exact Ideal.add_mem _ hy hz
    · rintro c y - hy; rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hy)

/--
@isnad1 id=eq.0h4v.s11.fdfad17c0feb from=translated src=- shape=378dff08 vocab=239f0d80
-/
@[simp] theorem res_mk (x : fibreProd σ) : res σ (mk σ x) = residue T (fst σ x) := rfl

/--
@isnad1 id=surjecti.0h3v.s8.e43dcc48de9f from=translated src=- shape=82076d40 vocab=2a87014b
-/
theorem res_surjective : Function.Surjective (res σ) := by
  intro c
  obtain ⟨a, rfl⟩ := residue_surjective c
  exact ⟨mk σ (diag σ a), rfl⟩

/--
@isnad1 id=eq.0h5v.s9.d3103cefc697 from=translated src=- shape=05dc30fa vocab=2f5e56eb
-/
theorem res_algebraMap {A : Type} [CommRing A] [Algebra A T] (a : A) :
    res σ (algebraMap A (Tangent σ) a) = residue T (algebraMap A T a) := rfl

end Local

section LocalB

variable [IsLocalRing T]

/--
@isnad1 id=le.0h3v.s7.872ca9bd08ae from=translated src=- shape=0309e25a vocab=9bdf7415
-/
theorem ker_le_maximalIdeal [Nontrivial S] : RingHom.ker σ ≤ maximalIdeal T :=
  IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top σ)

/--
@isnad1 id=iff.1h4v.s10.ce3c085f30ce from=translated src=- shape=e0cb59aa vocab=69741773
-/
theorem isUnit_iff_isUnit_fst (hJ : RingHom.ker σ ≤ maximalIdeal T) (x : fibreProd σ) :
    IsUnit x ↔ IsUnit (fst σ x) := by
  constructor
  · intro h; exact h.map (fst σ)
  · intro h1
    have h2 : IsUnit (snd σ x) := by
      have : snd σ x = fst σ x + (snd σ x - fst σ x) := by ring
      rw [this]
      by_contra hn
      have hm : fst σ x + (snd σ x - fst σ x) ∈ maximalIdeal T := (mem_maximalIdeal _).mpr hn
      have : fst σ x ∈ maximalIdeal T := by
        have := Ideal.sub_mem _ hm (hJ (snd_sub_fst_mem_ker σ x)); rwa [add_sub_cancel_right] at this
      exact (mem_maximalIdeal _).mp this h1
    refine ⟨⟨x, pair σ (↑h1.unit⁻¹) (↑h2.unit⁻¹) ?_, ?_, ?_⟩, rfl⟩
    ·
      have e1 : σ (fst σ x) = σ (snd σ x) := apply_fst_eq_apply_snd σ x
      have u1 : σ (fst σ x) * σ (↑h1.unit⁻¹ : T) = 1 := by rw [← map_mul, IsUnit.mul_val_inv, map_one]
      have u2 : σ (snd σ x) * σ (↑h2.unit⁻¹ : T) = 1 := by rw [← map_mul, IsUnit.mul_val_inv, map_one]
      calc σ (↑h1.unit⁻¹ : T) = σ (↑h1.unit⁻¹ : T) * (σ (snd σ x) * σ (↑h2.unit⁻¹ : T)) := by rw [u2, mul_one]
        _ = (σ (fst σ x) * σ (↑h1.unit⁻¹ : T)) * σ (↑h2.unit⁻¹ : T) := by rw [e1]; ring
        _ = σ (↑h2.unit⁻¹ : T) := by rw [u1, one_mul]
    · exact (ext_iff σ).mpr ⟨h1.mul_val_inv, h2.mul_val_inv⟩
    · exact (ext_iff σ).mpr ⟨h1.val_inv_mul, h2.val_inv_mul⟩

/--
@isnad1 id=islocalr.1h3v.s8.67a469c227da from=translated src=- shape=a05a6ac8 vocab=7c9983d2
-/
theorem isLocalRing_fibreProd (hJ : RingHom.ker σ ≤ maximalIdeal T) : IsLocalRing (fibreProd σ) := by
  haveI : Nontrivial (fibreProd σ) := (fst σ).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun x => ?_)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (fst σ x) with h | h
  · exact Or.inl ((isUnit_iff_isUnit_fst σ hJ x).mpr h)
  · exact Or.inr ((isUnit_iff_isUnit_fst σ hJ (1 - x)).mpr (by rwa [map_sub, map_one]))

/--
@isnad1 id=islocalr.1h3v.s7.468675fdaae1 from=translated src=- shape=eb5b43b8 vocab=600d281e
-/
theorem isLocalRing_tangent (hJ : RingHom.ker σ ≤ maximalIdeal T) : IsLocalRing (Tangent σ) := by
  haveI := isLocalRing_fibreProd σ hJ
  haveI : Nontrivial (Tangent σ) := (res σ).domain_nontrivial
  exact IsLocalRing.of_surjective' (mk σ) (mk_surjective σ)

/--
@isnad1 id=iff.1h4v.s9.42b3504cffe5 from=translated src=- shape=c1daef4b vocab=f74f5b23
-/
theorem isUnit_iff_res_ne_zero (hJ : RingHom.ker σ ≤ maximalIdeal T)
    (z : Tangent σ) : IsUnit z ↔ res σ z ≠ 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective σ z
  rw [res_mk, Ne, residue_eq_zero_iff]
  constructor
  · intro hu hm
    have : IsUnit (res σ (mk σ x)) := hu.map (res σ)
    rw [res_mk] at this
    exact (mem_maximalIdeal _).mp hm (by
      by_contra hn; exact absurd this (by rw [(residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)]; exact not_isUnit_zero))
  · intro hx
    have : IsUnit (fst σ x) := by by_contra hn; exact hx ((mem_maximalIdeal _).mpr hn)
    exact ((isUnit_iff_isUnit_fst σ hJ x).mpr this).map (mk σ)

/--
@isnad1 id=iff.1h4v.s10.89638e146c95 from=translated src=- shape=854623c2 vocab=a89df3a8
-/
theorem mem_maximalIdeal_tangent_iff
    (hJ : RingHom.ker σ ≤ maximalIdeal T) (z : Tangent σ) :
    (letI := isLocalRing_tangent σ hJ; z ∈ maximalIdeal (Tangent σ)) ↔ res σ z = 0 := by
  letI := isLocalRing_tangent σ hJ
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_res_ne_zero σ hJ, not_not]

/--
@isnad1 id=eq.1h3v.s9.02dc32457f46 from=translated src=- shape=9f033687 vocab=9131f4a6
-/
theorem ker_res_eq_maximalIdeal (hJ : RingHom.ker σ ≤ maximalIdeal T) :
    (letI := isLocalRing_tangent σ hJ; RingHom.ker (res σ) = maximalIdeal (Tangent σ)) := by
  letI := isLocalRing_tangent σ hJ
  ext z
  rw [RingHom.mem_ker, ← mem_maximalIdeal_tangent_iff σ hJ]

/--
@isnad1 id=eq.2h3v.s11.dc06d27e187a from=translated src=- shape=b8b58167 vocab=863ee62c
-/
theorem maximalIdeal_tangent_sq_eq_bot (hsmall : RingHom.ker σ * maximalIdeal T = ⊥)
    (hJ : RingHom.ker σ ≤ maximalIdeal T) :
    (letI := isLocalRing_tangent σ hJ; (maximalIdeal (Tangent σ)) ^ 2 = ⊥) := by
  letI := isLocalRing_tangent σ hJ
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro z hz w hw
  rw [mem_maximalIdeal_tangent_iff σ hJ] at hz hw
  obtain ⟨x, rfl⟩ := mk_surjective σ z
  obtain ⟨y, rfl⟩ := mk_surjective σ w
  rw [res_mk, residue_eq_zero_iff] at hz hw
  rw [Ideal.mem_bot, ← map_mul, mk, Ideal.Quotient.eq_zero_iff_mem, mem_diagMax_iff σ hsmall, map_mul, map_mul]
  refine ⟨?_, Ideal.mul_mem_right _ _ hz⟩

  have hx' := snd_sub_fst_mem_ker σ x
  have hy' := snd_sub_fst_mem_ker σ y
  have h1 : (snd σ x - fst σ x) * fst σ y = 0 := by
    have := Ideal.mul_mem_mul hx' hw; rwa [hsmall, Ideal.mem_bot] at this
  have h2 : (snd σ y - fst σ y) * fst σ x = 0 := by
    have := Ideal.mul_mem_mul hy' hz; rwa [hsmall, Ideal.mem_bot] at this
  have h3 : (snd σ x - fst σ x) * (snd σ y - fst σ y) = 0 := by
    have := Ideal.mul_mem_mul hx' (hJ hy'); rwa [hsmall, Ideal.mem_bot] at this
  linear_combination (-1 : T) * h1 - h2 - h3

end LocalB

section Theta

variable [IsLocalRing T]

theorem eq_of_fst_eq_of_mk_eq (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {x y : fibreProd σ}
    (h1 : fst σ x = fst σ y) (h2 : mk σ x = mk σ y) : x = y := by
  rw [mk_eq_mk_iff σ hsmall] at h2
  refine (ext_iff σ).mpr ⟨h1, ?_⟩
  have := h2.2; rw [h1, sub_self, sub_eq_zero] at this; exact this

/--
@isnad1 id=ex.2h5v.s11.7bc4856c3c11 from=translated src=- shape=c1959275 vocab=4e16487c
-/
theorem exists_fst_eq_and_mk_eq (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) (a : T) (z : Tangent σ)
    (h : residue T a = res σ z) : ∃ x : fibreProd σ, fst σ x = a ∧ mk σ x = z := by
  obtain ⟨y, rfl⟩ := mk_surjective σ z
  rw [res_mk, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h
  have hj := snd_sub_fst_mem_ker σ y
  refine ⟨pair σ a (a + (snd σ y - fst σ y)) ?_, rfl, ?_⟩
  · rw [map_add, (RingHom.mem_ker).mp hj, add_zero]
  · rw [mk_eq_mk_iff σ hsmall, fst_pair, snd_pair]
    exact ⟨h, by ring⟩

/--
@isnad1 id=iff.1h4v.s11.637bc02f7d97 from=translated src=- shape=1d1da960 vocab=0bbea17d
-/
theorem mk_diag_eq_zero_iff (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) (a : T) :
    mk σ (diag σ a) = 0 ↔ a ∈ maximalIdeal T := by
  rw [← map_zero (mk σ), mk_eq_mk_iff σ hsmall, fst_diag, snd_diag, map_zero, map_zero, sub_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/--
@isnad1 id=eq.0h4v.s10.d7d5766e74c4 from=translated src=- shape=0abfb3d6 vocab=b438b9ac
-/
theorem natCast_tangent_eq (n : ℕ) : (n : Tangent σ) = mk σ (diag σ n) := by
  rw [map_natCast, map_natCast]

end Theta

section Artinian

def fibreProdSubmodule : Submodule T (T × T) where
  carrier := fibreProd σ
  zero_mem' := (fibreProd σ).zero_mem
  add_mem' := fun ha hb => (fibreProd σ).add_mem ha hb
  smul_mem' := fun c x hx => by
    show σ (c • x).1 = σ (c • x).2
    rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul, map_mul, map_mul, show σ x.1 = σ x.2 from hx]

/--
@isnad1 id=isartini.0h3v.s7.ee794a8da1b0 from=translated src=- shape=88901dd6 vocab=b4a1bb4d
-/
theorem isArtinianRing_fibreProd [IsArtinianRing T] : IsArtinianRing (fibreProd σ) := by
  haveI : IsNoetherianRing T := inferInstance
  haveI : Module.Finite T (fibreProdSubmodule σ) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  let e : fibreProdSubmodule σ ≃ₗ[T] fibreProd σ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite T (fibreProd σ) := Module.Finite.equiv e
  exact IsArtinianRing.of_finite T (fibreProd σ)

/--
@isnad1 id=isartini.0h3v.s7.d1ee8bba5afa from=translated src=- shape=440d384a vocab=fa9bbc67
-/
theorem isArtinianRing_tangent [IsLocalRing T] [IsArtinianRing T] : IsArtinianRing (Tangent σ) := by
  haveI := isArtinianRing_fibreProd σ
  infer_instance

end Artinian

end IsLocalRing.SmallExtension

end
