import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_ProjSpace_awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_ProjSpace_awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace K6SOL

section ChartIdeal

variable {A : Type} [CommRing A] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

def xpow (i : Fin (n + 1)) (d : ℕ) : ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
  ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩

def frac (i : Fin (n + 1)) (d : ℕ) (F : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := F
      den := xpow (A := A) i d
      den_mem := ⟨d, rfl⟩ }

theorem frac_zero (i : Fin (n + 1)) (d : ℕ) : frac (A := A) i d 0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Submodule.coe_zero]
  exact Localization.mk_zero _

theorem frac_add (i : Fin (n + 1)) (d : ℕ) (F G : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    frac i d (F + G) = frac i d F + frac i d G := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_add, Submodule.coe_add]
  rw [Localization.add_mk_self]

theorem frac_mul (i : Fin (n + 1)) (e d : ℕ) (G : ↥(homogeneousSubmodule (Fin (n + 1)) A e))
    (F : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    frac i (e + d) ⟨(G : MvPolynomial (Fin (n + 1)) A) * (F : MvPolynomial (Fin (n + 1)) A),
      SetLike.mul_mem_graded G.2 F.2⟩ = frac i e G * frac i d F := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mul]
  rw [Localization.mk_mul]
  congr 1
  ext
  simp [xpow, pow_add]

def comp (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) : ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
  ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩

theorem comp_zero (d : ℕ) : comp (A := A) (n := n) d 0 = 0 := Subtype.ext (by simp [comp])

theorem comp_add (d : ℕ) (p q : MvPolynomial (Fin (n + 1)) A) : comp d (p + q) = comp d p + comp d q :=
  Subtype.ext (by simp [comp])

def fcHom (i : Fin (n + 1)) (d : ℕ) :
    MvPolynomial (Fin (n + 1)) A →+ HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) where
  toFun p := frac i d (comp d p)
  map_zero' := by simp only [comp_zero, frac_zero]
  map_add' p q := by simp only [comp_add, frac_add]

end ChartIdeal

section Sat

variable {A : Type} [CommRing A] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

theorem frac_xpow (i : Fin (n + 1)) (N : ℕ) : frac i N (xpow (A := A) i N) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self (⟨(xpow (A := A) i N : MvPolynomial (Fin (n + 1)) A), N, rfl⟩ :
    Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))

theorem frac_xpow_mul (i : Fin (n + 1)) (N d : ℕ) (F : ↥(𝒜 d)) :
    frac i (N + d) ⟨MvPolynomial.X i ^ N * (F : MvPolynomial (Fin (n + 1)) A),
      SetLike.mul_mem_graded (xpow (A := A) i N).2 F.2⟩ = frac i d F := by
  have := frac_mul i N d (xpow (A := A) i N) F
  rw [frac_xpow, one_mul] at this
  exact this

theorem frac_mul_xpow (i : Fin (n + 1)) (d N : ℕ) (F : ↥(𝒜 d)) :
    frac i (d + N) ⟨(F : MvPolynomial (Fin (n + 1)) A) * MvPolynomial.X i ^ N,
      SetLike.mul_mem_graded F.2 (xpow (A := A) i N).2⟩ = frac i d F := by
  have := frac_mul i d N F (xpow (A := A) i N)
  rw [frac_xpow, mul_one] at this
  exact this

theorem awayMk_eq_frac (i : Fin (n + 1)) (m : ℕ) (H : MvPolynomial (Fin (n + 1)) A)
    (hH : H ∈ 𝒜 (m • 1)) (hH' : H ∈ 𝒜 m) :
    HomogeneousLocalization.Away.mk 𝒜 (ProjSpace.X_mem_one A n i) m H hH = frac i m ⟨H, hH'⟩ := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  simp only [frac, HomogeneousLocalization.val_mk]
  rfl

def InSat (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (i : Fin (n + 1))
    (x : HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)) : Prop :=
  ∃ (D : ℕ) (P : MvPolynomial (Fin (n + 1)) A) (hP : P.IsHomogeneous D),
    P ∈ I ∧ x = frac i D ⟨P, (MvPolynomial.mem_homogeneousSubmodule D P).mpr hP⟩

def satAway (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (i : Fin (n + 1)) :
    Ideal (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)) where
  carrier := {x | InSat I i x}
  zero_mem' := by
    refine ⟨0, 0, MvPolynomial.isHomogeneous_zero _ _ _, I.zero_mem, ?_⟩
    rw [show (⟨(0 : MvPolynomial (Fin (n + 1)) A), (MvPolynomial.mem_homogeneousSubmodule 0 _).mpr
      (MvPolynomial.isHomogeneous_zero _ _ 0)⟩ : ↥(𝒜 0)) = 0 from Subtype.ext rfl, frac_zero]
  add_mem' := by
    rintro x y ⟨D, P, hP, hPI, rfl⟩ ⟨D', P', hP', hP'I, rfl⟩
    refine ⟨D + D', P * MvPolynomial.X i ^ D' + MvPolynomial.X i ^ D * P',
      (hP.mul (MvPolynomial.isHomogeneous_X_pow i D')).add ((MvPolynomial.isHomogeneous_X_pow i D).mul hP'),
      I.add_mem (I.mul_mem_right _ hPI) (I.mul_mem_left _ hP'I), ?_⟩
    rw [← frac_mul_xpow i D D' ⟨P, _⟩, ← frac_xpow_mul i D D' ⟨P', _⟩, ← frac_add]
    rfl
  smul_mem' := by
    rintro c x ⟨D, P, hP, hPI, rfl⟩
    obtain ⟨m, H, hH, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 (ProjSpace.X_mem_one A n i) c
    have hH' : H ∈ 𝒜 m := by simpa using hH
    have hHh : H.IsHomogeneous m := (MvPolynomial.mem_homogeneousSubmodule m H).mp hH'
    refine ⟨m + D, H * P, hHh.mul hP, I.mul_mem_left _ hPI, ?_⟩
    rw [smul_eq_mul, awayMk_eq_frac i m H hH hH', ← frac_mul]

theorem mem_satAway_iff (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (i : Fin (n + 1))
    (x : HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)) : x ∈ satAway I i ↔ InSat I i x := Iff.rfl

theorem exists_X_pow_mul_mem_of_inSat (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (i : Fin (n + 1))
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d)
    (h : InSat I i (frac i d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩)) :
    ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ I := by
  obtain ⟨D, P, hP, hPI, hEq⟩ := h
  have hval := congr_arg HomogeneousLocalization.val hEq
  simp only [frac, HomogeneousLocalization.val_mk, xpow] at hval
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
  obtain ⟨c, hc⟩ := hval
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
  refine ⟨k + D, ?_⟩
  have : MvPolynomial.X i ^ (k + D) * F = (c : MvPolynomial (Fin (n + 1)) A) * (MvPolynomial.X i ^ d * P) := by
    rw [← hc, ← hk, pow_add, mul_assoc]
  rw [this]
  exact I.mul_mem_left _ (I.mul_mem_left _ hPI)

end Sat

end K6SOL

open K6SOL in

theorem solution
    (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) :
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ }) ∈
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } ↔
      ∃ N : ℕ, X i ^ N * F ∈ I := by
  classical

  have hX := ProjSpace.X_mem_one A n i

  have hinj : Function.Injective (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)) := by
    intro a b hab
    have := congr_arg (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) hX one_pos).inv hab
    rwa [← Proj.basicOpenIsoAway_hom _ _ hX one_pos, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at this
  have hsurj : Function.Surjective (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)) := by
    intro y
    refine ⟨(Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) hX one_pos).inv y, ?_⟩
    rw [← Proj.basicOpenIsoAway_hom _ _ hX one_pos, Iso.inv_hom_id_apply]

  have hS : { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } =
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)) '' {x | InSat I i x} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, InSat]
    constructor
    · rintro ⟨d, F, hF, hFI, rfl⟩
      exact ⟨_, ⟨d, F, hF, hFI, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨d, F, hF, hFI, rfl⟩, rfl⟩
      exact ⟨d, F, hF, hFI, rfl⟩
  have hspan : Ideal.span {x : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) |
      InSat I i x} = satAway I i := by
    apply le_antisymm
    · exact Ideal.span_le.mpr fun x hx => hx
    · exact fun x hx => Ideal.subset_span hx
  rw [hS, ← Ideal.map_span, hspan]
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h
    have hx' : InSat I i (frac i d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩) := by
      rw [← mem_satAway_iff]
      have hxx := hinj hxe
      rw [hxx] at hx
      exact hx
    exact exists_X_pow_mul_mem_of_inSat I i d F hF hx'
  · rintro ⟨N, hN⟩
    apply Ideal.mem_map_of_mem
    show InSat I i (frac i d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩)
    refine ⟨N + d, X i ^ N * F, (MvPolynomial.isHomogeneous_X_pow i N).mul hF, hN, ?_⟩
    rw [← frac_xpow_mul i N d]

end
