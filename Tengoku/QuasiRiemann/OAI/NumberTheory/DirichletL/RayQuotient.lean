import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.RayOrthogonality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section

variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)

abbrev Characters := characters H
abbrev classNumber := Nat.card ((A ⧸ M)ˣ ⧸ H)

/--
@isnad1 id=lt.0h3v.s6.656eec23c1b0 from=translated src=- shape=8521d144 vocab=e19e8d23
-/
theorem classNumber_pos : 0 < classNumber M H := ray_card_pos H

include hH

/--
@isnad1 id=unitinva.1h4v.s10.fcac10b5f16e from=translated src=- shape=dc16b49f vocab=c56a1672
-/
theorem character_unitInvariant (χ : Characters M H) :
    IdealCharacter.UnitInvariant M χ := by
  intro u
  exact (mem_characters_iff H χ).mp χ.property _ (hH ⟨u, rfl⟩)

def toFullRay : Characters M H →* rayCharacters M where
  toFun χ := ⟨χ, (mem_rayCharacters_iff M χ).mpr (character_unitInvariant M H hH χ)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/--
@isnad1 id=injectiv.1h3v.s13.8eb06cfd1936 from=translated src=- shape=e10bf27f vocab=0c6e2f6c
-/
theorem toFullRay_injective : Function.Injective (toFullRay M H hH) := by
  intro χ ψ heq
  exact Subtype.ext (congrArg (fun ρ : rayCharacters M => (ρ : MulChar (A ⧸ M) ℂ)) heq)

/--
@isnad1 id=iff.1h4v.s14.08cbee70bc84 from=translated src=- shape=b6924bdb vocab=d61e7c8b
-/
@[simp] theorem toFullRay_eq_one (χ : Characters M H) :
    toFullRay M H hH χ = 1 ↔ χ = 1 := by
  rw [← map_one (toFullRay M H hH)]
  exact (toFullRay_injective M H hH).eq_iff

variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : Characters M H) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ (character_unitInvariant M H hH χ)

def identityClass : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    inUnitSubgroup H (Ideal.Quotient.mk M a)}

omit [Finite (A ⧸ M)] in
/--
@isnad1 id=iff.2h4v.s9.f89d9a75af6a from=translated src=- shape=8b860b7b vocab=9e2aa2a8
-/
theorem identityClass_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ identityClass M H ↔
      inUnitSubgroup H (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hua, huH⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    let w := Units.map (Ideal.Quotient.mk M).toMonoidHom v
    refine ⟨u * w⁻¹, ?_, H.mul_mem huH (H.inv_mem (hH ⟨v, rfl⟩))⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    change (u : A ⧸ M) * ((Units.map (Ideal.Quotient.mk M).toMonoidHom v)⁻¹ :
      (A ⧸ M)ˣ) = _
    rw [hua, ← hq]
    change (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) *
      (w : A ⧸ M) * (w⁻¹ : (A ⧸ M)ˣ) = _
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

/--
@isnad1 id=le.1h5v.s10.349393357170 from=translated src=- shape=048a5446 vocab=63ab5374
-/
theorem norm_idealCharacter_le_one (χ : Characters M H) (I : Ideal A) :
    ‖idealCharacter M H hH χ I‖ ≤ 1 :=
  IdealCharacter.norm_ofResidue_le_one M χ _ I

/--
@isnad1 id=eq.1h4v.s10.b156ef389639 from=translated src=- shape=a503a2b5 vocab=1f953d67
-/
theorem idealCharacter_one (I : Ideal A) :
    idealCharacter M H hH 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I

/--
@isnad1 id=eq.1h4v.s11.ac494498de92 from=translated src=- shape=b501526c vocab=b6676ebc
-/
theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : Characters M H, idealCharacter M H hH χ I =
      if I ∈ identityClass M H then (classNumber M H : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, identityClass]
  · have heq (χ : Characters M H) : idealCharacter M H hH χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_characters, identityClass_iff_generator M H hH hI, classNumber]

end
end SevenEighths.RayQuotient

end OAI
