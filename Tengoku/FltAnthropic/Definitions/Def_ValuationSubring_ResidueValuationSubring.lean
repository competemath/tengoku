import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ValuationSubring

open IsLocalRing

variable {L : Type*} [Field L]

noncomputable def residueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    ValuationSubring (ResidueField S) :=
  ValuationSubring.ofSubring ((residue S).comp (A.inclusion S h)).range <| by
    intro x
    obtain ⟨s, rfl⟩ := residue_surjective x
    rcases A.mem_or_inv_mem (s : L) with hs | hs
    · exact Or.inl ⟨⟨s, hs⟩, rfl⟩
    · by_cases hu : IsUnit s
      · obtain ⟨u, rfl⟩ := hu
        have hinv : (((u⁻¹ : Sˣ) : S) : L) = ((u : S) : L)⁻¹ := map_units_inv S.subtype u
        refine Or.inr ⟨⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩, ?_⟩
        change residue S (A.inclusion S h ⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩) = (residue S u)⁻¹
        rw [← map_units_inv]
        rfl
      · refine Or.inl ⟨0, ?_⟩
        rw [map_zero, eq_comm, residue_eq_zero_iff]
        exact (_root_.mem_nonunits_iff.mpr hu)

noncomputable def toResidueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    A →+* A.residueValuationSubring S h :=
  ((residue S).comp (A.inclusion S h)).codRestrict (A.residueValuationSubring S h) fun a => ⟨a, rfl⟩

variable (A S : ValuationSubring L) (h : A ≤ S)

/--
@isnad1 id=iff.1h4v.s10.45acfec13f8e from=translated src=- shape=6f07637b vocab=7066ac03
-/
theorem mem_residueValuationSubring_iff {x : ResidueField S} :
    x ∈ A.residueValuationSubring S h ↔ ∃ a : A, residue S (A.inclusion S h a) = x :=
  Iff.rfl

/--
@isnad1 id=eq.1h4v.s11.ba2fecfa4efe from=translated src=- shape=f4ab77b5 vocab=43a7d636
-/
@[simp]
theorem coe_toResidueValuationSubring (a : A) :
    (A.toResidueValuationSubring S h a : ResidueField S) = residue S (A.inclusion S h a) :=
  rfl

/--
@isnad1 id=surjecti.1h3v.s11.c78bb8b799a7 from=translated src=- shape=e7ba63e8 vocab=63ef601f
-/
theorem toResidueValuationSubring_surjective :
    Function.Surjective (A.toResidueValuationSubring S h) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

/--
@isnad1 id=eq.1h3v.s11.e0c460691055 from=translated src=- shape=1b3ca5b7 vocab=44397885
-/
theorem ker_toResidueValuationSubring :
    RingHom.ker (A.toResidueValuationSubring S h) = A.idealOfLE S h := by
  ext a
  rw [RingHom.mem_ker, ← Subtype.coe_inj, coe_toResidueValuationSubring, ZeroMemClass.coe_zero,
    residue_eq_zero_iff]
  rfl

end ValuationSubring
