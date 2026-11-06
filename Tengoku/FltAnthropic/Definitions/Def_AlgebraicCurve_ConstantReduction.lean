import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Repartitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure ConstantReduction where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  placeMap : Place L F → Place (ResidueField A) Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

  deg_placeMap : ∀ P, (placeMap P).deg = P.deg

  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

namespace ConstantReduction

variable {A F Fbar}

variable (R : ConstantReduction A F Fbar)

/--
@isnad1 id=eq.1h4v.s7.9705c57d8291 from=translated src=- shape=49556dc3 vocab=a2ca542d
-/
theorem ord_algebraMap (P : Place L F) {c : L} (hc : c ≠ 0) : P.ord (algebraMap L F c) = 0 := by
  have hu : IsUnit (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) :=
    ⟨⟨⟨algebraMap L F c, P.algebraMap_mem' c⟩, ⟨algebraMap L F c⁻¹, P.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

/--
@isnad1 id=eq.1h5v.s6.12e181a8c8c0 from=translated src=- shape=e385959b vocab=12ea738c
-/
theorem ord_smul (P : Place L F) {c : L} (hc : c ≠ 0) (f : F) : P.ord (c • f) = P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap P hc, zero_add]

/--
@isnad1 id=mem.1h6v.s9.b266d91a585a from=translated src=- shape=d7b11a38 vocab=5aec1eb0
-/
theorem mapDomain_mem_principal {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.principal (K := ResidueField A) (F := Fbar) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  exact ⟨R.residue ⟨c • f, hc⟩, hres, fun Q =>
    R.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P => by rw [hDf P]; exact (ord_smul P hc0 f).symm) Q⟩

end ConstantReduction

end AlgebraicCurve

end
