import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ExtEndgame_ProductionDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open ExtCitation

namespace ExtCitation

/--
@isnad1 id=mem.0h2v.s10.2015d070bc62 from=translated src=- shape=5e6522cb vocab=d2e95237
-/
theorem primeLocalToGlobal_mem_decompositionSubgroup (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    primeLocalToGlobal q g ∈ (primeLocalPlace q).decompositionSubgroup ℚ := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g

/--
@isnad1 id=eq.0h2v.s13.159db26d14f1 from=translated src=- shape=d31cc3c7 vocab=30a6b390
-/
theorem levelSubgroup_eq_ker (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup).comap (primeLocalToGlobal q)
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp (primeLocalToGlobal q)).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›, MonoidHom.comap_ker]
  rfl

/--
@isnad1 id=normal.0h2v.s8.3a8f64bdcc26 from=translated src=- shape=5cd70aa7 vocab=10fa84b3
-/
instance levelSubgroup_normal (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).Normal := by
  rw [levelSubgroup_eq_ker]; exact MonoidHom.normal_ker _

/--
@isnad1 id=finitein.0h2v.s9.72a23ed128c3 from=translated src=- shape=89dec9b9 vocab=cc9cfe25
-/
instance levelSubgroup_finiteIndex (q : Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ((F.fixingSubgroup).comap (primeLocalToGlobal q)).FiniteIndex := by
  rw [levelSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _

/--
@isnad1 id=le.1h3v.s8.84e7822806ed from=translated src=- shape=ae109a84 vocab=78bdbdd6
-/
theorem levelSubgroup_antitone (q : Nat.Primes) {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') :
    (F'.fixingSubgroup).comap (primeLocalToGlobal q) ≤ (F.fixingSubgroup).comap (primeLocalToGlobal q) :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h)

/--
@isnad1 id=iff.0h2v.s12.696f5250ea48 from=translated src=- shape=f611ab98 vocab=b3a24d4d
-/
theorem mem_inertiaPullback_iff (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    g ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ↔
      ∀ x : IsLocalRing.ResidueField (primeLocalPlace q),
        (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ :
          (primeLocalPlace q).decompositionSubgroup ℚ) • x = x := by
  rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτg⟩
    intro x
    have hmem : (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ : (primeLocalPlace q).decompositionSubgroup ℚ) = τ := by
      apply Subtype.ext; exact hτg.symm
    rw [hmem]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun φ => (φ : IsLocalRing.ResidueField (primeLocalPlace q) ≃+* _) x) hτ
    simpa using this
  · intro h
    refine ⟨⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    simpa using h x

/--
@isnad1 id=normal.0h1v.s7.6aab32ca691d from=translated src=- shape=1b34d4c8 vocab=ee0a77c5
-/
instance inertiaPullback_normal (q : Nat.Primes) :
    (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)).Normal := by

  let D := (primeLocalPlace q).decompositionSubgroup ℚ
  have hD : ∀ g : primeLocalGaloisGroup q, primeLocalToGlobal q g ∈ D := primeLocalToGlobal_mem_decompositionSubgroup q
  let r' : primeLocalGaloisGroup q →* D := (primeLocalToGlobal q).codRestrict D hD
  have : ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
      = (((primeLocalPlace q).inertiaSubgroup ℚ)).comap r' := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
    constructor
    · rintro ⟨τ, hτ, hτg⟩
      have : r' g = τ := Subtype.ext hτg.symm
      rwa [this]
    · intro h; exact ⟨r' g, h, rfl⟩
  rw [this, ValuationSubring.inertiaSubgroup, MonoidHom.comap_ker]
  exact MonoidHom.normal_ker _

end ExtCitation
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
