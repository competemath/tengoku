import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

section KummerChar

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ))

def kummerRoot (x : (↥F)ˣ) : AlgebraicClosure ℚ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

/--
@isnad1 id=eq.0h3v.s10.c5795040f239 from=translated src=- shape=dfa725a0 vocab=68e1ec1e
-/
theorem kummerRoot_pow (x : (↥F)ˣ) : kummerRoot p F x ^ p = ((x : ↥F) : AlgebraicClosure ℚ) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

/--
@isnad1 id=ne.0h3v.s8.50de6bba836b from=translated src=- shape=dbd6dbf0 vocab=15e7d54a
-/
theorem kummerRoot_ne_zero (x : (↥F)ˣ) : kummerRoot p F x ≠ 0 := fun h => by
  have := kummerRoot_pow p F x
  rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at this
  exact (Units.ne_zero x) (Subtype.ext (by exact_mod_cast this.symm))

/--
@isnad1 id=eq.0h4v.s10.19530e8d41c2 from=translated src=- shape=0d4a5dd6 vocab=ab9478a3
-/
theorem div_kummerRoot_pow_eq_one (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) / kummerRoot p F x) ^ p = 1 := by
  rw [div_pow, ← map_pow, kummerRoot_pow, div_eq_one_iff_eq]
  · exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ (x : ↥F).2
  · exact_mod_cast (Units.ne_zero x : (x : ↥F) ≠ 0)

include hζ in
/--
@isnad1 id=ex.1h5v.s10.56fcf0a1038f from=translated src=- shape=03814d3b vocab=44315c87
-/
theorem exists_kummerExp (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    ∃ i < p, ζ ^ i = (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) / kummerRoot p F x :=
  hζ.eq_pow_of_pow_eq_one (div_kummerRoot_pow_eq_one p F x σ)

def kummerChar (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) : ZMod p :=
  (Classical.choose (exists_kummerExp p ζ hζ F x σ) : ℕ)

/--
@isnad1 id=eq.1h5v.s10.efec08f27df8 from=translated src=- shape=76ac9950 vocab=1b60cf5a
-/
theorem kummerChar_spec (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) = ζ ^ (kummerChar p ζ hζ F x σ).val * kummerRoot p F x := by
  obtain ⟨hi, h⟩ := Classical.choose_spec (exists_kummerExp p ζ hζ F x σ)
  rw [kummerChar, ZMod.val_natCast_of_lt hi, h, div_mul_cancel₀ _ (kummerRoot_ne_zero p F x)]

end KummerChar

end NumberField.LevelArith

end
