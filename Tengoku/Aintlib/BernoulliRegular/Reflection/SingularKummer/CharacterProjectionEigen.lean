module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.SingularRepresentative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: character projections are eigenspaces

This file proves the elementary eigenspace calculation for the character
projection

```text
  e_i = |Delta|^{-1} sum_a a^{-i} [a].
```

If an element lies in the range of this projection, then the action of
`b : Delta` on it is multiplication by `b^i`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace CharacterProjection

variable {p : ℕ} [NeZero p]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

/-- Reindexing coefficient identity for the `i`-th character.
@isnad1 id=eq.0h4v.s7.1550e72834cc from=translated src=- shape=37fba8bb vocab=4b8f8e1c
-/
theorem characterProjectionCoefficient_inv_mul
    (i : ℕ) (b a : Delta p) :
    characterProjectionCoefficient (p := p) i (b⁻¹ * a) =
      ((b : ZMod p) ^ i) * characterProjectionCoefficient (p := p) i a := by
  have hinv : (b⁻¹ * a)⁻¹ = a⁻¹ * b := by group
  rw [characterProjectionCoefficient, characterProjectionCoefficient, hinv]
  simp only [Units.val_mul]
  rw [mul_pow]
  ring

/-- The character projection is contained in the eigenspace for the
corresponding character.
@isnad1 id=eq.0h6v.s10.b00eeb9a5344 from=translated src=- shape=38bfec14 vocab=a91c7567
-/
theorem apply_characterProjection
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) (b : Delta p) (x : M) :
    ρ b (characterProjection (p := p) i ρ x) =
      ((b : ZMod p) ^ i) • characterProjection (p := p) i ρ x := by
  calc
    ρ b (characterProjection (p := p) i ρ x)
        = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a • ρ (b * a) x := by
          simp [characterProjection, projection, map_mul]
    _ = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i (b⁻¹ * a) • ρ a x := by
          refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
          intro a
          simp [map_mul]
    _ = ((b : ZMod p) ^ i) • characterProjection (p := p) i ρ x := by
          simp [characterProjection, projection, characterProjectionCoefficient_inv_mul,
            smul_smul, Finset.smul_sum]

/-- Elementwise eigenspace statement for the range of the character
projection.
@isnad1 id=eq.1h6v.s10.f92d0f26c093 from=translated src=- shape=fd91dd96 vocab=31dff2af
-/
theorem mem_characterProjection_range_apply
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) (b : Delta p)
    {x : M}
    (hx : x ∈ LinearMap.range (characterProjection (p := p) i ρ)) :
    ρ b x = ((b : ZMod p) ^ i) • x := by
  obtain ⟨y, rfl⟩ := hx
  exact apply_characterProjection (p := p) i ρ b y

end CharacterProjection

namespace SingularLinearAction
namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

end SingularPair
end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
