import Tengoku.Seed.LinearAlgebra.BilinearMap
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms reflection_reflection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reflection_one` (it only prints; the queue checks the axioms of every declaration). -/

/-! Polynomial part of the Peirce involution construction.

This file deliberately stops before multiplicativity.  The operator cubic is
named as an explicit intermediate input here; the accompanying derivation note
records how it must be proved from the polarized Jordan identity. -/

noncomputable section
namespace AlbertLean.Generic.PeircePolynomial

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {A : Type v} [AddCommGroup A] [Module K A]

def leftMul (μ : A →ₗ[K] A →ₗ[K] A) (p : A) : A →ₗ[K] A := μ p

def reflection (μ : A →ₗ[K] A →ₗ[K] A) (p x : A) : A :=
  x - (8 : K) • μ p x + (8 : K) • μ p (μ p x)

/-- Once the polarized Jordan identity supplies the Peirce operator cubic,
the polynomial `1 - 8L_p + 8L_p²` is involutive.  This is an intermediate
algebra lemma, not the final Jordan-automorphism theorem.-/
theorem reflection_reflection
    (μ : A →ₗ[K] A →ₗ[K] A) (p : A)
    (hcubic : ∀ x,
      (2 : K) • μ p (μ p (μ p x)) -
        (3 : K) • μ p (μ p x) + μ p x = 0)
    (x : A) : reflection μ p (reflection μ p x) = x := by
  have h3 := hcubic x
  have h4 := hcubic (μ p x)
  dsimp only [reflection]
  simp only [map_add, map_sub, map_smul]
  linear_combination (norm := module)
    (-16 : K) • h3 + (32 : K) • h4

/-- The same polynomial fixes the unit once `p²=p` and `p∘1=p` are known.-/
theorem reflection_one
    (μ : A →ₗ[K] A →ₗ[K] A) (one p : A)
    (hone : μ p one = p) (hidem : μ p p = p) :
    reflection μ p one = one := by
  simp [reflection, hone, hidem]

end AlbertLean.Generic.PeircePolynomial
