import Tengoku.PaperCLean.PaperC.Affine.System
import Tengoku.Seed.Data.Rat.Cast.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform probabilities of finite affine systems

The probability model used in the paper is uniform on a finite vector space
over `𝔽₂`.  This module turns the cardinality theorem for affine fibers into an
exact rational probability formula.  It is a coordinate-free version of the
counting part of Lemma 2.1.
-/

namespace PaperC.Affine

variable {V W : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [AddCommGroup W] [Module 𝔽₂ W]

noncomputable section

variable [Fintype V]

local instance probabilitySolutionFintype (A : V →ₗ[𝔽₂] W) (b : W) :
    Fintype (Solution A b) :=
  Fintype.ofFinite _

local instance probabilityCompatibleDecidable (A : V →ₗ[𝔽₂] W) (b : W) :
    Decidable (Compatible A b) :=
  Classical.propDecidable _

/-- Uniform probability of the affine event `A x = b`, as an exact rational
number.-/
def uniformSolutionProbability (A : V →ₗ[𝔽₂] W) (b : W) : ℚ :=
  (Fintype.card (Solution A b) : ℚ) / (Fintype.card V : ℚ)

/-- The cardinality of a finite `𝔽₂`-vector space is the corresponding power
of two.
@isnad1 id=eq.0h1v.s6.7f454aedefe0 from=translated src=- shape=2a7f782c vocab=7160d684
-/
theorem card_eq_two_pow_finrank :
    Fintype.card V = 2 ^ Module.finrank 𝔽₂ V := by
  calc
    Fintype.card V =
        Fintype.card 𝔽₂ ^ Module.finrank 𝔽₂ V :=
      Module.card_eq_pow_finrank (K := 𝔽₂) (V := V)
    _ = 2 ^ Module.finrank 𝔽₂ V := by rw [ZMod.card]

/-- Exact uniform probability of a finite affine system.  Incompatibility
gives probability zero; otherwise the numerator is the size of the kernel.
@isnad1 id=eq.0h4v.s9.b00090c1548d from=translated src=- shape=f7f12a5e vocab=5a865fcf
-/
theorem uniformSolutionProbability_eq_ite
    (A : V →ₗ[𝔽₂] W) (b : W) :
    uniformSolutionProbability A b =
      if Compatible A b then
        (2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) : ℚ) /
          (2 ^ Module.finrank 𝔽₂ V : ℚ)
      else
        0 := by
  classical
  unfold uniformSolutionProbability
  rw [card_solution_eq_ite, card_eq_two_pow_finrank (V := V)]
  split_ifs <;> simp_all

/-- Compatible case of the exact affine probability formula.
@isnad1 id=eq.1h4v.s9.195b72e19ff5 from=translated src=- shape=88dab0ac vocab=99f9b826
-/
theorem uniformSolutionProbability_of_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : Compatible A b) :
    uniformSolutionProbability A b =
      (2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) : ℚ) /
        (2 ^ Module.finrank 𝔽₂ V : ℚ) := by
  rw [uniformSolutionProbability_eq_ite, ite_eq_left h]

/-- Incompatible affine systems have probability zero.
@isnad1 id=eq.1h4v.s7.5daf3a6f83c2 from=translated src=- shape=d8368ed4 vocab=fcae2623
-/
theorem uniformSolutionProbability_of_not_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : ¬Compatible A b) :
    uniformSolutionProbability A b = 0 := by
  rw [uniformSolutionProbability_eq_ite, ite_eq_right h]

end

end PaperC.Affine
