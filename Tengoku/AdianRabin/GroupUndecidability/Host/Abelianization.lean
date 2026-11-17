import Tengoku.AdianRabin.GroupUndecidability.Host.Presentation
import Tengoku.Seed.GroupTheory.Abelianization.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability
namespace Host

/-- Every homomorphism from the host group to a commutative group kills `D`.
@isnad1 id=eq.0h3v.s8.c44ae83cfff0 from=translated src=- shape=1a039146 vocab=d825eb6d
-/
theorem map_d_eq_one_of_commGroup
    (datum : Thue.StandingDatum) {A : Type*} [CommGroup A]
    (f : (presentationOf datum).Group →* A) :
    f (PresentedGroup.of (0 : Fin 3)) = 1 := by
  let P := presentationOf datum
  let x : Fin 3 → A := fun i ↦ f (PresentedGroup.of i)
  have hrel (i : Fin 9) : Word.eval x (P.relator i) = 1 := by
    calc
      Word.eval x (P.relator i) = f (P.evalWord (P.relator i)) :=
        (Word.map_eval f
          (fun j ↦ (PresentedGroup.of j : P.Group)) (P.relator i)).symm
      _ = f 1 := congrArg f (P.relator_eq_one i)
      _ = 1 := map_one f
  have h₀ := hrel 0
  have h₈ := hrel 8
  simp [P, presentationOf, presentation, rho, oldSurvivingRelator, tau,
    dWord, sWord, zWord, tWord, cWord, yWord, eWord,
    mul_comm] at h₀ h₈
  change x 0 = 1
  have hd₄ : x 0 ^ 4 = x 0 := mul_inv_eq_one.mp h₀
  have hdinv : (x 0)⁻¹ = x 0 := mul_inv_eq_one.mp h₈
  have hd₂ : x 0 ^ 2 = 1 := by
    calc
      x 0 ^ 2 = (x 0)⁻¹ * x 0 := by rw [pow_two, hdinv]
      _ = 1 := by simp
  calc
    x 0 = x 0 ^ 4 := hd₄.symm
    _ = (x 0 ^ 2) ^ 2 := pow_mul (x 0) 2 2
    _ = 1 := by simp [hd₂]

/-- The image of `D` is trivial in the abelianization of the host group.
@isnad1 id=eq.0h1v.s10.69d932b021ca from=translated src=- shape=5202a4ca vocab=dd4f3517
-/
theorem d_eq_one_in_abelianization (datum : Thue.StandingDatum) :
    Abelianization.of
      (PresentedGroup.of (0 : Fin 3) : (presentationOf datum).Group) = 1 :=
  map_d_eq_one_of_commGroup datum Abelianization.of

end Host
end Undecidability
