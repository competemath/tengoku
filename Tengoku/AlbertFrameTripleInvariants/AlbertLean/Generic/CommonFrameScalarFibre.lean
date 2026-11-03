import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.OuterProductScaling

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms two_column_coefficients_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms three_scalars_eq_of_minor` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms common_frame_scalar_fibre` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ScalarFibre

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A displayed nonzero two-column minor makes the two column coefficients
unique.  This is the only rank-two input used below.
@isnad1 id=and.3h7v.s8.75c1275de518 from=translated src=- shape=97ef822f vocab=b8e146e0
-/
theorem two_column_coefficients_zero
    (x y : Vec3 K) (p q : Fin 3) (α β : K)
    (hminor : x p * y q - x q * y p ≠ 0)
    (hp : α * x p + β * y p = 0)
    (hq : α * x q + β * y q = 0) :
    α = 0 ∧ β = 0 := by
  have hα : α * (x p * y q - x q * y p) = 0 := by
    linear_combination y q * hp - y p * hq
  have hβ : β * (x p * y q - x q * y p) = 0 := by
    linear_combination x p * hq - x q * hp
  exact ⟨(mul_eq_zero.mp hα).resolve_right hminor,
    (mul_eq_zero.mp hβ).resolve_right hminor⟩

def ThreeSumZero (u : Fin 3 → Vec3 K) : Prop :=
  ∀ j, u 0 j + u 1 j + u 2 j = 0

def ThreeScaledSumZero (t : Fin 3 → K) (u : Fin 3 → Vec3 K) : Prop :=
  ∀ j, t 0 * u 0 j + t 1 * u 1 j + t 2 * u 2 j = 0

/-- If three columns sum to zero and have one displayed rank-two minor, a
second relation with all three coefficients forces those coefficients equal.
@isnad1 id=and.3h5v.s8.1eb4297219d5 from=translated src=- shape=5fb598f0 vocab=b8be4049
-/
theorem three_scalars_eq_of_minor
    (u : Fin 3 → Vec3 K) (t : Fin 3 → K) (p q : Fin 3)
    (hsum : ThreeSumZero u)
    (hscaled : ThreeScaledSumZero t u)
    (hminor : u 0 p * u 1 q - u 0 q * u 1 p ≠ 0) :
    t 0 = t 1 ∧ t 1 = t 2 := by
  have hp : (t 0 - t 2) * u 0 p + (t 1 - t 2) * u 1 p = 0 := by
    linear_combination hscaled p - t 2 * hsum p
  have hq : (t 0 - t 2) * u 0 q + (t 1 - t 2) * u 1 q = 0 := by
    linear_combination hscaled q - t 2 * hsum q
  obtain ⟨h0, h1⟩ :=
    two_column_coefficients_zero (u 0) (u 1) p q
      (t 0 - t 2) (t 1 - t 2) hminor hp hq
  constructor
  · exact (sub_eq_zero.mp h0).trans (sub_eq_zero.mp h1).symm
  · exact sub_eq_zero.mp h1

/-- Projector data for one labelled three-frame after its `a`-blocks have
already been matched.
@isnad1 id=ex.9h6v.s10.bbfb4c251771 from=translated src=- shape=c4a1718c vocab=27ebdfee
-/
theorem common_frame_scalar_fibre
    (a : Fin 3 → Mat3 K)
    (u v u' v' : Fin 3 → Vec3 K)
    (hblock : ∀ i, a i * a i - a i = -(hat (u i) * hat (v i)))
    (hblock' : ∀ i, a i * a i - a i = -(hat (u' i) * hat (v' i)))
    (htrace : ∀ i, Matrix.trace (a i) = 1)
    (hadj : ∀ i, Matrix.adjugate (a i) ≠ 0)
    (hsumu : ThreeSumZero u) (hsumu' : ThreeSumZero u')
    (hsumv : ThreeSumZero v) (hsumv' : ThreeSumZero v')
    (hrankTwo :
      (∃ p q, u 0 p * u 1 q - u 0 q * u 1 p ≠ 0) ∨
      (∃ p q, v 0 p * v 1 q - v 0 q * v 1 p ≠ 0)) :
    ∃ t : K, t ≠ 0 ∧
      (∀ i, u' i = t • u i) ∧ (∀ i, v' i = t⁻¹ • v i) := by
  classical
  choose t ht hu hv using fun i =>
    same_a_scalar_fibre (a i) (u i) (v i) (u' i) (v' i)
      (hblock i) (hblock' i) (htrace i) (hadj i)
  have htu : ThreeScaledSumZero t u := by
    intro j
    have h := hsumu' j
    simpa [hu] using h
  have htv : ThreeScaledSumZero (fun i => (t i)⁻¹) v := by
    intro j
    have h := hsumv' j
    simpa [hv] using h
  have hcommon : t 0 = t 1 ∧ t 1 = t 2 := by
    rcases hrankTwo with ⟨p, q, hminor⟩ | ⟨p, q, hminor⟩
    · exact three_scalars_eq_of_minor u t p q hsumu htu hminor
    · obtain ⟨h01, h12⟩ :=
        three_scalars_eq_of_minor v (fun i => (t i)⁻¹) p q hsumv htv hminor
      exact ⟨inv_injective h01, inv_injective h12⟩
  refine ⟨t 0, ht 0, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hu 0
    · simpa [hcommon.1] using hu 1
    · simpa [hcommon.1, hcommon.2] using hu 2
  · intro i
    fin_cases i
    · exact hv 0
    · simpa [hcommon.1] using hv 1
    · simpa [hcommon.1, hcommon.2] using hv 2

end AlbertLean.Generic.QuaternionRow.ScalarFibre
