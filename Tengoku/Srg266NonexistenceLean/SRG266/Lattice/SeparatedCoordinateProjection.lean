/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SplitCoordinateTrace
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Classical

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

def middleCoordinateProjection (n : ℕ) : ((W × (Fin n → ℚ)) × U) →ₗ[ℚ] (Fin n → ℚ) :=
  (LinearMap.snd ℚ W (Fin n → ℚ)).comp (LinearMap.fst ℚ (W × (Fin n → ℚ)) U)

def middleCoordinateInclusion (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] ((W × (Fin n → ℚ)) × U) :=
  (LinearMap.inl ℚ (W × (Fin n → ℚ)) U).comp (LinearMap.inr ℚ W (Fin n → ℚ))

theorem separated_coordinate_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (ψ : (ι → ℚ) ≃ₗ[ℚ] ((W × (Fin n → ℚ)) × U))
    (hsep : ∀ i, (ψ (Pi.single i 1)).1.2 = 0 ∨
      ((ψ (Pi.single i 1)).1.1 = 0 ∧ (ψ (Pi.single i 1)).2 = 0)) :
    ∃ a : ι → ℚ, (∀ i, a i = 0 ∨ a i = 1) ∧
      (∀ i, middleCoordinateInclusion n (middleCoordinateProjection n (ψ (Pi.single i 1))) =
        a i • ψ (Pi.single i 1)) ∧ (∑ i, a i) = n := by
  let a : ι → ℚ := fun i => if (ψ (Pi.single i 1)).1.2 = 0 then 0 else 1
  have ha (i) : a i = 0 ∨ a i = 1 := by
    dsimp only [a]
    split_ifs <;> simp
  have heigen (i) : middleCoordinateInclusion n
      (middleCoordinateProjection n (ψ (Pi.single i 1))) = a i • ψ (Pi.single i 1) := by
    by_cases hz : (ψ (Pi.single i 1)).1.2 = 0
    · change ((0, (ψ (Pi.single i 1)).1.2), 0) = _
      simp [a, hz]
    · obtain ⟨hw, hu⟩ := (hsep i).resolve_left hz
      change ((0, (ψ (Pi.single i 1)).1.2), 0) = _
      simp only [a, ite_eq_right hz, one_smul]
      exact Prod.ext (Prod.ext hw.symm rfl) hu.symm
  let f := (middleCoordinateProjection n (W := W) (U := U)).comp ψ.toLinearMap
  let g := ψ.symm.toLinearMap.comp (middleCoordinateInclusion n (W := W) (U := U))
  have hfg : f.comp g = LinearMap.id := by
    ext z i
    simp [f, g, middleCoordinateProjection, middleCoordinateInclusion]
  have hdiag (i) : g (f (Pi.single i 1)) = a i • Pi.single i 1 := by
    apply ψ.injective
    simpa [f, g] using heigen i
  refine ⟨a, ha, heigen, ?_⟩
  simpa using sum_coordinate_eigenvalues_of_split f g hfg a hdiag

theorem middleProjection_pairing {n : ℕ}
    (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (x y : (W × (Fin n → ℚ)) × U) :
    prodForm (prodForm B (standardRatForm n)) C
        (middleCoordinateInclusion n (middleCoordinateProjection n x)) y =
      prodForm (prodForm B (standardRatForm n)) C x
        (middleCoordinateInclusion n (middleCoordinateProjection n y)) := by
  simp [middleCoordinateInclusion, middleCoordinateProjection, prodForm_apply]

theorem middleProjection_eigenvalues_eq_of_pairing_ne_zero {n : ℕ}
    (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    {x y : (W × (Fin n → ℚ)) × U} {a b : ℚ}
    (hx : middleCoordinateInclusion n (middleCoordinateProjection n x) = a • x)
    (hy : middleCoordinateInclusion n (middleCoordinateProjection n y) = b • y)
    (hxy : prodForm (prodForm B (standardRatForm n)) C x y ≠ 0) : a = b := by
  have h := middleProjection_pairing B C x y
  rw [hx, hy] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ hxy (by simpa only [mul_comm] using h)

end SRG266.Lattice
