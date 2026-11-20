import Tengoku.Hellingerrepolean4.Hellinger.ColumnSelection
import Tengoku.Hellingerrepolean4.Hellinger.ShearNoise

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The selected input coordinates and remaining coordinates form an actual
equivalence of cubes. This equivalence preserves the product BSC exactly. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.PivotCoordinates
open F2Model ChannelSections

variable {n k : ℕ}

abbrev Remaining (a : Fin k ↪ Fin n) := {j : Fin n // j ∉ Set.range a}

noncomputable instance remainingFintype (a : Fin k ↪ Fin n) : Fintype (Remaining a) :=
  Fintype.ofFinite _

def indexEquiv (a : Fin k ↪ Fin n) : Fin k ⊕ Remaining a ≃ Fin n := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective a a.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range a))

/--
@isnad1 id=eq.0h4v.s6.03e58239d17c from=translated src=- shape=d2d8f30d vocab=2988e9db
-/
@[simp] theorem indexEquiv_inl (a : Fin k ↪ Fin n) (i : Fin k) :
    indexEquiv a (Sum.inl i) = a i := rfl

/--
@isnad1 id=eq.0h4v.s7.7487fa9ea937 from=translated src=- shape=a8d1d1f2 vocab=39d7ddba
-/
@[simp] theorem indexEquiv_inr (a : Fin k ↪ Fin n) (i : Remaining a) :
    indexEquiv a (Sum.inr i) = i.val := rfl

def coordinates (a : Fin k ↪ Fin n) : Cube n ≃ (Cube k × (Remaining a → F2)) :=
  (Equiv.arrowCongr (indexEquiv a).symm (Equiv.refl F2)).trans
    (Equiv.sumArrowEquivProdArrow (Fin k) (Remaining a) F2)

/--
@isnad1 id=eq.0h5v.s6.a1f2f54fc951 from=translated src=- shape=b08a4f1c vocab=2b980052
-/
@[simp] theorem coordinates_fst (a : Fin k ↪ Fin n) (x : Cube n) (i : Fin k) :
    (coordinates a x).1 i = x (a i) := rfl

/--
@isnad1 id=eq.0h5v.s7.9d89353fee73 from=translated src=- shape=0592f872 vocab=98564ff0
-/
@[simp] theorem coordinates_snd (a : Fin k ↪ Fin n) (x : Cube n) (i : Remaining a) :
    (coordinates a x).2 i = x i.val := rfl

def coordinatesLinear (a : Fin k ↪ Fin n) : Cube n ≃ₗ[F2] (Cube k × (Remaining a → F2)) :=
  { coordinates a with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/--
@isnad1 id=eq.0h4v.s10.f59d9be4e830 from=translated src=- shape=eea749b6 vocab=8bd2d035
-/
@[simp] theorem coordinatesLinear_apply (a : Fin k ↪ Fin n) (x : Cube n) :
    coordinatesLinear a x = coordinates a x := rfl

/--
@isnad1 id=eq.1h6v.s9.c3c57b84ae67 from=translated src=- shape=643dc1d8 vocab=449c1f5e
-/
theorem noise_weight_coordinates (a : Fin k ↪ Fin n) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : Cube n) :
    (productChannel (noise (Fin k) ρ hρ) (noise (Remaining a) ρ hρ)).weight
      (coordinates a x) (coordinates a y) = (noise (Fin n) ρ hρ).weight x y := by
  have h := (indexEquiv a).prod_comp (fun i => (oneStep ρ hρ).weight (x i) (y i))
  rw [Fintype.prod_sum_type] at h
  exact h

/--
@isnad1 id=eq.1h6v.s9.2a751169a34c from=translated src=- shape=eead33f8 vocab=776fa820
-/
theorem noise_apply_coordinates (a : Fin k ↪ Fin n) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (g : (Cube k × (Remaining a → F2)) → ℝ) (x : Cube n) :
    (noise (Fin n) ρ hρ).apply (g ∘ coordinates a) x =
      (productChannel (noise (Fin k) ρ hρ) (noise (Remaining a) ρ hρ)).apply g (coordinates a x) := by
  unfold UniformChannel.apply
  rw [← (coordinates a).sum_comp
    (fun y => (productChannel (noise (Fin k) ρ hρ) (noise (Remaining a) ρ hρ)).weight
      (coordinates a x) y * g y)]
  simp only [noise_weight_coordinates, Function.comp_apply]

/--
@isnad1 id=eq.0h4v.s10.d9ee568c6e05 from=translated src=- shape=ec4b1508 vocab=f8c03f8d
-/
theorem selected_single (a : Fin k ↪ Fin n) (i : Fin k) :
    coordinatesLinear a (Pi.single (a i) 1) = (Pi.single i 1, 0) := by
  apply Prod.ext
  · funext j
    simp [coordinatesLinear, coordinates, indexEquiv, Pi.single_apply, a.injective.eq_iff]
  · funext j
    have hne : j.val ≠ a i := by
      intro h
      exact j.property ⟨i, h.symm⟩
    simp [coordinatesLinear, coordinates, indexEquiv, hne]

/--
@isnad1 id=eq.0h4v.s10.aa4ffe111bff from=translated src=- shape=9b6a9190 vocab=f764f8be
-/
theorem selected_assembly (a : Fin k ↪ Fin n) (x : Cube k) :
    (coordinatesLinear a).symm (x, 0) = ∑ i, x i • Pi.single (a i) 1 := by
  apply (coordinatesLinear a).injective
  simp only [LinearEquiv.apply_symm_apply, map_sum, map_smul, selected_single,
    Prod.smul_mk, smul_zero]
  apply Prod.ext
  · simp [Prod.fst_sum, ← Pi.single_smul, Finset.univ_sum_single]
  · simp [Prod.snd_sum]

/--
@isnad1 id=eq.1h6v.s11.913b97ad169f from=translated src=- shape=c6fc9f88 vocab=f2767dfc
-/
theorem quotient_assembly (a : Fin k ↪ Fin n) (b : Module.Basis (Fin k) F2 (Cube k))
    (L : Cube n →ₗ[F2] Cube k) (hb : ∀ i, b i = L (Pi.single (a i) 1)) (x : Cube k) :
    L ((coordinatesLinear a).symm (x, 0)) = b.equivFun.symm x := by
  rw [selected_assembly, map_sum, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hb]

def outsideLinear (a : Fin k ↪ Fin n) : (Remaining a → F2) →ₗ[F2] Cube n :=
  (coordinatesLinear a).symm.toLinearMap.comp (LinearMap.inr F2 (Cube k) (Remaining a → F2))

def quotientShear (a : Fin k ↪ Fin n) (b : Module.Basis (Fin k) F2 (Cube k))
    (L : Cube n →ₗ[F2] Cube k) : (Remaining a → F2) →ₗ[F2] Cube k :=
  b.equivFun.toLinearMap.comp (L.comp (outsideLinear a))

/--
@isnad1 id=eq.1h7v.s11.7ce8c7d6d4ec from=translated src=- shape=d7c0394a vocab=9ac101e6
-/
theorem quotient_coordinate_formula (a : Fin k ↪ Fin n) (b : Module.Basis (Fin k) F2 (Cube k))
    (L : Cube n →ₗ[F2] Cube k) (hb : ∀ i, b i = L (Pi.single (a i) 1))
    (x : Cube k) (z : Remaining a → F2) :
    L ((coordinates a).symm (x, z)) = b.equivFun.symm (x + quotientShear a b L z) := by
  have hsplit : (x, z) = (x, 0) + (0, z) := by simp
  change L ((coordinatesLinear a).symm (x, z)) = _
  rw [hsplit, map_add, map_add, quotient_assembly a b L hb x, map_add]
  congr 1
  exact (b.equivFun.symm_apply_apply (L (outsideLinear a z))).symm

end Hellinger.PivotCoordinates
