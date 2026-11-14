import Tengoku.TdaLib.TDA.Persistence.RankInvariant
import Tengoku.Seed.Data.Rat.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u
namespace TDA.Persistence
open CategoryTheory
variable {k : Type u} [Field k]

namespace RankExampleFixtures

def oneStageDiagram : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k k
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

instance oneStageFD (i : Fin 1) :
    FiniteDimensional k ((oneStageDiagram (k := k)).obj i) := by
  change FiniteDimensional k k
  infer_instance

theorem oneStageMultiplicity (M : PModule.{u,0,u} k (Fin 1))
    [∀ i : Fin 1, FiniteDimensional k (M.obj i)] :
    moduleMultiplicityInteger M 0 1 = Module.finrank k (M.obj 0) := by
  have hself := moduleRankInteger_fin M (0 : Fin 1) (0 : Fin 1) (le_refl _)
  have hr : structureMapRank M (0 : Fin 1) 0 (le_refl _) =
      Module.finrank k (M.obj 0) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  simp only [moduleMultiplicityInteger, Nat.cast_zero, Nat.cast_one]
  norm_num only
  simp only [moduleRankInteger_neg_one]
  rw [show moduleRankInteger M 0 1 = 0 from moduleRankInteger_at_size M 0]
  change moduleRankInteger M 0 0 = _ at hself
  rw [hself, hr]
  ring

theorem oneStageField : moduleMultiplicityInteger (oneStageDiagram (k := k)) 0 1 = 1 := by
  rw [oneStageMultiplicity]
  change ((Module.finrank k k : ℕ) : ℤ) = 1
  rw [Module.finrank_self]
  rfl

theorem oneStageZeroFiber (M : PModule.{u,0,u} k (Fin 1))
    [∀ i : Fin 1, FiniteDimensional k (M.obj i)]
    [Subsingleton (M.obj (0 : Fin 1))] : moduleMultiplicityInteger M 0 1 = 0 := by
  rw [oneStageMultiplicity]
  exact_mod_cast Module.finrank_zero_of_subsingleton (R := k) (M := M.obj (0 : Fin 1))

def oneStageZeroDiagram : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k (Fin 0 → k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

instance oneStageZeroFD (i : Fin 1) :
    FiniteDimensional k ((oneStageZeroDiagram (k := k)).obj i) := by
  change FiniteDimensional k (Fin 0 → k)
  infer_instance

theorem oneStageZero : moduleMultiplicityInteger (oneStageZeroDiagram (k := k)) 0 1 = 0 := by
  have hzero : Subsingleton ((oneStageZeroDiagram (k := k)).obj (0 : Fin 1)) := by
    change Subsingleton (Fin 0 → k)
    infer_instance
  exact @oneStageZeroFiber k _ (oneStageZeroDiagram (k := k))
    (fun i => oneStageZeroFD i) hzero

theorem twoStageValues (M : PModule.{u,0,u} k (Fin 2))
    [∀ i : Fin 2, FiniteDimensional k (M.obj i)] :
    moduleMultiplicityInteger M 0 1 =
      (Module.finrank k (M.obj (0 : Fin 2)) : ℤ) -
        structureMapRank M 0 1 (by decide) ∧
    moduleMultiplicityInteger M 0 2 =
      (structureMapRank M 0 1 (by decide) : ℤ) ∧
    moduleMultiplicityInteger M 1 2 =
      (Module.finrank k (M.obj (1 : Fin 2)) : ℤ) -
        structureMapRank M 0 1 (by decide) := by
  have h00 := moduleRankInteger_fin M (0 : Fin 2) 0 (le_refl _)
  have h01 := moduleRankInteger_fin M (0 : Fin 2) 1 (by decide)
  have h11 := moduleRankInteger_fin M (1 : Fin 2) 1 (le_refl _)
  have h0 : structureMapRank M 0 0 (le_refl (0 : Fin 2)) =
      Module.finrank k (M.obj 0) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  have h1 : structureMapRank M 1 1 (le_refl (1 : Fin 2)) =
      Module.finrank k (M.obj 1) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  simp only [moduleMultiplicityInteger, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  norm_num only
  simp only [moduleRankInteger_neg_one]
  rw [show moduleRankInteger M 0 2 = 0 from moduleRankInteger_at_size M 0,
    show moduleRankInteger M 1 2 = 0 from moduleRankInteger_at_size M 1]
  change moduleRankInteger M 0 0 = _ at h00
  change moduleRankInteger M 0 1 = _ at h01
  change moduleRankInteger M 1 1 = _ at h11
  rw [h00, h01, h11, h0, h1]
  constructor
  · ring
  · constructor <;> ring

instance identityTwoStageFD (i : Fin 2) :
    FiniteDimensional k ((identityTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

instance zeroTwoStageFD (i : Fin 2) :
    FiniteDimensional k ((zeroTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

theorem identityTwoStageRanks :
    structureMapRank (identityTransitionDiagram k) 0 1 (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = 1
  rw [LinearMap.range_id, finrank_top]
  exact Module.finrank_self k

theorem zeroTwoStageRanks :
    structureMapRank (zeroTransitionDiagram k) 0 1 (by decide) = 0 := by
  change Module.finrank k (LinearMap.range (0 : k →ₗ[k] k)) = 0
  simp

theorem identityTwoStage :
    moduleMultiplicityInteger (identityTransitionDiagram k) 0 1 = 0 ∧
    moduleMultiplicityInteger (identityTransitionDiagram k) 0 2 = 1 ∧
    moduleMultiplicityInteger (identityTransitionDiagram k) 1 2 = 0 := by
  have h := twoStageValues (identityTransitionDiagram k)
  rw [identityTwoStageRanks] at h
  simpa only [show Module.finrank k ((identityTransitionDiagram k).obj (0 : Fin 2)) = 1
      from Module.finrank_self k,
    show Module.finrank k ((identityTransitionDiagram k).obj (1 : Fin 2)) = 1
      from Module.finrank_self k, Nat.cast_one, sub_self] using h

theorem zeroTwoStage :
    moduleMultiplicityInteger (zeroTransitionDiagram k) 0 1 = 1 ∧
    moduleMultiplicityInteger (zeroTransitionDiagram k) 0 2 = 0 ∧
    moduleMultiplicityInteger (zeroTransitionDiagram k) 1 2 = 1 := by
  have h := twoStageValues (zeroTransitionDiagram k)
  rw [zeroTwoStageRanks] at h
  simpa only [show Module.finrank k ((zeroTransitionDiagram k).obj (0 : Fin 2)) = 1
      from Module.finrank_self k,
    show Module.finrank k ((zeroTransitionDiagram k).obj (1 : Fin 2)) = 1
      from Module.finrank_self k, Nat.cast_one, Nat.cast_zero, sub_zero] using h

end RankExampleFixtures

open RankExampleFixtures

private def threeStageDiagram (f : k →ₗ[k] k × k) (g : (k × k) →ₗ[k] k) :
    PModule.{u,0,u} k (Fin 3) where
  obj i := if i.val = 1 then ModuleCat.of k (k × k) else ModuleCat.of k k
  map {p q} h := by
    rcases p with ⟨p, hp⟩
    rcases q with ⟨q, hq⟩
    interval_cases p <;> interval_cases q
    · exact 𝟙 _
    · exact ModuleCat.ofHom f
    · exact ModuleCat.ofHom (g.comp f)
    · have hh : (1 : Fin 3) ≤ 0 := leOfHom h
      exact False.elim ((by decide : ¬(1 : Fin 3) ≤ 0) hh)
    · exact 𝟙 _
    · exact ModuleCat.ofHom g
    · have hh : (2 : Fin 3) ≤ 0 := leOfHom h
      exact False.elim ((by decide : ¬(2 : Fin 3) ≤ 0) hh)
    · have hh : (2 : Fin 3) ≤ 1 := leOfHom h
      exact False.elim ((by decide : ¬(2 : Fin 3) ≤ 1) hh)
    · exact 𝟙 _
  map_id i := by
    fin_cases i <;> apply ModuleCat.hom_ext <;> rfl
  map_comp {i j l} h1 h2 := by
    apply ModuleCat.hom_ext
    fin_cases i <;> fin_cases j <;> fin_cases l
    all_goals
      have hi := leOfHom h1
      have hj := leOfHom h2
      simp_all [Fin.le_iff_val_le_val]

private def includeFirst : k →ₗ[k] k × k :=
  { toFun := fun x => (x, 0)
    map_add' := by intros; ext <;> simp
    map_smul' := by intros; ext <;> simp }

private def projectFirst : (k × k) →ₗ[k] k := LinearMap.fst k k k
private def projectSecond : (k × k) →ₗ[k] k := LinearMap.snd k k k
