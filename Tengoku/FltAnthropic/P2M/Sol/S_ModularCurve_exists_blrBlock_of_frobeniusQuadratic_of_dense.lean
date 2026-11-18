import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_FrobeniusPowerDense
import Tengoku.FltAnthropic.Theorems.Thm_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_cayleyHamilton_forall_of_frobeniusQuadratic_of_dense

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_blrBlock_of_frobeniusQuadratic_of_dense.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_blrBlock_of_frobeniusQuadratic_of_dense

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Matrix BostonLenstraRibet

namespace ModularCurve
export _root_.ModularCurve (HeckeAlg heckeGen heckeTorsion mem_heckeTorsion_iff smul_mem_heckeTorsion FrobeniusQuadratic cayleyHamilton_forall_of_frobeniusQuadratic_of_dense)
open _root_.ModularCurve

noncomputable section

section Carrier

variable {G : Type*} [Group G] {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J] (𝔪 : Ideal HeckeAlg)

abbrev heckeTorsionCarrier : Type _ := Submodule.torsionBySet HeckeAlg J (𝔪 : Set HeckeAlg)

variable {𝔪}

def heckeTorsionRep : Representation (HeckeAlg ⧸ 𝔪) G (heckeTorsionCarrier (J := J) 𝔪) where
  toFun σ :=
    { toFun := fun x => ⟨σ • (x : J), smul_mem_heckeTorsion J σ x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add σ (x : J) (y : J))
      map_smul' := fun q x => by
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine Subtype.ext ?_
        have hxq : ((Ideal.Quotient.mk 𝔪 t • x : heckeTorsionCarrier (J := J) 𝔪) : J)
            = t • (x : J) := by
          rw [Submodule.torsionBySet.mk_smul]
          rfl
        have hyq : ((Ideal.Quotient.mk 𝔪 t •
            (⟨σ • (x : J), smul_mem_heckeTorsion J σ x.2⟩ : heckeTorsionCarrier (J := J) 𝔪) :
              heckeTorsionCarrier (J := J) 𝔪) : J) = t • (σ • (x : J)) := by
          rw [Submodule.torsionBySet.mk_smul]
          rfl
        show σ • ((Ideal.Quotient.mk 𝔪 t • x : heckeTorsionCarrier (J := J) 𝔪) : J) = _
        rw [hxq]
        refine Eq.trans (smul_comm σ t (x : J)) ?_
        exact hyq.symm }
  map_one' := LinearMap.ext fun x => Subtype.ext (one_smul G (x : J))
  map_mul' σ τ := LinearMap.ext fun x => Subtype.ext (mul_smul σ τ (x : J))

end Carrier

section Headline

variable {G : Type*} [Group G] {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

theorem exists_blrBlock_of_cayleyHamilton_of_neBot
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal)
    (ρ : G → Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hirr : ∀ W : Submodule (HeckeAlg ⧸ 𝔪) (Fin 2 → HeckeAlg ⧸ 𝔪),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : G} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1)
    (h2 : (2 : HeckeAlg ⧸ 𝔪) ≠ 0)
    (hCH : ∀ σ : G, ∀ x : J, x ∈ heckeTorsion J 𝔪 →
      ∀ t d : HeckeAlg, Ideal.Quotient.mk 𝔪 t = (ρ σ).trace →
        Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
        σ • σ • x - t • (σ • x) + d • x = 0)
    (hne : heckeTorsion J 𝔪 ≠ ⊥) :
    ∃ ι : (Fin 2 → HeckeAlg ⧸ 𝔪) →+ J,
      Function.Injective ι ∧
      (∀ (σ : G) (v : Fin 2 → HeckeAlg ⧸ 𝔪), ι ((ρ σ).mulVec v) = σ • ι v) ∧
      (∀ v : Fin 2 → HeckeAlg ⧸ 𝔪, ι v ∈ heckeTorsion J 𝔪) := by
  classical

  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪

  letI ρV : Representation (HeckeAlg ⧸ 𝔪) G (heckeTorsionCarrier (J := J) 𝔪) :=
    heckeTorsionRep (J := J) (𝔪 := 𝔪)

  have hCH' : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsionCarrier (J := J) 𝔪)) = 0 := by
    intro σ
    refine LinearMap.ext fun x => ?_

    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((ρ σ).trace)
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective ((ρ σ).det)
    have hxmem : (x : J) ∈ heckeTorsion J 𝔪 := x.2
    have key := hCH σ (x : J) hxmem t d ht hd

    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.one_apply, LinearMap.zero_apply]

    rw [← ZeroMemClass.coe_eq_zero, Submodule.coe_add, AddSubgroupClass.coe_sub]

    have hterm1 : ((ρV σ (ρV σ x) : heckeTorsionCarrier (J := J) 𝔪) : J)
        = σ • σ • (x : J) := rfl
    have hterm2 : (((ρ σ).trace • (ρV σ x) : heckeTorsionCarrier (J := J) 𝔪) : J)
        = t • (σ • (x : J)) := by
      rw [← ht, Submodule.torsionBySet.mk_smul, SetLike.val_smul]
      rfl
    have hterm3 : (((ρ σ).det • x : heckeTorsionCarrier (J := J) 𝔪) : J) = d • (x : J) := by
      rw [← hd, Submodule.torsionBySet.mk_smul, SetLike.val_smul]
    rw [hterm1, hterm2, hterm3]
    exact key

  obtain ⟨v₀, hv₀mem, hv₀ne⟩ := (Submodule.ne_bot_iff _).mp hne
  have hV : ∃ v : heckeTorsionCarrier (J := J) 𝔪, v ≠ 0 :=
    ⟨⟨v₀, hv₀mem⟩, fun h => hv₀ne (congrArg Subtype.val h)⟩

  obtain ⟨φ, hφinj, hφequiv⟩ :=
    exists_embedding_of_irreducible_of_odd (ρV := ρV) (ρ := ρ) hρ hCH' hirr hc2 hcdet h2 hV

  refine ⟨((Submodule.torsionBySet HeckeAlg J
      (𝔪 : Set HeckeAlg)).subtype.toAddMonoidHom).comp φ.toAddMonoidHom, ?_, ?_, ?_⟩
  ·
    intro v w h
    exact hφinj (Subtype.ext h)
  ·
    intro σ v
    exact congrArg Subtype.val (hφequiv σ v)
  ·
    intro v
    exact (φ v).2

end Headline

end

end ModularCurve
open scoped _root_.P2MW.S_ModularCurve_exists_blrBlock_of_frobeniusQuadratic_of_dense.ModularCurve

theorem solution {J : Type*} [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ModularCurve.HeckeAlg ⧸ 𝔪))
    (hirr : ∀ (W : Submodule (ModularCurve.HeckeAlg ⧸ 𝔪) (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪)),
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1)
    (h2 : (2 : ModularCurve.HeckeAlg ⧸ 𝔪) ≠ 0)
    (hES : ModularCurve.FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧ Ideal.Quotient.mk 𝔪 ((ℓ : ModularCurve.HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ModularCurve.heckeTorsion J 𝔪 : Set J)))
    (hne : ModularCurve.heckeTorsion J 𝔪 ≠ ⊥) :
    ∃ ι : (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪) →+ J, Function.Injective ι ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪), ι ((ρ σ).mulVec v) = σ • ι v) ∧
      ∀ (v : Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪), ι v ∈ ModularCurve.heckeTorsion J 𝔪 :=
  ModularCurve.exists_blrBlock_of_cayleyHamilton_of_neBot 𝔪 hmax (⇑ρ) (fun σ τ => map_mul ρ σ τ) hirr
    hc2 hcdet h2
    (ModularCurve.cayleyHamilton_forall_of_frobeniusQuadratic_of_dense N p 𝔪 hp ρ hES hS hatt hdense)
    hne
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
