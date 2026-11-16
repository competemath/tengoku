import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.RingTheory.Valuation.RamificationGroup
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_GaloisRep
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

/--
@isnad1 id=smulcomm.0h5v.s12.9a44079efb56 from=translated src=- shape=5eca1a03 vocab=2a4f959d
-/
instance instSMulCommClassAlgEquivZModTorsionBy (n : ℕ) :
    SMulCommClass (K ≃ₐ[S] K) (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  smul_comm σ c x :=
    ZMod.map_smul (DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ (W'⁄K).Point n) σ) c x

variable (S) in

def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →* Module.End (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleEnd (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)

/--
@isnad1 id=eq.0h7v.s13.18c4dcbacdf4 from=translated src=- shape=21277981 vocab=720628fc
-/
@[simp] lemma galoisRepModuleEnd_apply (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K)
    (x : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRepModuleEnd S W' n σ x = σ • x :=
  rfl

variable (S) in

def galoisTrace (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) : ZMod n :=
  LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) (galoisRepModuleEnd S W' n σ)

/--
@isnad1 id=eq.0h6v.s13.4606e570478c from=translated src=- shape=35aaae9d vocab=cc4a2fa0
-/
lemma galoisTrace_def (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) :
    galoisTrace S W' n σ =
      LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (galoisRepModuleEnd S W' n σ) :=
  rfl

end WeierstrassCurve.Affine.Point

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup K) • x = x ^ q

/--
@isnad1 id=mem.1h5v.s7.3d17e8727d58 from=translated src=- shape=aba17ff5 vocab=6ff8b506
-/
lemma IsFrobeniusAt.mem_decompositionSubgroup {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) : σ ∈ A.decompositionSubgroup K :=
  h.choose

/--
@isnad1 id=eq.1h6v.s11.2f6d9675c95e from=translated src=- shape=219be15a vocab=121a5ee6
-/
lemma IsFrobeniusAt.smul_residue_eq {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) (x : IsLocalRing.ResidueField A) :
    (⟨σ, h.mem_decompositionSubgroup⟩ : A.decompositionSubgroup K) • x = x ^ q :=
  h.choose_spec x

end ValuationSubring

end
