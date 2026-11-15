import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Module_CommFamilyAnnPart
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeU
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeV
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_QExpansionDiff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RegularDifferentials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

open AlgebraicCurve

noncomputable def qExpGens (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) : Option ι → Module.End K (LaurentSeries K)
  | none => LaurentSeries.heckeU K p (Fact.out : p.Prime).pos
  | some i => LaurentSeries.heckeT K (ℓ i) (hℓ i) 2

/--
@isnad1 id=eq.1h4v.s6.e19abf447a90 from=translated src=- shape=5916c823 vocab=125563c4
-/
@[simp] theorem qExpGens_none (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) :
    qExpGens K p ℓ hℓ none = LaurentSeries.heckeU K p (Fact.out : p.Prime).pos := rfl

/--
@isnad1 id=eq.1h5v.s7.83a64126617f from=translated src=- shape=e59688fa vocab=e14523f8
-/
@[simp] theorem qExpGens_some (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) (i : ι) :
    qExpGens K p ℓ hℓ (some i) = LaurentSeries.heckeT K (ℓ i) (hℓ i) 2 := rfl

noncomputable def mTorsionDiffOf (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {σ : Type*} (F : Module.End.CommFamily K (LaurentSeries K) σ)
    (θbar : σ → K) : Submodule K (Ω[↥(modularFunctionFieldC K N)⁄K]) :=
  regularDifferentials K (modularFunctionFieldC K N) ⊓
    (F.annPart p θbar).comap (qExpansionDiffAlong (modularFunctionFieldC K N).val)

/--
@isnad1 id=iff.0h7v.s15.800242cbe8f8 from=translated src=- shape=db474aef vocab=1c585162
-/
theorem mem_mTorsionDiffOf_iff (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {σ : Type*} (F : Module.End.CommFamily K (LaurentSeries K) σ)
    (θbar : σ → K) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    ω ∈ mTorsionDiffOf K p N F θbar ↔
      ω ∈ regularDifferentials K (modularFunctionFieldC K N) ∧
        ∀ Q : MvPolynomial σ (ZMod p),
          MvPolynomial.aeval θbar (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q) = 0 →
            F.eval (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q)
              (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) = 0 := by
  rw [mTorsionDiffOf, Submodule.mem_inf, Submodule.mem_comap, Module.End.CommFamily.mem_annPart_iff]

noncomputable def mTorsionDiff (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i)
    (hcomm : ∀ a b : Option ι, Commute (qExpGens K p ℓ hℓ a) (qExpGens K p ℓ hℓ b))
    (θbar : Option ι → K) : Submodule K (Ω[↥(modularFunctionFieldC K N)⁄K]) :=
  mTorsionDiffOf K p N (Module.End.CommFamily.mk (qExpGens K p ℓ hℓ) hcomm) θbar

/--
@isnad1 id=iff.2h7v.s15.921a69378023 from=translated src=- shape=4f08005b vocab=191e229c
-/
theorem mem_mTorsionDiff_iff (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i)
    (hcomm : ∀ a b : Option ι, Commute (qExpGens K p ℓ hℓ a) (qExpGens K p ℓ hℓ b))
    (θbar : Option ι → K) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    ω ∈ mTorsionDiff K p N ℓ hℓ hcomm θbar ↔
      ω ∈ regularDifferentials K (modularFunctionFieldC K N) ∧
        ∀ Q : MvPolynomial (Option ι) (ZMod p),
          MvPolynomial.aeval θbar (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q) = 0 →
            (Module.End.CommFamily.mk (qExpGens K p ℓ hℓ) hcomm).eval
                (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q)
              (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) = 0 := by
  rw [mTorsionDiff, mem_mTorsionDiffOf_iff]

end ModularCurve
