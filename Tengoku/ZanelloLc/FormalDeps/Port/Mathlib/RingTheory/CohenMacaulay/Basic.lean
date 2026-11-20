/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module

public import Tengoku.Seed.RingTheory.KrullDimension.Regular
public import Tengoku.Seed.RingTheory.Regular.Flat
public import Tengoku.ZanelloLc.FormalDeps.Port.Mathlib.RingTheory.Regular.Ischebeck

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Definition of Cohen-Macaulay Ring

In this file, we define a `R`-module `M` is Cohen Macaulay module if it is zero or
`Module.supportDim R M = IsLocalRing.depth M`. We also define a local ring `R`
`IsCohenMacaulayLocalRing` if `ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)`,
a commutative ring is Cohen Macaulay if its localization at every prime `IsCohenMacaulayLocalRing`.

# Main definition and results

* `ModuleCat.IsCohenMacaulay` : A `R`-module `M` is Cohen Macaulay if it is zero or
  `Module.supportDim R M = IsLocalRing.depth M`.

* `isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay` : For any prime ideal `p` and
  finitely generated `R`-module `M`, `Module.supportDim Rₚ Mₚ = p.depth M`

* `isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay` : For any prime ideal `p` and
  finitely generated `R`-module `M`, `Mₚ` is Cohen Macaulay as `Rₚ` module.

* `IsCohenMacaulayLocalRing` : A local ring is Cohen Macaulay if
  `ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)`.

* `IsCohenMacaulayRing` : A commutative ring is Cohen Macaulay if its localization at every prime
  `IsCohenMacaulayLocalRing`

* `isCohenMacaulayRing_iff` : A commutative ring is Cohen Macaulay iff its localization at
  every maximal ideal `IsCohenMacaulayLocalRing`

-/

@[expose] public section
namespace Tengoku.ZanelloLc end Tengoku.ZanelloLc open Tengoku.ZanelloLc 
universe v' v u' u

variable {R : Type u} [CommRing R]

open RingTheory.Sequence IsLocalRing ModuleCat
open scoped Pointwise

/-- A `R`-module `M` is Cohen Macaulay if it is zero or
`Module.supportDim R M = IsLocalRing.depth M`.-/
class ModuleCat.IsCohenMacaulay [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M

/--
@isnad1 id=iff.0h2v.s6.d3cb3b830d1c from=translated src=- shape=af6dcde5 vocab=115b159d
-/
lemma ModuleCat.isCohenMacaulay_iff [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) :
    M.IsCohenMacaulay ↔ Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/--
@isnad1 id=eq.0h2v.s6.3efeb11578b4 from=translated src=- shape=11d2d1be vocab=84768a11
-/
lemma ModuleCat.depth_eq_supportDim_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay] [ntr : Nontrivial M] :
    Module.supportDim R M = IsLocalRing.depth M := by
  have : ¬ Subsingleton M := not_subsingleton_iff_nontrivial.mpr ntr
  have := M.isCohenMacaulay_iff.mp cm
  tauto

/--
@isnad1 id=eq.0h2v.s6.a9834ec5d0a0 from=translated src=- shape=4f373394 vocab=3a93ffe4
-/
lemma ModuleCat.depth_eq_supportDim_unbot_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay] [ntr : Nontrivial M] :
    (Module.supportDim R M).unbot
    (Module.supportDim_ne_bot_of_nontrivial R M) = IsLocalRing.depth M := by
  simp [M.depth_eq_supportDim_of_cohenMacaulay]

/--
@isnad1 id=iscohenm.0h4v.s5.cc56a29cac10 from=translated src=- shape=c311fbfc vocab=4aed5baa
-/
lemma ModuleCat.IsCohenMacaulay_of_iso [IsLocalRing R] [Small.{v} R] {M M' : ModuleCat.{v} R}
    (e : M ≅ M') [M.IsCohenMacaulay] : M'.IsCohenMacaulay := by
  rw [M'.isCohenMacaulay_iff]
  by_cases ntr : Nontrivial M
  · right
    rw [← IsLocalRing.depth_eq_of_iso e,
      ← Module.supportDim_eq_of_equiv e.toLinearEquiv, M.depth_eq_supportDim_of_cohenMacaulay]
  · simp [← e.toLinearEquiv.subsingleton_congr, not_nontrivial_iff_subsingleton.mp ntr]

section IsLocalization

variable [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [Small.{v} R]

/--
@isnad1 id=iff.2h3v.s10.38d4757a7e3a from=translated src=- shape=e4c3d1bd vocab=899f6fe4
-/
lemma _root_.Tengoku.ZanelloLc.quotSMulTop_isCohenMacaulay_iff_isCohenMacaulay (M : ModuleCat.{v} R) [Module.Finite R M]
    (r : R) (reg : IsSMulRegular M r) (mem : r ∈ maximalIdeal R) :
     M.IsCohenMacaulay ↔ (ModuleCat.of R (QuotSMulTop r M)).IsCohenMacaulay := by
  simp only [ModuleCat.isCohenMacaulay_iff]
  by_cases ntr : Subsingleton M
  · have : Subsingleton (QuotSMulTop r M) := Function.Surjective.subsingleton
      (Submodule.mkQ_surjective _)
    simp [ntr, this]
  · have ntr1 : Nontrivial M := not_subsingleton_iff_nontrivial.mp ntr
    have ntr2 : Nontrivial (QuotSMulTop r M) := quotSMulTop_nontrivial mem M
    simp only [not_subsingleton_iff_nontrivial.mpr ntr2, false_or, ntr]
    rw [← Module.supportDim_quotSMulTop_succ_eq_supportDim reg mem,
      ← IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth M r reg mem, WithBot.coe_add]
    exact ENat.WithBot.add_natCast_cancel

/--
@isnad1 id=iff.1h3v.s9.d04c777b36af from=translated src=- shape=ee149521 vocab=576d526d
-/
lemma _root_.Tengoku.ZanelloLc.quotient_regular_isCohenMacaulay_iff_isCohenMacaulay
    (M : ModuleCat.{v} R) [Module.Finite R M] (rs : List R) (reg : IsRegular M rs) :
    M.IsCohenMacaulay ↔
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))).IsCohenMacaulay := by
  have ntr2 : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
    (IsRegular.quot_ofList_smul_nontrivial reg ⊤)
  have ntr1 : Nontrivial M := Function.Surjective.nontrivial (Submodule.mkQ_surjective
    (Ideal.ofList rs • (⊤ : Submodule R M)))
  simp only [isCohenMacaulay_iff, ← not_nontrivial_iff_subsingleton, ntr1, not_true_eq_false,
    false_or, ntr2]
  rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular rs reg,
    ← depth_quotient_regular_sequence_add_length_eq_depth M rs reg, WithBot.coe_add]
  exact ENat.WithBot.add_natCast_cancel

variable [p.IsPrime] {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]

/-- Turn a `R`-linear map into `algebraMap R A`-semilinear map if its target is an `A`-module.-/
abbrev _root_.Tengoku.ZanelloLc.SemiLinearMapAlgebraMapOfLinearMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R A] N where
  __ := f
  map_smul' m r := by simp

/-- Turn a `algebraMap R A`-semilinear map into a `R`-linear map.-/
abbrev _root_.Tengoku.ZanelloLc.LinearMapOfSemiLinearMapAlgebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₛₗ[algebraMap R A] N) : M →ₗ[R] N where
  __ := f
  map_smul' m r := by simp

variable (Rₚ) in
/-- Given `R`-algebra `Rₚ`, `R`-module `M` and `Rₚ`-module `Mₚ` and `f : M →ₗ[R] Mₚ`,
The linear map `QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ` lifted from `f`.-/
abbrev _root_.Tengoku.ZanelloLc.quotSMulTop_isLocalizedModule_map (x : R) (M : Type*) [AddCommGroup M] [Module R M]
    (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) :
    QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ :=
  LinearMapOfSemiLinearMapAlgebraMap (Submodule.mapQ _ _
    (SemiLinearMapAlgebraMapOfLinearMap f)
    (fun m hm ↦ by
      rw [← Submodule.ideal_span_singleton_smul] at hm
      simp only [Submodule.mem_comap, LinearMap.coe_mk, LinearMap.coe_toAddHom]
      refine Submodule.smul_induction_on hm (fun r hr m hm ↦ ?_)
        (fun m1 m2 hm1 hm2 ↦ by simpa using Submodule.add_mem _ hm1 hm2)
      rcases Ideal.mem_span_singleton'.mp hr with ⟨r', hr'⟩
      simpa only [← hr', map_smul, mul_comm r' x, ← smul_smul,
        algebra_compatible_smul Rₚ x (r' • f m)]
        using Submodule.smul_mem_pointwise_smul (r' • f m) ((algebraMap R Rₚ) x) ⊤ hm))

variable (Rₚ) in
omit [IsLocalRing R] [IsNoetherianRing R] [Small.{v, u} R] in
/--
@isnad1 id=atprime.0h7v.s10.6cfe6724503a from=translated src=- shape=0cd5b6bb vocab=03ae7f71
-/
lemma _root_.Tengoku.ZanelloLc.isLocalizedModule_quotSMulTop_isLocalizedModule_map (x : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    IsLocalizedModule.AtPrime p (quotSMulTop_isLocalizedModule_map Rₚ x M Mₚ f) where
  map_units r := by
    let alg := (Algebra.algHom R Rₚ (Module.End Rₚ (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ)))
    rcases isUnit_iff_exists.mp (IsUnit.algebraMap_of_algebraMap (r := r.1) alg.toLinearMap
      (map_one alg) (IsLocalization.map_units Rₚ r)) with ⟨s, hs1, hs2⟩
    exact isUnit_iff_exists.mpr ⟨LinearMap.restrictScalars R s,
      ⟨LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs1 (Eq.refl x)),
        LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs2 (Eq.refl x))⟩⟩
  surj y := by
    induction y using Submodule.Quotient.induction_on
    rename_i y
    rcases IsLocalizedModule.surj (S := p.primeCompl) (f := f) y with ⟨z, hz⟩
    use (Submodule.Quotient.mk z.1, z.2)
    simp [← hz]
  exists_of_eq {y1 y2} h := by
    induction y1 using Submodule.Quotient.induction_on
    induction y2 using Submodule.Quotient.induction_on
    rename_i y1 y2
    simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, Submodule.mapQ_apply] at h
    have h := (Submodule.Quotient.mk_eq_zero _).mp (sub_eq_zero_of_eq h)
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨m, _, hm⟩
    rcases IsLocalizedModule.surj p.primeCompl f m with ⟨⟨z, s⟩, hz⟩
    have eq : f (s • (y1 - y2)) = f (x • z) := by simp [← hm, ← hz, smul_comm s x m]
    rcases IsLocalizedModule.exists_of_eq (S := p.primeCompl) eq with ⟨c, hc⟩
    use c * s
    apply sub_eq_zero.mp
    have h : (0 : QuotSMulTop x M) = Submodule.Quotient.mk (c • s • (y1 - y2)) := by
      symm
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [hc]
      rw [Submonoid.smul_def, smul_comm (c : R) x z]
      exact Submodule.smul_mem_pointwise_smul (c • z) x ⊤ Submodule.mem_top
    simp [h, smul_sub, mul_smul]

variable [Small.{v'} Rₚ] [IsNoetherianRing Rₚ]
  (M : ModuleCat.{v} R) (Mₚ : ModuleCat.{v'} Rₚ) [Module R Mₚ] [IsScalarTower R Rₚ Mₚ]
  (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]

include p f

end IsLocalization

-- have some universe problem may have better statement using `IsLocalizedModule`

variable (R)

/-- A local ring is Cohen Macaulay if `ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)`.-/
class _root_.Tengoku.ZanelloLc.IsCohenMacaulayLocalRing : Prop extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

/--
@isnad1 id=iff.0h1v.s5.971f607293db from=translated src=- shape=fe070d63 vocab=06dd8c7e
-/
lemma _root_.Tengoku.ZanelloLc.isCohenMacaulayLocalRing_def [IsLocalRing R] : IsCohenMacaulayLocalRing R ↔
    ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/--
@isnad1 id=iff.0h1v.s5.b04c574c570f from=translated src=- shape=191a1445 vocab=b2636129
-/
lemma _root_.Tengoku.ZanelloLc.isCohenMacaulayLocalRing_iff [IsLocalRing R] :
    IsCohenMacaulayLocalRing R ↔ (ModuleCat.of R R).IsCohenMacaulay := by
  simp [isCohenMacaulayLocalRing_def, isCohenMacaulay_iff,
    not_subsingleton_iff_nontrivial.mpr inferInstance, Module.supportDim_self_eq_ringKrullDim]

/-- A commutative ring is Cohen Macaulay if its localization at every prime
`IsCohenMacaulayLocalRing`.-/
class _root_.Tengoku.ZanelloLc.IsCohenMacaulayRing : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p)

/--
@isnad1 id=iff.0h1v.s5.11c80a91f43a from=translated src=- shape=f7df49f2 vocab=702d0cd8
-/
lemma _root_.Tengoku.ZanelloLc.isCohenMacaulayRing_def : IsCohenMacaulayRing R ↔
    ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/--
@isnad1 id=iff.0h1v.s6.1eea57b14604 from=translated src=- shape=e8abf496 vocab=3d238626
-/
lemma _root_.Tengoku.ZanelloLc.isCohenMacaulayRing_def' : IsCohenMacaulayRing R ↔
  ∀ p : PrimeSpectrum R, IsCohenMacaulayLocalRing (Localization.AtPrime p.1) :=
  ⟨fun ⟨h⟩ ↦ fun p ↦ h p.1 p.2, fun h ↦ ⟨fun p hp ↦ h ⟨p, hp⟩⟩⟩

open Ideal

end
-- Tengoku: root names of this library moved to Tengoku.ZanelloLc so they do not collide with other libraries (generated)
