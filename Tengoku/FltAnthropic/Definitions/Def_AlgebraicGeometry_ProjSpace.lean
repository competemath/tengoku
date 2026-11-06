import Tengoku.Seed.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Tengoku.Seed.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
import Tengoku.Seed.RingTheory.MvPolynomial.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section PnSetup

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

def grad0Equiv : R ≃+* (𝒜 0) where
  toFun r := ⟨C r, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ r)⟩
  invFun p := MvPolynomial.constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    ext : 1
    have hp : p.1.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp p.2
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [MvPolynomial.constantCoeff]
    · rw [MvPolynomial.coeff_C, ite_eq_right (Ne.symm hd)]
      by_contra h
      refine hd (Finsupp.ext fun i => ?_)

      have hdeg : (Finsupp.weight (1 : Fin (n + 1) → ℕ)) d = 0 := hp (fun h0 => h h0.symm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Finsupp.sum] at hdeg
      by_cases hi : i ∈ d.support
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hdeg i hi
      · exact Finsupp.notMem_support_iff.mp hi
  map_mul' a b := by ext : 1; simp
  map_add' a b := by ext : 1; simp

def π : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom)

end PnSetup

section StdCover

open MvPolynomial AlgebraicGeometry.Proj

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

end StdCover

section Setup

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/--
@isnad1 id=mem.0h3v.s8.a4ee721dcc1e from=translated src=- shape=6eb5528a vocab=7d23f883
-/
theorem X_mem_one (j : Fin (n + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R j)

def ratio (i k : Fin (n + 1)) : Away 𝒜 (MvPolynomial.X i) :=
  Away.mk 𝒜 (X_mem_one R n i) 1 (MvPolynomial.X k)
    (by simpa using X_mem_one R n k)

end Setup

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

end StdCover

section AdjoinRatio

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

end AdjoinRatio

section ProdOver

variable (R : Type u) [CommRing R]

def prodOverAux :
    ∀ {m : ℕ}, (Fin m → ℕ) → Σ (P : Scheme.{u}), P ⟶ Spec (.of R)
  | 0, _ => ⟨Spec (.of R), 𝟙 _⟩
  | m + 1, e =>
    let prev := @prodOverAux m (e ∘ Fin.succ)
    ⟨pullback (π R (e 0)) prev.2,
     pullback.fst _ _ ≫ π R (e 0)⟩

abbrev prodOver {m : ℕ} (e : Fin m → ℕ) : Scheme.{u} :=
  (prodOverAux R e).1

abbrev prodOverπ {m : ℕ} (e : Fin m → ℕ) :
    prodOver R e ⟶ Spec (.of R) :=
  (prodOverAux R e).2

end ProdOver

section MapGraded

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

end MapGraded

end ProjSpace

section Carrier

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

structure ChowDatum where

  m : ℕ

  e : Fin m → ℕ

  V' : Scheme.{u}

  p : V' ⟶ V

  ι : V' ⟶ ProjSpace.prodOver R e

  hp_proper : IsProper p

  hι_closed : IsClosedImmersion ι

  hover : ι ≫ ProjSpace.prodOverπ R e = p ≫ π

  U : V.Opens

  hU_dense : Dense (U : Set V)

  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatum.hp_proper ChowDatum.hι_closed ChowDatum.hp_isoU

end Carrier

section CarrierProj

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

structure ChowDatumProj where

  Nd : ℕ

  V' : Scheme.{u}

  p : V' ⟶ V

  ιN : V' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Nd + 1)) R)

  hp_proper : IsProper p

  hιN_closed : IsClosedImmersion ιN

  hoverN : ιN ≫ ProjSpace.π R Nd = p ≫ π

  U : V.Opens

  hU_dense : Dense (U : Set V)

  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatumProj.hp_proper ChowDatumProj.hιN_closed
  ChowDatumProj.hp_isoU

end CarrierProj

end AlgebraicGeometry

end
