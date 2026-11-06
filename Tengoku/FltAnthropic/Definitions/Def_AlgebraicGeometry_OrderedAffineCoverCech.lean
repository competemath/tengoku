import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Tengoku.Seed.AlgebraicGeometry.AffineScheme
import Tengoku.Seed.RingTheory.Finiteness.Defs
import Tengoku.Seed.LinearAlgebra.Quotient.Defs
import Tengoku.Seed.LinearAlgebra.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

structure Scheme.OrderedAffineCover (V : Scheme.{u}) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  iSup_eq_top : ⨆ i, U i = ⊤

attribute [instance] Scheme.OrderedAffineCover.instFintype Scheme.OrderedAffineCover.instLinearOrder

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance instFintypeIdx (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _

instance instDecidableEqIdx (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

variable (V) in

def ofAffine [IsAffine V] : V.OrderedAffineCover where
  ι := PUnit.{u + 1}
  U _ := ⊤
  isAffineOpen _ := isAffineOpen_top V
  iSup_eq_top := iSup_const

end Scheme.OrderedAffineCover

namespace Scheme.TwoAffineOpenCover

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)

def toOrderedAffineCover : X.OrderedAffineCover where
  ι := ULift.{u} (Fin 2)
  instLinearOrder := LinearOrder.lift' ULift.down ULift.down_injective
  U i := ![𝒱.U0, 𝒱.U1] i.down
  isAffineOpen i := by
    rcases i with ⟨i⟩
    fin_cases i
    · exact 𝒱.isAffineOpen_U0
    · exact 𝒱.isAffineOpen_U1
  iSup_eq_top := by
    rw [eq_top_iff, ← 𝒱.sup_eq_top]
    exact sup_le (le_iSup (fun i : ULift.{u} (Fin 2) => ![𝒱.U0, 𝒱.U1] i.down) ⟨0⟩)
      (le_iSup (fun i : ULift.{u} (Fin 2) => ![𝒱.U0, 𝒱.U1] i.down) ⟨1⟩)

end Scheme.TwoAffineOpenCover

structure OModulePresheaf {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) where

  obj : V.Opens → Type u
  [addCommGroup : ∀ U, AddCommGroup (obj U)]

  [module : ∀ U, Module R (obj U)]

  [moduleSections : ∀ U, Module Γ(V, U) (obj U)]

  [isScalarTower : ∀ U, letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    IsScalarTower R Γ(V, U) (obj U)]

  res : ∀ {U U' : V.Opens}, U ≤ U' → obj U' →ₗ[R] obj U

  res_smul : ∀ {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : obj U'),
    res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x

  res_refl : ∀ U, res (le_refl U) = LinearMap.id

  res_comp : ∀ {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U''), res (h.trans h') = res h ∘ₗ res h'

attribute [instance] OModulePresheaf.addCommGroup OModulePresheaf.module OModulePresheaf.moduleSections
  OModulePresheaf.isScalarTower

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem res_res {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U'') (x : F.obj U'') :
    F.res h (F.res h' x) = F.res (h.trans h') x := by
  rw [F.res_comp h h']; rfl

abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, F.obj (K.inter s)

def d (i : ℕ) : F.cochain K i →ₗ[R] F.cochain K (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

abbrev H0 : Submodule R (F.cochain K 0) := LinearMap.ker (F.d K 0)

abbrev HSucc (i : ℕ) : Type u :=
  LinearMap.ker (F.d K (i + 1)) ⧸ (LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype

def CechFinite : Prop := Module.Finite R (F.H0 K) ∧ ∀ i, Module.Finite R (F.HSucc K i)

def IsCoherent : Prop := ∀ U : V.affineOpens, Module.Finite Γ(V, U.1) (F.obj U.1)

def IsQuasicoherent : Prop :=
  ∀ (U : V.affineOpens) (f : Γ(V, U.1)),
    (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
        F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
      ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0)

def SupportedIn (Y : Closeds V) : Prop :=
  ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Y = ∅ → Subsingleton (F.obj U)

section TwoChart

variable (𝒱 : V.TwoAffineOpenCover)

end TwoChart

end OModulePresheaf

end AlgebraicGeometry

end
