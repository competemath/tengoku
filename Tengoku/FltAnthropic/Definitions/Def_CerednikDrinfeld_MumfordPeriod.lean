import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_Ribbon
import Tengoku.Seed.Combinatorics.SimpleGraph.Dart
import Tengoku.Seed.Combinatorics.SimpleGraph.Acyclic
import Tengoku.Seed.GroupTheory.GroupAction.Quotient
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Algebra.Module.Torsion.Basic
import Tengoku.Seed.LinearAlgebra.BilinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
noncomputable section
namespace CerednikDrinfeld
namespace Mumford

open ModularCurve MulAction

class GraphAction (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) : Prop where
  smul_adj : ∀ (g : G) {v w : W}, 𝒯.Adj v w → 𝒯.Adj (g • v) (g • w)

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

instance dartAction : MulAction G 𝒯.Dart where
  smul g d := ⟨(g • d.fst, g • d.snd), GraphAction.smul_adj g d.adj⟩
  one_smul d := SimpleGraph.Dart.ext _ _ (Prod.ext (one_smul G d.fst) (one_smul G d.snd))
  mul_smul g h d := SimpleGraph.Dart.ext _ _ (Prod.ext (mul_smul g h d.fst) (mul_smul g h d.snd))

/--
@isnad1 id=eq.0h5v.s6.3ead64d9aace from=translated src=- shape=8be2d1f1 vocab=5ba8c874
-/
@[simp] theorem smul_dart_fst (g : G) (d : 𝒯.Dart) : (g • d).fst = g • d.fst := rfl
/--
@isnad1 id=eq.0h5v.s6.b0d6e801861f from=translated src=- shape=8be2d1f1 vocab=149c98f0
-/
@[simp] theorem smul_dart_snd (g : G) (d : 𝒯.Dart) : (g • d).snd = g • d.snd := rfl

/--
@isnad1 id=eq.0h5v.s7.0a218c3cc020 from=translated src=- shape=97ce238e vocab=b54b979d
-/
theorem smul_dart_symm (g : G) (d : 𝒯.Dart) : (g • d).symm = g • d.symm := rfl

abbrev QuotEdge (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯] :=
  orbitRel.Quotient G 𝒯.Dart

abbrev QuotVert (G : Type) [Group G] (W : Type) [MulAction G W] := orbitRel.Quotient G W

/--
@isnad1 id=eq.0h5v.s7.37f5039d19f6 from=translated src=- shape=0f165e10 vocab=b3e15938
-/
theorem card_stabilizer_smul (g : G) (d : 𝒯.Dart) :
    Nat.card (stabilizer G (g • d)) = Nat.card (stabilizer G d) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

variable (G) in

def stabWidth (e : QuotEdge G 𝒯) : ℕ+ :=
  Nat.toPNat' (Nat.card (stabilizer G e.out))

/--
@isnad1 id=eq.0h4v.s6.0fd5665f5798 from=translated src=- shape=c7ec6518 vocab=001b7125
-/
theorem stabWidth_mk (d : 𝒯.Dart) :
    stabWidth G 𝒯 (Quotient.mk'' d) = Nat.toPNat' (Nat.card (stabilizer G d)) :=
  congrArg Nat.toPNat' (Nat.card_congr
    (stabilizerEquivStabilizerOfOrbitRel (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d)).toEquiv)

variable (G) in

def quotientDegeneracyData : DegeneracyData (QuotEdge G 𝒯) (QuotVert G W) where
  a := Quotient.map' (fun d : 𝒯.Dart => d.fst) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  b := Quotient.map' (fun d : 𝒯.Dart => d.snd) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  w := stabWidth G 𝒯

variable (G) in

def quotientReversal : QuotEdge G 𝒯 → QuotEdge G 𝒯 :=
  Quotient.map' SimpleGraph.Dart.symm (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)

variable (G) in

def formalU [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [Fintype (QuotVert G W)]
    [DecidableEq (QuotVert G W)] :
    Matrix (QuotEdge G 𝒯) (QuotEdge G 𝒯) ℤ :=
  (degeneracyMatrix (quotientDegeneracyData G 𝒯).b).transpose * degeneracyMatrix (quotientDegeneracyData G 𝒯).a
    - Matrix.of fun e e' => if quotientReversal G 𝒯 e' = e then 1 else 0

structure PeriodDatum {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (K L : Type) [Field K] [Field L] [Algebra K L] (ord : Additive Kˣ →+ ℤ) where

  Q : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D) →ₗ[ℤ] Additive Kˣ

  Q_symm : ∀ x y, Q x y = Q y x

  ord_Q : ∀ x y, ord (Q x y) = ribbonGram D x y

def PeriodDatum.HeckeAdjointable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)
    (H : HeckeData D) : Prop :=
  ∀ (ℓ : Nat.Primes) (y : ↥(ribbonKernel D)), ∃ y' : ↥(ribbonKernel D),
    ∀ z : ↥(ribbonKernel D), P.Q y (heckeKernelMap H ℓ z) = P.Q y' z

def unitsBaseChange (K L : Type) [Field K] [Field L] [Algebra K L] : Additive Kˣ →ₗ[ℤ] Additive Lˣ :=
  (MonoidHom.toAdditive (Units.map (algebraMap K L).toMonoidHom)).toIntLinearMap

/--
@isnad1 id=eq.0h3v.s9.daa134efc92d from=translated src=- shape=96aaedb6 vocab=219e302f
-/
@[simp] theorem unitsBaseChange_apply (K L : Type) [Field K] [Field L] [Algebra K L] (u : Kˣ) :
    unitsBaseChange K L (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u) := rfl

namespace PeriodDatum
variable {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)


abbrev TorusPoints (P : PeriodDatum D K L ord) : Type := ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ

def QL : ↥(ribbonKernel D) →ₗ[ℤ] P.TorusPoints := P.Q.compr₂ (unitsBaseChange K L)

/--
@isnad1 id=eq.0h9v.s13.845132361606 from=translated src=- shape=509a0882 vocab=fcc6e652
-/
@[simp] theorem QL_apply (x y : ↥(ribbonKernel D)) : P.QL x y = unitsBaseChange K L (P.Q x y) := rfl

def periodLattice : Submodule ℤ P.TorusPoints := LinearMap.range P.QL

abbrev JacPoints : Type := P.TorusPoints ⧸ P.periodLattice

def U : Submodule ℤ P.TorusPoints := (Submodule.torsion ℤ P.JacPoints).comap P.periodLattice.mkQ

def π : ↥P.U →ₗ[ℤ] P.JacPoints := P.periodLattice.mkQ ∘ₗ P.U.subtype

def IsTorsionOf (T : Type) [AddCommGroup T] : Prop :=
  ∃ e : ↥P.U →+ T, (∀ t : T, IsOfFinAddOrder t → t ∈ e.range) ∧ (∀ u, IsOfFinAddOrder (e u)) ∧
    ∀ u : ↥P.U, e u = 0 ↔ (u : P.TorusPoints) ∈ P.periodLattice
end PeriodDatum

end Mumford
end CerednikDrinfeld
end
