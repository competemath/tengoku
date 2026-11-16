import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_GaloisRep
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace FrobeniusEndo

section Pencil

variable {A : Type*} [AddCommGroup A]

def linePencil (ψ : A →+ A) (m n : ℤ) : A →+ A :=
  m • AddMonoidHom.id A - n • ψ

/--
@isnad1 id=eq.0h5v.s7.2bd92d90df87 from=translated src=- shape=0873bdbe vocab=2aa662a4
-/
@[simp] lemma linePencil_apply (ψ : A →+ A) (m n : ℤ) (P : A) :
    linePencil ψ m n P = m • P - n • ψ P :=
  rfl

def kerDeg (ψ : A →+ A) (m n : ℤ) : ℕ :=
  Nat.card (linePencil ψ m n).ker

/--
@isnad1 id=eq.0h4v.s6.817607ca079b from=translated src=- shape=edbadf2c vocab=8f75a665
-/
lemma kerDeg_def (ψ : A →+ A) (m n : ℤ) : kerDeg ψ m n = Nat.card (linePencil ψ m n).ker :=
  rfl

/--
@isnad1 id=iff.0h5v.s7.6eacca48619c from=translated src=- shape=c350500a vocab=f9cf0926
-/
lemma mem_ker_linePencil_iff (ψ : A →+ A) (m n : ℤ) (P : A) :
    P ∈ (linePencil ψ m n).ker ↔ m • P = n • ψ P := by
  rw [AddMonoidHom.mem_ker, linePencil_apply, sub_eq_zero]

end Pencil

section Frobenius

variable {R : Type*} {S : Type*} {k : Type*} [CommRing R] [CommRing S] [Field k] [DecidableEq k]
  [Algebra R S] [Algebra R k] [Algebra S k] [IsScalarTower R S k]
  (W : WeierstrassCurve R) (σ : k ≃ₐ[S] k)

abbrev frobEnd : (W⁄k).Point →+ (W⁄k).Point :=
  DistribSMul.toAddMonoidHom (W⁄k).Point σ

/--
@isnad1 id=eq.0h6v.s8.29d07b776fc6 from=translated src=- shape=3f134b7c vocab=781e7156
-/
lemma frobEnd_apply (P : (W⁄k).Point) : frobEnd W σ P = σ • P :=
  rfl

abbrev frobPencilEnd (p : ℕ) (m n : ℤ) :
    Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄k).Point p) :=
  ((m : ZMod p) • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄k).Point p))) -
    (n : ZMod p) • galoisRepModuleEnd S W p σ

def FrobCharEqOnPoints (a : ℤ) (q : ℕ) : Prop :=
  ∀ P : (W⁄k).Point, σ • (σ • P) - a • (σ • P) + (q : ℤ) • P = 0

end Frobenius

end FrobeniusEndo

end
