import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroupHecke
import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_Ribbon

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def awayIdeal (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) : Ideal HeckeAlg :=
  Ideal.span ({t | ∃ n : ℕ, (n : HeckeAlg) ∈ 𝔪 ∧ t = n} ∪
    {t | ∃ ℓ : Nat.Primes, ℓ ∉ S ∧ ∃ b : ℤ,
      heckeGen ℓ - MvPolynomial.C b ∈ 𝔪 ∧ t = heckeGen ℓ - MvPolynomial.C b})

/--
@isnad1 id=le.0h2v.s7.aa228aeb26f7 from=translated src=- shape=a386c58b vocab=9dfc6ca7
-/
theorem awayIdeal_le (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) : awayIdeal S 𝔪 ≤ 𝔪 := by
  refine Ideal.span_le.2 ?_
  rintro t (⟨n, hn, rfl⟩ | ⟨ℓ, -, b, hb, rfl⟩)
  · exact hn
  · exact hb

/--
@isnad1 id=mem.1h3v.s7.729f4b3e2d1b from=translated src=- shape=3463c750 vocab=d75a256c
-/
theorem natCast_mem_awayIdeal {S : Finset Nat.Primes} {𝔪 : Ideal HeckeAlg} {n : ℕ}
    (hn : (n : HeckeAlg) ∈ 𝔪) : (n : HeckeAlg) ∈ awayIdeal S 𝔪 :=
  Ideal.subset_span (Or.inl ⟨n, hn, rfl⟩)

/--
@isnad1 id=mem.2h4v.s8.2f9324c5ee24 from=translated src=- shape=df1b63a4 vocab=4f2abd54
-/
theorem heckeGen_sub_C_mem_awayIdeal {S : Finset Nat.Primes} {𝔪 : Ideal HeckeAlg} {ℓ : Nat.Primes}
    (hℓ : ℓ ∉ S) {b : ℤ} (hb : heckeGen ℓ - MvPolynomial.C b ∈ 𝔪) :
    heckeGen ℓ - MvPolynomial.C b ∈ awayIdeal S 𝔪 :=
  Ideal.subset_span (Or.inr ⟨ℓ, hℓ, b, hb, rfl⟩)

def HasAwaySupport (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) (M : Type*) [AddCommGroup M]
    [Module HeckeAlg M] : Prop :=
  (awayIdeal S 𝔪 • ⊤ : Submodule HeckeAlg M) ≠ ⊤

def anemicInclusion (S : Finset Nat.Primes) :
    MvPolynomial {ℓ : Nat.Primes // ℓ ∉ S} ℤ →+* HeckeAlg :=
  (MvPolynomial.rename (Subtype.val : {ℓ : Nat.Primes // ℓ ∉ S} → Nat.Primes)).toRingHom

/--
@isnad1 id=eq.0h2v.s8.1700833c64ed from=translated src=- shape=d4e3d458 vocab=acc8e24f
-/
theorem anemicInclusion_X (S : Finset Nat.Primes) (ℓ : {ℓ : Nat.Primes // ℓ ∉ S}) :
    anemicInclusion S (MvPolynomial.X ℓ) = heckeGen ℓ.1 :=
  MvPolynomial.rename_X _ ℓ

def anemicContraction (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) :
    Ideal (MvPolynomial {ℓ : Nat.Primes // ℓ ∉ S} ℤ) :=
  𝔪.comap (anemicInclusion S)

/--
@isnad1 id=iff.0h3v.s9.c8c7289cf416 from=translated src=- shape=e9e1eea9 vocab=bcf12230
-/
theorem mem_anemicContraction {S : Finset Nat.Primes} {𝔪 : Ideal HeckeAlg}
    {t : MvPolynomial {ℓ : Nat.Primes // ℓ ∉ S} ℤ} :
    t ∈ anemicContraction S 𝔪 ↔ anemicInclusion S t ∈ 𝔪 :=
  Ideal.mem_comap

end ModularCurve

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}

/--
@isnad1 id=eq.0h3v.s7.214e31762e9e from=translated src=- shape=f09077cd vocab=00eab2f4
-/
theorem heckeDivisorAction_transpose (T : Matrix E E ℤ) (x : E → ℤ) :
    heckeDivisorAction T.transpose x = T.mulVec x := by
  ext j
  simp [heckeDivisorAction_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

namespace HeckeData

variable (H : HeckeData D)

structure LatticeHyp (H : HeckeData D) where

  n : Nat.Primes → ℤ

  colSum : ∀ ℓ, HeckeRowSums (H.T ℓ).transpose (n ℓ)

  nV : Nat.Primes → ℤ

  colSumV : ∀ ℓ, HeckeRowSums (H.Tv ℓ).transpose (nV ℓ)

variable (h : H.LatticeHyp)

def latticeOp (ℓ : Nat.Primes) : characterLattice E →ₗ[ℤ] characterLattice E :=
  heckeCharacterAction (H.T ℓ).transpose (h.colSum ℓ)

/--
@isnad1 id=eq.0h7v.s10.1a02fc3d1035 from=translated src=- shape=2b3f80ac vocab=ca5655ad
-/
theorem coe_latticeOp (ℓ : Nat.Primes) (x : characterLattice E) :
    (H.latticeOp h ℓ x : E → ℤ) = (H.T ℓ).mulVec x :=
  heckeDivisorAction_transpose _ _

/--
@isnad1 id=eq.0h8v.s12.dd0f33f6b6b2 from=translated src=- shape=313548d1 vocab=58c4740e
-/
theorem latticeOp_comm (ℓ ℓ' : Nat.Primes) (x : characterLattice E) :
    H.latticeOp h ℓ (H.latticeOp h ℓ' x) = H.latticeOp h ℓ' (H.latticeOp h ℓ x) := by
  apply Subtype.ext
  simp only [coe_latticeOp, Matrix.mulVec_mulVec, (H.comm ℓ ℓ').eq]

def latticeOpV (ℓ : Nat.Primes) : characterLattice V →ₗ[ℤ] characterLattice V :=
  heckeCharacterAction (H.Tv ℓ).transpose (h.colSumV ℓ)

/--
@isnad1 id=eq.0h7v.s10.3fe113fe046f from=translated src=- shape=bf190107 vocab=297bc209
-/
theorem coe_latticeOpV (ℓ : Nat.Primes) (x : characterLattice V) :
    (H.latticeOpV h ℓ x : V → ℤ) = (H.Tv ℓ).mulVec x :=
  heckeDivisorAction_transpose _ _

/--
@isnad1 id=eq.0h8v.s12.7c744f5ac815 from=translated src=- shape=11cc9d46 vocab=6bd03db9
-/
theorem latticeOpV_comm (ℓ ℓ' : Nat.Primes) (x : characterLattice V) :
    H.latticeOpV h ℓ (H.latticeOpV h ℓ' x) = H.latticeOpV h ℓ' (H.latticeOpV h ℓ x) := by
  apply Subtype.ext
  simp only [coe_latticeOpV, Matrix.mulVec_mulVec, (H.commv ℓ ℓ').eq]

end HeckeData

end CerednikDrinfeld
