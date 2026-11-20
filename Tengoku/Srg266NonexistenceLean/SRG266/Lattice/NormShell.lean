/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

def NormShell {n : ℕ} (L : PDUnimodularLattice n) (q : ℕ) :=
  {v : L.carrier // L.pairing v v = (q : ℤ)}

/--
@isnad1 id=finite.0h3v.s3.4702a86d5aa6 from=translated src=- shape=364cbd43 vocab=1e09ccbb
-/
theorem normShell_finite {n : ℕ} (L : PDUnimodularLattice n) (q : ℕ) :
    Finite (NormShell L q) := by
  let := L.moduleFree
  let := L.moduleFinite
  let b : Module.Basis (Fin n) ℤ L.carrier :=
    Module.finBasisOfFinrankEq ℤ L.carrier L.rank
  choose d hd using fun i : Fin n => L.unimodular.2 (b.coord i)
  let bound : Fin n → ℤ := fun i => (q : ℤ) * L.pairing (d i) (d i) + 1
  let BoxCoord : Fin n → Type := fun i =>
    {a : ℤ // a ∈ Set.Icc (-bound i) (bound i)}
  let (i : Fin n) : Fintype (BoxCoord i) :=
    (Set.finite_Icc (-bound i) (bound i)).fintype
  let encode : NormShell L q → (∀ i, BoxCoord i) := fun r i =>
    ⟨b.equivFun r.1 i, by
      have hcoord : b.equivFun r.1 i = L.pairing (d i) r.1 := by
        change b.coord i r.1 = L.pairing (d i) r.1
        exact (DFunLike.congr_fun (hd i) r.1).symm
      have hcs := L.pairing.apply_sq_le_of_symm
        (pairing_self_nonneg L)
        (LinearMap.BilinForm.isSymm_iff.mp L.symmetric) (d i) r.1
      rw [r.2] at hcs
      have hdnonneg := pairing_self_nonneg L (d i)
      have hqnonneg : (0 : ℤ) ≤ q := by exact_mod_cast (Nat.zero_le q)
      change -bound i ≤ b.equivFun r.1 i ∧
        b.equivFun r.1 i ≤ bound i
      dsimp only [bound]
      rw [hcoord]
      constructor <;> nlinarith⟩
  exact Finite.of_injective encode fun r s hrs => by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    exact congrArg Subtype.val (congrFun hrs i)

/--
@isnad1 id=finite.0h3v.s3.4702a86d5aa6 from=translated src=- shape=364cbd43 vocab=1e09ccbb
-/
noncomputable instance normShellFinite {n : ℕ}
    (L : PDUnimodularLattice n) (q : ℕ) : Finite (NormShell L q) :=
  normShell_finite L q

noncomputable instance normShellFintype {n : ℕ}
    (L : PDUnimodularLattice n) (q : ℕ) : Fintype (NormShell L q) :=
  Fintype.ofFinite _

def normShellTwoEquivNormTwoRoot {n : ℕ} (L : PDUnimodularLattice n) :
    NormShell L 2 ≃ NormTwoRoot L :=
  Equiv.refl _

end SRG266.Lattice
