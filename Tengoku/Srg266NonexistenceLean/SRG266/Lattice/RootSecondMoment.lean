/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootBasis
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootFinite
import Tengoku.Seed.Algebra.Module.Torsion.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

def RootSecondMomentIdentity {n : ℕ} (L : PDUnimodularLattice n)
    (c : ℤ) : Prop :=
  ∀ x y : L.carrier,
    (∑ r : NormTwoRoot L, L.pairing r.1 x * L.pairing r.1 y) =
      c * L.pairing x y

theorem rootSecondMoment_reconstruction {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ}
    (h : RootSecondMomentIdentity L c) (x : L.carrier) :
    ∑ r : NormTwoRoot L, (L.pairing r.1 x) • r.1 = c • x := by
  apply L.unimodular.1
  ext y
  simpa only [map_sum, LinearMap.sum_apply, map_zsmul,
    LinearMap.smul_apply, smul_eq_mul]
    using h x y

theorem smul_mem_normTwoRootSpan_of_secondMoment {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ}
    (h : RootSecondMomentIdentity L c) (x : L.carrier) :
    c • x ∈ normTwoRootSpan L := by
  rw [← rootSecondMoment_reconstruction L h x]
  exact Submodule.sum_mem _ fun r _ =>
    (normTwoRootSpan L).toAddSubgroup.zsmul_mem
      (Submodule.subset_span (Set.mem_range_self r)) _

noncomputable def secondMomentSpanAddHom {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ}
    (h : RootSecondMomentIdentity L c) :
    L.carrier →+ normTwoRootSpan L where
  toFun x := ⟨c • x, smul_mem_normTwoRootSpan_of_secondMoment L h x⟩
  map_zero' := by
    apply Subtype.ext
    change c • (0 : L.carrier) = 0
    exact zsmul_zero c
  map_add' x y := by
    apply Subtype.ext
    change c • (x + y) = c • x + c • y
    exact zsmul_add x y c

theorem normTwoRoots_fullRank_of_secondMoment {n : ℕ}
    (L : PDUnimodularLattice n) {c : ℤ} (hc : c ≠ 0)
    (h : RootSecondMomentIdentity L c) :
    Set.finrank ℤ (Set.range (@normTwoRootVal n L)) = n := by
  let := L.moduleFree
  let := L.moduleFinite
  let S := normTwoRootSpan L
  let : Module ℤ S := S.module
  let : Module.Finite ℤ S := by
    dsimp only [S]
    exact Module.Finite.span_of_finite ℤ
      (Set.finite_range (@normTwoRootVal n L))
  let f : L.carrier →ₗ[ℤ] S :=
    toZLinearMap (secondMomentSpanAddHom L h)
  let : IsAddTorsionFree L.carrier :=
    IsAddTorsionFree.of_isTorsionFree ℤ L.carrier
  have hinj : Function.Injective f := by
    intro x y hxy
    apply zsmul_right_injective hc
    exact congrArg Subtype.val hxy
  have hlower : Module.finrank ℤ L.carrier ≤
      Module.finrank ℤ S :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hupper : Module.finrank ℤ S ≤
      Module.finrank ℤ L.carrier :=
    Submodule.finrank_le S
  unfold Set.finrank
  change Module.finrank ℤ S = n
  have hrank := L.rank
  omega

end Lattice
end SRG266
