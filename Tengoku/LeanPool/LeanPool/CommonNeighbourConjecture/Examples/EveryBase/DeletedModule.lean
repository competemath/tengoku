/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import Tengoku.LeanPool.LeanPool.CommonNeighbourConjecture.Examples.EveryBase.FrobeniusGroup
public import Tengoku

/-!
# The binary deleted permutation module

This file constructs the deleted permutation module for an odd finite
permutation set.  The explicit equivariant retraction is used in the
irreducibility proof: every endomorphism of the deleted module extends to the
full permutation module, while the all-ones operator restricts to zero.
-/

@[expose] public section

noncomputable section

namespace SaxlCounterexamples.EveryBase

open scoped BigOperators

/-- The binary field used throughout the deleted-module construction. -/
abbrev F2 := ZMod 2

/-- The binary permutation module on `Ω`. -/
abbrev PermMod (Ω : Type*) := Ω → F2

variable {H Ω : Type*} [Group H] [MulAction H Ω] [Fintype Ω]

instance permModDistribMulAction : DistribMulAction H (PermMod Ω) where
  smul g f x := f (g⁻¹ • x)
  one_smul f := by
    funext x
    change f ((1 : H)⁻¹ • x) = f x
    rw [inv_one, one_smul]
  mul_smul g h f := by
    funext x
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • g⁻¹ • x)
    rw [mul_inv_rev, mul_smul]
  smul_add _ _ _ := rfl
  smul_zero _ := rfl

/-- Sum all coordinates of a vector in the permutation module. -/
def coordSum : PermMod Ω →ₗ[F2] F2 where
  toFun f := ∑ x, f x
  map_add' f g := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a f := by
    change (∑ x, a * f x) = a * ∑ x, f x
    rw [Finset.mul_sum]

/--
@isnad1 id=eq.0h4v.s9.07ddfd82a7f8 from=translated src=- shape=39815c40 vocab=ee576d4b
-/
theorem coordSum_smul (g : H) (f : PermMod Ω) :
    coordSum (g • f) = coordSum f := by
  exact (MulAction.toPerm g).symm.sum_comp f

/-- The deleted binary permutation module, i.e. the coordinate-sum kernel. -/
def DeletedModule (Ω : Type*) [Fintype Ω] :=
  LinearMap.ker (coordSum (Ω := Ω))

instance deletedModuleDistribMulAction :
    DistribMulAction H (DeletedModule Ω) where
  smul g v := ⟨g • (v : PermMod Ω), by
    change coordSum (g • (v : PermMod Ω)) = 0
    rw [coordSum_smul]
    exact v.property⟩
  one_smul v := by
    apply Subtype.ext
    change (1 : H) • (v : PermMod Ω) = (v : PermMod Ω)
    exact one_smul H _
  mul_smul g h v := by
    apply Subtype.ext
    change (g * h) • (v : PermMod Ω) = g • h • (v : PermMod Ω)
    exact mul_smul g h _
  smul_add _ _ _ := by apply Subtype.ext; rfl
  smul_zero _ := by apply Subtype.ext; rfl

/--
@isnad1 id=smulcomm.0h2v.s12.e3ca49b06390 from=translated src=- shape=ccaffa9c vocab=f4d97748
-/
instance deletedModuleSMulCommClass :
    SMulCommClass H F2 (DeletedModule Ω) where
  smul_comm _ _ _ := by apply Subtype.ext; rfl

/-- The inclusion of the deleted module into the full permutation module. -/
def deletedIncl : DeletedModule Ω →ₗ[F2] PermMod Ω :=
  (DeletedModule Ω).subtype

/--
@isnad1 id=eq.1h1v.s8.3a1a6b54f3a0 from=translated src=- shape=ca3a24f9 vocab=7e60713a
-/
theorem coordSum_one (hΩodd : Odd (Fintype.card Ω)) :
    coordSum (1 : PermMod Ω) = 1 := by
  simp only [coordSum, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa using hΩodd.natCast_zmod_two

/-- Since `|Ω|` is odd, adding the coordinate sum times the all-ones vector
is an equivariant retraction onto the deleted module. -/
def deletedProj (hΩodd : Odd (Fintype.card Ω)) :
    PermMod Ω →ₗ[F2] DeletedModule Ω where
  toFun f := ⟨f + coordSum f • (fun _ ↦ (1 : F2)), by
    change coordSum (f + coordSum f • (1 : PermMod Ω)) = 0
    rw [map_add, map_smul, coordSum_one hΩodd]
    simpa [smul_eq_mul] using ZModModule.add_self (coordSum f)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, map_add, Pi.smul_apply,
      smul_eq_mul, mul_one]
    abel
  map_smul' a f := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, Pi.add_apply,
      map_smul, RingHom.id_apply, smul_eq_mul]
    ring

/--
@isnad1 id=eq.1h2v.s12.d8540c963f24 from=translated src=- shape=4c580f47 vocab=f5ab4784
-/
@[simp] theorem deletedProj_incl (hΩodd : Odd (Fintype.card Ω))
    (v : DeletedModule Ω) :
    deletedProj hΩodd (deletedIncl v) = v := by
  apply Subtype.ext
  funext x
  simp [deletedProj, deletedIncl, LinearMap.mem_ker.mp v.property]

/--
@isnad1 id=eq.1h4v.s13.033975e74864 from=translated src=- shape=b97e6a6b vocab=c93a8efb
-/
theorem deletedProj_smul (hΩodd : Odd (Fintype.card Ω))
    (g : H) (f : PermMod Ω) :
    deletedProj hΩodd (g • f) = g • deletedProj hΩodd f := by
  apply Subtype.ext
  change (g • f : PermMod Ω) + coordSum (g • f) • (1 : PermMod Ω) =
    g • (f + coordSum f • (1 : PermMod Ω))
  rw [coordSum_smul]
  rfl

/-- Extend a deleted-module endomorphism to the full permutation module by
the canonical inclusion/retraction pair. -/
def extendDeletedEnd (hΩodd : Odd (Fintype.card Ω))
    (T : DeletedModule Ω →ₗ[F2] DeletedModule Ω) :
    PermMod Ω →ₗ[F2] PermMod Ω :=
  deletedIncl.comp (T.comp (deletedProj hΩodd))

/--
@isnad1 id=eq.1h3v.s13.938c76e34bbf from=translated src=- shape=4eebb8aa vocab=e8661342
-/
@[simp] theorem extendDeletedEnd_incl (hΩodd : Odd (Fintype.card Ω))
    (T : DeletedModule Ω →ₗ[F2] DeletedModule Ω)
    (v : DeletedModule Ω) :
    extendDeletedEnd hΩodd T (deletedIncl v) = deletedIncl (T v) := by
  simp [extendDeletedEnd]

/--
@isnad1 id=eq.2h5v.s14.35b25e5752e9 from=translated src=- shape=20d2550a vocab=41b78565
-/
theorem extendDeletedEnd_smul (hΩodd : Odd (Fintype.card Ω))
    (T : DeletedModule Ω →ₗ[F2] DeletedModule Ω)
    (hT : ∀ (g : H) (v : DeletedModule Ω), T (g • v) = g • T v)
    (g : H) (f : PermMod Ω) :
    extendDeletedEnd hΩodd T (g • f) = g • extendDeletedEnd hΩodd T f := by
  simp only [extendDeletedEnd, LinearMap.comp_apply]
  rw [deletedProj_smul hΩodd, hT]
  rfl

/-- The deleted permutation module for the affine group over `Fq d`. -/
abbrev Vq (d : Nat) := DeletedModule (Fq d)

noncomputable instance fqDecidableEq (d : Nat) : DecidableEq (Fq d) :=
  Classical.typeDecidableEq _

noncomputable instance hqFintype (d : Nat) : Fintype (Hq d) :=
  Fintype.ofEquiv (Multiplicative (Fq d) × Cq d)
    { toFun := fun z ↦ ⟨z.1, z.2⟩
      invFun := fun z ↦ (z.left, z.right)
      left_inv := by rintro ⟨x, g⟩; rfl
      right_inv := by rintro ⟨x, g⟩; rfl }

/--
@isnad1 id=nontrivi.0h1v.s2.936258716445 from=translated src=- shape=76a08d12 vocab=84f59c19
-/
instance hqNontrivial (d : Nat) : Nontrivial (Hq d) := by
  refine ⟨⟨⟨Multiplicative.ofAdd 0, 1⟩,
    ⟨Multiplicative.ofAdd 1, 1⟩, ?_⟩⟩
  intro h
  have hleft := congrArg (fun g : Hq d ↦ g.left.toAdd) h
  exact zero_ne_one hleft

noncomputable instance vqFintype (d : Nat) : Fintype (Vq d) :=
  Fintype.ofFinite (Vq d)

/--
@isnad1 id=ne.1h1v.s9.a42c46e696d5 from=translated src=- shape=930949b2 vocab=24cef505
-/
theorem coordSum_ne_zero_q (d : Nat) (hd : Odd d) :
    coordSum (Ω := Fq d) ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (1 : PermMod (Fq d))
  rw [coordSum_one (by
    rw [Fintype.card_eq_nat_card]
    exact fq_odd_card d hd), LinearMap.zero_apply] at h1
  exact one_ne_zero h1

/-- The deleted module has the paper's dimension `3^d - 1`.
@isnad1 id=eq.1h1v.s9.427cc3156256 from=translated src=- shape=cbec717e vocab=360f27a8
-/
theorem vq_finrank (d : Nat) (hd : Odd d) :
    Module.finrank F2 (Vq d) = 3 ^ d - 1 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (coordSum_ne_zero_q d hd)
  rw [Module.finrank_pi F2, Fintype.card_eq_nat_card, fq_card d hd] at h
  exact Nat.eq_sub_of_add_eq h

/-- Consequently `Vq d` has exactly `2^(3^d-1)` elements.
@isnad1 id=eq.1h1v.s8.479f2999e53b from=translated src=- shape=fc2029c8 vocab=c64af970
-/
theorem vq_card (d : Nat) (hd : Odd d) :
    Nat.card (Vq d) = 2 ^ (3 ^ d - 1) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), vq_finrank d hd]
  norm_num

/-- The natural representation of `Hq d` on its deleted module. -/
def hqRepresentation (d : Nat) : Representation F2 (Hq d) (Vq d) :=
  Representation.ofDistribMulAction F2 (Hq d) (Vq d)

/-- The characteristic vector of `{0,1}`, written as a deleted vector. -/
noncomputable def pairVector (d : Nat) : Vq d :=
  ⟨Pi.basisFun F2 (Fq d) 0 + Pi.basisFun F2 (Fq d) 1, by
    change coordSum (Pi.basisFun F2 (Fq d) 0 +
      Pi.basisFun F2 (Fq d) 1) = 0
    rw [map_add]
    have hsum (a : Fq d) : coordSum (Pi.basisFun F2 (Fq d) a) = 1 := by
      rw [Pi.basisFun_apply]
      simp [coordSum, Pi.single_apply]
    rw [hsum, hsum]
    exact ZModModule.add_self 1⟩

/--
@isnad1 id=eq.0h2v.s9.369cb3b3c048 from=translated src=- shape=ef0f8dfc vocab=f9c0e35f
-/
@[simp] theorem pairVector_apply (d : Nat) (x : Fq d) :
    (pairVector d : PermMod (Fq d)) x =
      Pi.basisFun F2 (Fq d) 0 x + Pi.basisFun F2 (Fq d) 1 x := rfl

/--
@isnad1 id=eq.0h1v.s8.f66e8a43c453 from=translated src=- shape=19fb3858 vocab=d6c7a637
-/
theorem pairVector_coe_eq_twoPointVector (d : Nat) :
    (pairVector d : PermMod (Fq d)) = twoPointVector d := by
  exact (twoPointVector_eq_basisSum d).symm

/--
@isnad1 id=eq.0h1v.s8.fd014dc4613c from=translated src=- shape=631dd3df vocab=fae2f3e1
-/
theorem pairVector_zero (d : Nat) :
    (pairVector d : PermMod (Fq d)) 0 = 1 := by
  rw [pairVector_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  simp

/--
@isnad1 id=ne.0h1v.s9.8840c0c44d88 from=translated src=- shape=6899ba77 vocab=da2b5eb5
-/
theorem pairVector_ne_zero (d : Nat) : pairVector d ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Vq d ↦ (v : PermMod (Fq d)) 0) h
  rw [pairVector_zero] at h0
  exact one_ne_zero h0

/--
@isnad1 id=nontrivi.0h1v.s8.87951a7bc9b1 from=translated src=- shape=f43f238e vocab=bcd5ec24
-/
instance vqNontrivial (d : Nat) : Nontrivial (Vq d) :=
  ⟨⟨pairVector d, 0, pairVector_ne_zero d⟩⟩

/--
@isnad1 id=isregula.1h1v.s11.b04d3874ba41 from=translated src=- shape=8e23bd34 vocab=1275f250
-/
theorem pairVector_isRegular (d : Nat) (hd : Odd d) :
    Saxl.IsRegularVector (Hq d) (Vq d) (pairVector d) := by
  intro g hg
  have hfix : ∀ x : Fq d,
      twoPointVector d (g⁻¹ • x) = twoPointVector d x := by
    intro x
    have h := congrArg (fun v : Vq d ↦ (v : PermMod (Fq d)) x) hg
    change (pairVector d : PermMod (Fq d)) (g⁻¹ • x) =
      (pairVector d : PermMod (Fq d)) x at h
    simpa only [pairVector_coe_eq_twoPointVector] using h
  have hinv : g⁻¹ = 1 :=
    hq_eq_one_of_twoPointVector_comp_eq d hd g⁻¹ hfix
  exact inv_eq_one.mp hinv

/-- Paper Lemma 6.1: the two-point vector gives a regular `Hq d`-orbit.
@isnad1 id=ex.1h1v.s11.4f11826685d6 from=translated src=- shape=02ce4904 vocab=28823e70
-/
theorem hq_regularOrbit_exists (d : Nat) (hd : Odd d) :
    ∃ v : Vq d, Saxl.IsRegularVector (Hq d) (Vq d) v :=
  ⟨pairVector d, pairVector_isRegular d hd⟩

/-- Paper Lemma 6.1: the deleted-module action is faithful.
@isnad1 id=faithful.1h1v.s12.ebdf83b6e1db from=translated src=- shape=fad7645e vocab=38cac9d4
-/
theorem hq_faithful (d : Nat) (hd : Odd d) : FaithfulSMul (Hq d) (Vq d) := by
  rw [faithfulSMul_iff]
  intro g hfix
  exact pairVector_isRegular d hd g (hfix (pairVector d))

/-- The complement-of-zero vector used in the displayed obstruction. -/
noncomputable def hqBadSeedVector (d : Nat) (hd : Odd d) : Vq d :=
  ⟨(1 : PermMod (Fq d)) + Pi.basisFun F2 (Fq d) 0, by
    change coordSum ((1 : PermMod (Fq d)) +
      Pi.basisFun F2 (Fq d) 0) = 0
    rw [map_add, coordSum_one (by
      rw [Fintype.card_eq_nat_card]
      exact fq_odd_card d hd)]
    have hsum : coordSum (Pi.basisFun F2 (Fq d) 0) = 1 := by
      rw [Pi.basisFun_apply]
      simp [coordSum, Pi.single_apply]
    rw [hsum]
    exact ZModModule.add_self 1⟩

/--
@isnad1 id=eq.1h2v.s8.cf9e643c880c from=translated src=- shape=5bedf4fd vocab=67e9ca1b
-/
@[simp] theorem hqBadSeedVector_apply (d : Nat) (hd : Odd d) (x : Fq d) :
    (hqBadSeedVector d hd : PermMod (Fq d)) x =
      if x = 0 then 0 else 1 := by
  rw [hqBadSeedVector]
  simp only [Pi.add_apply, Pi.one_apply, Pi.basisFun_apply]
  by_cases hx : x = 0
  · subst x
    simp [ZModModule.add_self]
  · simp [hx]

/-- The displayed bad seed vector is not regular: every nonidentity square
multiplier fixes both `0` and its complement.
@isnad1 id=not.2h1v.s11.cefee33dc95d from=translated src=- shape=2080d50b vocab=eb94e2ed
-/
theorem hqBadSeedVector_not_regular
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) :
    ¬ Saxl.IsRegularVector (Hq d) (Vq d) (hqBadSeedVector d hd) := by
  have hcard : 1 < Nat.card (Cq d) := by
    rw [cq_card d hd]
    have hpow : 27 ≤ 3 ^ d := by
      calc
        27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ d := Nat.pow_le_pow_right (by omega) hd3
    omega
  let : Nontrivial (Cq d) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a, ha⟩ := exists_ne (1 : Cq d)
  let h : Hq d := ⟨Multiplicative.ofAdd 0, a⟩
  have hne : h ≠ 1 := by
    intro heq
    apply ha
    simpa [h] using congrArg SemidirectProduct.right heq
  intro hregular
  apply hne
  apply hregular h
  apply Subtype.ext
  funext x
  change (hqBadSeedVector d hd : PermMod (Fq d)) (h⁻¹ • x) =
    (hqBadSeedVector d hd : PermMod (Fq d)) x
  rw [hqBadSeedVector_apply, hqBadSeedVector_apply]
  congr 1
  apply propext
  have hzero : h⁻¹ • (0 : Fq d) = 0 := by
    simp [h]
  constructor
  · intro hx
    exact (MulAction.toPerm h⁻¹).injective (hx.trans hzero.symm)
  · rintro rfl
    exact hzero

/-- The coordinate map from the deleted module to binary-valued functions. -/
def deletedCoord (d : Nat) : Vq d →+ (Fq d → F2) :=
  (Vq d).subtype.toAddHom

end SaxlCounterexamples.EveryBase
