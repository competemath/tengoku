import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

universe u

namespace Tengoku.FltAnthropic.MvFormalGroup

namespace WittLaw

open MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

def weight {idx : Type*} (c : idx → ℕ) : idx × ℕ → ℕ := fun im => c im.1 * p ^ im.2

omit hp in
/--
@isnad1 id=eq.0h5v.s5.ddf2a64a1399 from=translated src=- shape=ec5273ed vocab=c04da52d
-/
@[simp] theorem weight_apply {idx : Type*} (c : idx → ℕ) (i : idx) (m : ℕ) :
    weight p c (i, m) = c i * p ^ m := rfl

omit hp in

/--
@isnad1 id=isweight.0h5v.s8.2aac9d79ddb1 from=translated src=- shape=3493bebb vocab=c40acef6
-/
theorem isWeightedHomogeneous_rename_wittPolynomial {idx : Type*} (c : idx → ℕ) (i : idx)
    (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (rename (Prod.mk i) (wittPolynomial p ℤ n))
      (c i * p ^ n) := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun j hj => ?_
  rw [map_mul, rename_C, map_pow, map_pow, rename_X]
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hX := (isWeightedHomogeneous_X (R := ℤ) (weight p c) (i, j)).pow (p ^ (n - j))
  have hdeg : (p ^ (n - j)) • weight p c (i, j) = c i * p ^ n := by
    rw [weight_apply, smul_eq_mul, ← mul_assoc, mul_comm (p ^ (n - j)), mul_assoc,
      ← pow_add, Nat.sub_add_cancel hj']
  rw [hdeg] at hX
  have := hX.C_mul ((p : ℤ) ^ j)
  rwa [map_pow] at this

/--
@isnad1 id=isweight.1h6v.s9.becce1b0e289 from=translated src=- shape=63789c8c vocab=09a85df8
-/
theorem isWeightedHomogeneous_wittStructureInt {idx : Type*} (c : idx → ℕ)
    (Φ : MvPolynomial idx ℤ) (k : ℕ)
    (hΦ : ∀ n, IsWeightedHomogeneous (weight p c)
      (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ) (k * p ^ n)) (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (wittStructureInt p Φ n) (k * p ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key := wittStructureInt_prop p Φ n
    rw [← aeval_eq_bind₁, aeval_wittPolynomial, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      pow_one] at key

    have hsum : IsWeightedHomogeneous (weight p c)
        (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)) (k * p ^ n) := by
      refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have h1 := (ih i hi').pow (p ^ (n - i))
      have hdeg : (p ^ (n - i)) • (k * p ^ i) = k * p ^ n := by
        rw [smul_eq_mul, mul_left_comm, ← pow_add, Nat.sub_add_cancel hi'.le]
      rw [hdeg] at h1
      have h2 := h1.C_mul ((p : ℤ) ^ i)
      rwa [map_pow, map_natCast] at h2
    intro d hd
    by_contra hne
    have hcoeff : coeff d ((p : MvPolynomial (idx × ℕ) ℤ) ^ n * wittStructureInt p Φ n) = 0 := by
      have := congrArg (coeff d) key
      rw [coeff_add] at this
      have hR : coeff d (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ) = 0 :=
        (hΦ n).coeff_eq_zero d hne
      have hS : coeff d (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)) = 0 := hsum.coeff_eq_zero d hne
      rw [hR, hS, zero_add] at this
      exact this
    have hC : (p : MvPolynomial (idx × ℕ) ℤ) ^ n = C ((p : ℤ) ^ n) := by
      rw [map_pow, map_natCast]
    rw [hC, coeff_C_mul] at hcoeff
    rcases mul_eq_zero.mp hcoeff with h | h
    · exact absurd h (pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.out.ne_zero))
    · exact hd h

/--
@isnad1 id=isweight.0h2v.s5.f2572d10baa6 from=translated src=- shape=f70aaa77 vocab=977228be
-/
theorem isWeightedHomogeneous_wittAdd (n : ℕ) :
    IsWeightedHomogeneous (weight p fun _ : Fin 2 => 1) (WittVector.wittAdd p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p (fun _ : Fin 2 => 1) (X 0 + X 1) 1
    (fun m => by
      rw [map_add, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 1 m
      rw [one_mul] at h0 h1
      exact h0.add h1) n
  rwa [one_mul] at h

/--
@isnad1 id=isweight.0h2v.s6.14b9b75e9743 from=translated src=- shape=2d296c49 vocab=8896b2f1
-/
theorem isWeightedHomogeneous_wittMul (n : ℕ) :
    IsWeightedHomogeneous (weight p ![0, 1]) (WittVector.wittMul p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p ![0, 1] (X 0 * X 1) 1
    (fun m => by
      rw [map_mul, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 1 m
      simp only [Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one, one_mul] at h0 h1
      have := h0.mul h1
      rwa [zero_add] at this) n
  rwa [one_mul] at h

variable (R : Type u) [CommRing R]

def addFam (n : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  ↑(MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n))

/--
@isnad1 id=eq.0h3v.s7.31d6481b3a2e from=translated src=- shape=46ce887b vocab=033f5e1f
-/
theorem constantCoeff_addFam (n : ℕ) : MvPowerSeries.constantCoeff (addFam p R n) = 0 := by
  rw [addFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    coeff_map, ← constantCoeff_eq, WittVector.constantCoeff_wittAdd, map_zero]

/--
@isnad1 id=eq.1h4v.s8.2e357701d28f from=translated src=- shape=482b1758 vocab=72a14929
-/
theorem weight_eq_of_coeff_addFam_ne_zero {n : ℕ} {d : Fin 2 × ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff d (addFam p R n) ≠ 0) :
    Finsupp.weight (weight p fun _ : Fin 2 => 1) d = p ^ n := by
  rw [addFam, MvPolynomial.coeff_coe, coeff_map] at h
  have h' : coeff d (WittVector.wittAdd p n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_wittAdd p n h'

/--
@isnad1 id=hassubst.0h2v.s4.db1c4f08f622 from=translated src=- shape=4016c2e9 vocab=1a828138
-/
theorem hasSubst_addFam : MvPowerSeries.HasSubst (addFam p R) := by
  refine ⟨fun n => by rw [constantCoeff_addFam]; exact IsNilpotent.zero, fun d => ?_⟩
  · refine (Set.finite_lt_nat (Finsupp.weight (weight p fun _ : Fin 2 => 1) d)).subset ?_
    intro n hn
    have hw := weight_eq_of_coeff_addFam_ne_zero p R hn
    show n < Finsupp.weight (weight p fun _ : Fin 2 => 1) d
    rw [hw]
    exact Nat.lt_pow_self hp.out.one_lt

/--
@isnad1 id=tendstoc.0h1v.s4.cb2769bc6a85 from=translated src=- shape=8879a807 vocab=68322568
-/
instance instTendstoCofiniteProdMk (i : Fin 2) :
    Filter.TendstoCofinite (Prod.mk i : ℕ → Fin 2 × ℕ) :=
  Filter.tendstoCofinite_of_injective (Prod.mk_right_injective i)

variable {R}

def blk (i : Fin 2) : ℕ → MvPowerSeries (Fin 2 × ℕ) R := fun m => MvPowerSeries.X (i, m)

omit hp in
/--
@isnad1 id=eq.0h3v.s5.a1b8b268c795 from=translated src=- shape=1440dcc8 vocab=a979c020
-/
@[simp] theorem blk_apply (i : Fin 2) (m : ℕ) : blk (R := R) i m = MvPowerSeries.X (i, m) := rfl

omit hp in
/--
@isnad1 id=eq.0h3v.s7.1ef4368538aa from=translated src=- shape=4570a66b vocab=972e7cde
-/
theorem constantCoeff_blk (i : Fin 2) (m : ℕ) :
    MvPowerSeries.constantCoeff (blk (R := R) i m) = 0 :=
  MvPowerSeries.constantCoeff_X _

omit hp in
/--
@isnad1 id=hassubst.0h2v.s4.26da44831e23 from=translated src=- shape=469b8d2b vocab=da862ea0
-/
theorem hasSubst_blk (i : Fin 2) : MvPowerSeries.HasSubst (blk (R := R) i) :=
  MvPowerSeries.HasSubst.X_comp (Prod.mk i)

omit hp in

/--
@isnad1 id=eq.0h3v.s8.d6c0c84f2afa from=translated src=- shape=b4f0d576 vocab=7d304d04
-/
theorem subst_blk_eq_rename (i : Fin 2) (f : MvPowerSeries ℕ R) :
    MvPowerSeries.subst (blk i) f = MvPowerSeries.rename (Prod.mk i) f :=
  (MvPowerSeries.rename_eq_subst (Prod.mk i) f).symm

end WittLaw

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]

structure CartierModule (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]
    (Φ : MvFormalGroup d R) where

  toPowerSeries : Fin d → MvPowerSeries ℕ R

  constantCoeff_eq_zero : ∀ j, (toPowerSeries j).constantCoeff = 0

  subst_eq : ∀ j,
    subst (WittLaw.addFam p R) (toPowerSeries j) =
      subst
        (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
        (Φ.toPowerSeries j)

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

/--
@isnad1 id=eq.1h6v.s6.5f17bdadfbdd from=translated src=- shape=3da314bc vocab=ce6e24f8
-/
@[ext] theorem ext {f g : CartierModule p Φ} (h : f.toPowerSeries = g.toPowerSeries) : f = g := by
  cases f; cases g; cases h; rfl

/--
@isnad1 id=hassubst.0h5v.s5.ed10d1f569c0 from=translated src=- shape=e07a53b8 vocab=f3e25c6f
-/
theorem hasSubst_toPowerSeries (f : CartierModule p Φ) : HasSubst f.toPowerSeries :=
  hasSubst_of_constantCoeff_zero f.constantCoeff_eq_zero

def inBlk (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) : Fin d → MvPowerSeries (Fin 2 × ℕ) R :=
  fun l => subst (blk i) (a l)

omit hp in
/--
@isnad1 id=eq.0h5v.s6.9c1925571b39 from=translated src=- shape=98bdf21c vocab=7e612a66
-/
@[simp] theorem inBlk_apply (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) (l : Fin d) :
    inBlk i a l = subst (blk i) (a l) := rfl

omit hp in
/--
@isnad1 id=eq.1h5v.s8.ddfc14667f23 from=translated src=- shape=492a1ff5 vocab=8e4dc1eb
-/
theorem constantCoeff_inBlk (i : Fin 2) {a : Fin d → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (l : Fin d) : (inBlk i a l).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk i) (constantCoeff_blk i) (ha l)

omit hp in
/--
@isnad1 id=eq.0h3v.s6.1594d7921628 from=translated src=- shape=b2e7e540 vocab=a441bd93
-/
theorem inBlk_zero (i : Fin 2) : inBlk i (fun _ : Fin d => (0 : MvPowerSeries ℕ R)) = fun _ => 0 := by
  funext l
  show subst (blk i) (0 : MvPowerSeries ℕ R) = 0
  rw [← coe_substAlgHom (hasSubst_blk i), map_zero]

omit hp in

/--
@isnad1 id=eq.2h6v.s8.8582d905c2c6 from=translated src=- shape=779db9ca vocab=de5f4f74
-/
theorem inBlk_subst_elim (G : MvFormalGroup d' R) (i : Fin 2) {a b : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (hb : ∀ l, (b l).constantCoeff = 0) :
    inBlk i (fun l => subst (Sum.elim a b) (G.toPowerSeries l)) =
      fun l => subst (Sum.elim (inBlk i a) (inBlk i b)) (G.toPowerSeries l) := by
  funext l
  exact subst_subst_elim G ha hb (hasSubst_blk i) l

omit hp in

/--
@isnad1 id=eq.1h5v.s7.73be13a1b907 from=translated src=- shape=2bcbba20 vocab=3766d641
-/
theorem inBlk_negSeries (G : MvFormalGroup d' R) (i : Fin 2) {a : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) :
    inBlk i (negSeries G a) = negSeries G (inBlk i a) := by
  have hneg : ∀ j, (negSeries G a j).constantCoeff = 0 := constantCoeff_negSeries G a
  refine negSeries_unique G (constantCoeff_inBlk i ha) (constantCoeff_inBlk i hneg) fun l => ?_
  have h := congrFun (inBlk_subst_elim G i ha hneg) l
  rw [← h]
  show subst (blk i) (subst (Sum.elim a (negSeries G a)) (G.toPowerSeries l)) = 0
  rw [subst_elim_negSeries G ha l, ← coe_substAlgHom (hasSubst_blk i), map_zero]

/--
@isnad1 id=eq.0h6v.s7.e4e74b41f1a6 from=translated src=- shape=723b3f90 vocab=bc2cf039
-/
theorem subst_addFam (f : CartierModule p Φ) (j : Fin d) :
    subst (WittLaw.addFam p R) (f.toPowerSeries j) =
      subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries)) (Φ.toPowerSeries j) :=
  f.subst_eq j

protected def zero (Φ : MvFormalGroup d R) : CartierModule p Φ where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro j
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    have h0 : (fun l : Fin d => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 0
    have h1 : (fun l : Fin d => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 1
    rw [h0, h1]
    exact (subst_elim_zero_right Φ (fun _ => map_zero _) j).symm

instance instZero : Zero (CartierModule p Φ) := ⟨CartierModule.zero Φ⟩

/--
@isnad1 id=eq.0h4v.s6.b5cad8f22c2d from=translated src=- shape=46a02b9a vocab=ce6e24f8
-/
@[simp] theorem toPowerSeries_zero : (0 : CartierModule p Φ).toPowerSeries = fun _ => 0 := rfl

protected def add [Φ.IsComm] (f g : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero j
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hg := g.constantCoeff_eq_zero
    show subst (WittLaw.addFam p R)
        (subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)) =
      subst (Sum.elim
        (inBlk 0 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l))
        (inBlk 1 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l)))
        (Φ.toPowerSeries j)
    rw [subst_subst_elim Φ hf hg (hasSubst_addFam p R) j, inBlk_subst_elim Φ 0 hf hg,
      inBlk_subst_elim Φ 1 hf hg]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    have hgeq : (fun l => subst (WittLaw.addFam p R) (g.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 g.toPowerSeries) (inBlk 1 g.toPowerSeries))
          (Φ.toPowerSeries l) := funext g.subst_addFam
    rw [hfeq, hgeq]
    exact subst_elim_exchange Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf)
      (constantCoeff_inBlk 0 hg) (constantCoeff_inBlk 1 hg) j

instance instAdd [Φ.IsComm] : Add (CartierModule p Φ) := ⟨CartierModule.add⟩

/--
@isnad1 id=eq.0h6v.s7.3b5d783a5d2a from=translated src=- shape=3a53b5ef vocab=4a9d8c73
-/
@[simp] theorem toPowerSeries_add [Φ.IsComm] (f g : CartierModule p Φ) :
    (f + g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j) := rfl

protected def neg [Φ.IsComm] (f : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := negSeries Φ f.toPowerSeries
  constantCoeff_eq_zero := constantCoeff_negSeries Φ f.toPowerSeries
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hneg : ∀ j, (negSeries Φ f.toPowerSeries j).constantCoeff = 0 :=
      constantCoeff_negSeries Φ _
    show subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries j) =
      subst (Sum.elim (inBlk 0 (negSeries Φ f.toPowerSeries)) (inBlk 1 (negSeries Φ f.toPowerSeries)))
        (Φ.toPowerSeries j)

    have hS : (fun l => subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries l)) =
        negSeries Φ fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l) := by
      have hA := hasSubst_addFam p R
      have hA0 := constantCoeff_addFam p R
      refine negSeries_unique Φ (fun l => constantCoeff_subst_eq_zero hA hA0 (hf l))
        (fun l => constantCoeff_subst_eq_zero hA hA0 (hneg l)) fun i => ?_
      rw [← subst_subst_elim Φ hf hneg hA i, subst_elim_negSeries Φ hf i, ← coe_substAlgHom hA,
        map_zero]
    have h1 := congrFun hS j
    rw [h1]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfeq, negSeries_elim_add Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf),
      ← inBlk_negSeries Φ 0 hf, ← inBlk_negSeries Φ 1 hf]

instance instNeg [Φ.IsComm] : Neg (CartierModule p Φ) := ⟨CartierModule.neg⟩

/--
@isnad1 id=eq.0h5v.s6.01ef16ffbc94 from=translated src=- shape=8f4f4765 vocab=6108f7db
-/
@[simp] theorem toPowerSeries_neg [Φ.IsComm] (f : CartierModule p Φ) :
    (-f).toPowerSeries = negSeries Φ f.toPowerSeries := rfl

instance instAddCommGroup [Φ.IsComm] : AddCommGroup (CartierModule p Φ) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := CartierModule.ext (funext fun j =>
    subst_elim_assoc Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero c.constantCoeff_eq_zero j)
  zero_add a := CartierModule.ext (funext fun j =>
    subst_elim_zero_left Φ a.constantCoeff_eq_zero j)
  add_zero a := CartierModule.ext (funext fun j =>
    subst_elim_zero_right Φ a.constantCoeff_eq_zero j)
  add_comm a b := CartierModule.ext (funext fun j =>
    subst_elim_comm Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero j)
  neg_add_cancel a := CartierModule.ext (funext fun j =>
    subst_elim_negSeries_left Φ a.constantCoeff_eq_zero j)

/--
@isnad1 id=eq.0h6v.s7.56aeb5c4b5a3 from=translated src=- shape=bdf26a24 vocab=c026c801
-/
@[simp] theorem toPowerSeries_sub [Φ.IsComm] (f g : CartierModule p Φ) :
    (f - g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries (negSeries Φ g.toPowerSeries)) (Φ.toPowerSeries j) := by
  rw [sub_eq_add_neg]; rfl

end CartierModule

namespace WittLaw

variable (p)

def pairFam (u : ℕ → MvPowerSeries ℕ R) : Fin 2 × ℕ → MvPowerSeries (Fin 2 × ℕ) R :=
  fun im => subst (blk im.1) (u im.2)

structure IsEndo (u : ℕ → MvPowerSeries ℕ R) : Prop where
  hasSubst : HasSubst u
  constantCoeff : ∀ n, (u n).constantCoeff = 0
  subst_addFam : ∀ n, subst (addFam p R) (u n) = subst (pairFam u) (addFam p R n)

variable {p}

omit hp in
/--
@isnad1 id=eq.0h4v.s6.b34f1e1ff483 from=translated src=- shape=0b018b35 vocab=745c31c4
-/
@[simp] theorem pairFam_apply (u : ℕ → MvPowerSeries ℕ R) (i : Fin 2) (m : ℕ) :
    pairFam u (i, m) = subst (blk i) (u m) := rfl

omit hp in
/--
@isnad1 id=eq.1h3v.s8.5d65df2847b2 from=translated src=- shape=a6f38d3b vocab=25f9ba94
-/
theorem constantCoeff_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : ∀ n, (u n).constantCoeff = 0)
    (im : Fin 2 × ℕ) : (pairFam u im).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk im.1) (constantCoeff_blk im.1) (hu im.2)

omit hp in

/--
@isnad1 id=ex.1h4v.s9.9227e7ac45f5 from=translated src=- shape=ab6bdeb7 vocab=c2d88b4a
-/
theorem exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero (i : Fin 2) (f : MvPowerSeries ℕ R)
    {e : Fin 2 × ℕ →₀ ℕ} (h : coeff e (subst (blk (R := R) i) f) ≠ 0) :
    ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e ∧ coeff x f ≠ 0 := by
  rw [subst_blk_eq_rename, coeff_rename] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨x, ?_, hne⟩
  simpa using hx

omit hp in

/--
@isnad1 id=hassubst.2h2v.s7.18a12059577a from=translated src=- shape=c2bf5a17 vocab=e378d257
-/
theorem hasSubst_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) : HasSubst (pairFam u) := by
  refine ⟨fun im => by rw [constantCoeff_pairFam hu0]; exact IsNilpotent.zero, fun e => ?_⟩
  have hfin : ∀ i : Fin 2, {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0}.Finite := by
    intro i
    by_cases hx : ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e
    · obtain ⟨x, rfl⟩ := hx
      refine (hu.coeff_zero x).subset fun m hm => ?_
      obtain ⟨y, hy, hne⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      have hyx : y = x := Finsupp.mapDomain_injective (Prod.mk_right_injective i) hy
      rw [hyx] at hne
      exact hne
    · convert Set.finite_empty
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      by_contra hm
      obtain ⟨y, hy, -⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      exact hx ⟨y, hy⟩
  have hsub : {im : Fin 2 × ℕ | coeff e (pairFam u im) ≠ 0} ⊆
      ⋃ i : Fin 2, Prod.mk i '' {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0} := by
    rintro ⟨i, m⟩ him
    exact Set.mem_iUnion.mpr ⟨i, m, him, rfl⟩
  exact (Set.finite_iUnion fun i => (hfin i).image _).subset hsub

omit hp in

/--
@isnad1 id=eq.2h4v.s7.e2b51300fde4 from=translated src=- shape=f04e5104 vocab=61bbe2be
-/
theorem subst_pairFam_subst_blk {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) (i : Fin 2) (f : MvPowerSeries ℕ R) :
    subst (pairFam u) (subst (blk (R := R) i) f) = subst (blk (R := R) i) (subst u f) := by
  rw [subst_comp_subst_apply (hasSubst_blk i) (hasSubst_pairFam hu hu0),
    subst_comp_subst_apply hu (hasSubst_blk i)]
  congr 1
  funext m
  show subst (pairFam u) (X (i, m)) = subst (blk i) (u m)
  rw [subst_X (hasSubst_pairFam hu hu0)]
  rfl

variable (R)

def verFam : ℕ → MvPowerSeries ℕ R
  | 0 => 0
  | n + 1 => X n

variable {R}

omit hp in
/--
@isnad1 id=eq.0h1v.s5.8e15eb6036ce from=translated src=- shape=9db32426 vocab=d49925b0
-/
@[simp] theorem verFam_zero : verFam R 0 = 0 := rfl

omit hp in
/--
@isnad1 id=eq.0h2v.s5.534a40d70012 from=translated src=- shape=9677bdfb vocab=c2094061
-/
@[simp] theorem verFam_succ (n : ℕ) : verFam R (n + 1) = X n := rfl

omit hp in
/--
@isnad1 id=eq.0h2v.s6.02a663692fa5 from=translated src=- shape=56a78aba vocab=768767f5
-/
theorem constantCoeff_verFam (n : ℕ) : (verFam R n).constantCoeff = 0 := by
  cases n with
  | zero => exact map_zero _
  | succ n => exact constantCoeff_X _

omit hp in
/--
@isnad1 id=hassubst.0h1v.s3.1f2a7266bbaa from=translated src=- shape=5f0010f5 vocab=816de513
-/
theorem hasSubst_verFam : HasSubst (verFam R) := by
  classical
  refine ⟨fun n => by rw [constantCoeff_verFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (e.support.image Nat.succ).finite_toSet.subset fun n hn => ?_
  cases n with
  | zero => exact absurd (by simp) hn
  | succ n =>
    have h : coeff e (X n : MvPowerSeries ℕ R) ≠ 0 := hn
    rw [coeff_X] at h
    split_ifs at h with he
    · subst he
      simp
    · exact absurd rfl h

/--
@isnad1 id=eq.0h2v.s9.ec862ab17576 from=translated src=- shape=c313062a vocab=79727049
-/
theorem aeval_verschiebung_wittAdd (n : ℕ) :
    MvPolynomial.aeval (fun im : Fin 2 × ℕ =>
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ))
      (WittVector.wittAdd p n) =
      Nat.casesOn n 0 fun m => WittVector.wittAdd p m := by

  let A := MvPolynomial (Fin 2 × ℕ) ℤ
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (0, m)
  let y : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (1, m)
  have key := congrArg (fun z : WittVector p A => z.coeff n)
    (WittVector.verschiebung.map_add x y).symm
  have hval : (fun im : Fin 2 × ℕ =>
      (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : A)) =
      Function.uncurry ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] := by
    funext ⟨i, m⟩
    fin_cases i <;> cases m <;> rfl
  rw [hval]
  change WittVector.peval (WittVector.wittAdd p n)
      ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] = _
  rw [← WittVector.add_coeff, key]
  cases n with
  | zero => exact WittVector.verschiebung_coeff_zero _
  | succ m =>
    rw [WittVector.verschiebung_coeff_succ, WittVector.add_coeff]
    show MvPolynomial.aeval (Function.uncurry ![x.coeff, y.coeff]) (WittVector.wittAdd p m) = _
    have hid : Function.uncurry ![x.coeff, y.coeff] = (MvPolynomial.X : Fin 2 × ℕ → A) := by
      funext ⟨i, k⟩
      fin_cases i <;> rfl
    rw [hid, MvPolynomial.aeval_X_left_apply]

/--
@isnad1 id=eq.0h5v.s9.fa6eb29cc45c from=translated src=- shape=5fd07c88 vocab=4327efe3
-/
theorem subst_coe_addFam {τ : Type*} (g : Fin 2 × ℕ → MvPolynomial τ ℤ) (n : ℕ) :
    subst (fun im => ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) :
      MvPowerSeries τ R)) (addFam p R n) =
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.aeval g (WittVector.wittAdd p n)) :
        MvPolynomial τ R) : MvPowerSeries τ R) := by
  rw [addFam, subst_coe]
  set G : Fin 2 × ℕ → MvPowerSeries τ R := fun im =>
    ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) : MvPowerSeries τ R)
  let ψ₁ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.aeval G).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (MvPolynomial.aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · have h1 := RingHom.ext_int (ψ₁.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
        (ψ₂.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
      exact RingHom.congr_fun h1 r
    · simp [ψ₁, ψ₂, G]
  exact RingHom.congr_fun hψ (WittVector.wittAdd p n)

/--
@isnad1 id=isendo.0h2v.s4.2b516b1ec860 from=translated src=- shape=cbbf2760 vocab=ca0ef8ff
-/
theorem isEndo_verFam : IsEndo p (verFam R) := by
  refine ⟨hasSubst_verFam, constantCoeff_verFam, fun n => ?_⟩
  have hpair : pairFam (verFam R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R)
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ) :
          MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    cases m with
    | zero =>
      show subst (blk i) (0 : MvPowerSeries ℕ R) = _
      rw [← coe_substAlgHom (hasSubst_blk i), map_zero]
      simp
    | succ m =>
      show subst (blk i) (X m : MvPowerSeries ℕ R) = _
      rw [subst_X (hasSubst_blk i)]
      simp [blk]
  rw [hpair, subst_coe_addFam (fun im : Fin 2 × ℕ =>
    (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ)) n,
    aeval_verschiebung_wittAdd]
  cases n with
  | zero =>
    show subst (addFam p R) (0 : MvPowerSeries ℕ R) = _
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    simp
  | succ m =>
    show subst (addFam p R) (X m : MvPowerSeries ℕ R) = _
    rw [subst_X (hasSubst_addFam p R)]
    rfl

variable (p R)

def frobFam : ℕ → MvPowerSeries ℕ R := fun n => X n ^ p

variable {p R}

omit hp in
/--
@isnad1 id=eq.0h3v.s5.949cd1101e0b from=translated src=- shape=d936969c vocab=99c68cab
-/
@[simp] theorem frobFam_apply (n : ℕ) : frobFam p R n = X n ^ p := rfl

/--
@isnad1 id=eq.0h3v.s6.19a02ec14ce7 from=translated src=- shape=1ed1471a vocab=3f4d0b60
-/
theorem constantCoeff_frobFam (n : ℕ) : (frobFam p R n).constantCoeff = 0 := by
  rw [frobFam_apply, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]

/--
@isnad1 id=hassubst.0h2v.s4.aec8f167c179 from=translated src=- shape=b3341b83 vocab=b60c0984
-/
theorem hasSubst_frobFam : HasSubst (frobFam p R) := HasSubst.X_pow hp.out.ne_zero

/--
@isnad1 id=eq.0h3v.s10.fcefdf909991 from=translated src=- shape=ca397f62 vocab=9c2c2a00
-/
theorem expand_map_wittAdd [CharP R p] (n : ℕ) :
    MvPolynomial.expand p (MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n)) =
      MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n) ^ p := by
  haveI : ExpChar R p := ExpChar.prime hp.out
  rw [← MvPolynomial.map_frobenius_expand p, MvPolynomial.map_expand, MvPolynomial.map_map,
    show (frobenius R p).comp (Int.castRingHom R) = Int.castRingHom R from RingHom.ext_int _ _]

/--
@isnad1 id=isendo.0h2v.s4.3a3189bf99e2 from=translated src=- shape=13b0060a vocab=021c62b2
-/
theorem isEndo_frobFam [CharP R p] : IsEndo p (frobFam p R) := by
  refine ⟨hasSubst_frobFam, constantCoeff_frobFam, fun n => ?_⟩
  have hpair : pairFam (frobFam p R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    show subst (blk i) (X m ^ p : MvPowerSeries ℕ R) = _
    rw [subst_pow (hasSubst_blk i), subst_X (hasSubst_blk i), map_pow, MvPolynomial.map_X,
      MvPolynomial.coe_pow, MvPolynomial.coe_X]
    rfl
  rw [hpair, frobFam_apply, subst_pow (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    subst_coe_addFam (fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ)) n]
  have hexp : MvPolynomial.aeval (fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p :
      MvPolynomial (Fin 2 × ℕ) ℤ)) (WittVector.wittAdd p n) =
      MvPolynomial.expand p (WittVector.wittAdd p n) := by
    rw [MvPolynomial.expand, ← MvPolynomial.aeval_eq_bind₁]
  rw [hexp, MvPolynomial.map_expand, expand_map_wittAdd, MvPolynomial.coe_pow]
  rfl

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

def precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    CartierModule p Φ where
  toPowerSeries := fun j => subst u (f.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero hu.hasSubst hu.constantCoeff (f.constantCoeff_eq_zero j)
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hA := hasSubst_addFam p R
    have hP := hasSubst_pairFam hu.hasSubst hu.constantCoeff
    show subst (WittLaw.addFam p R) (subst u (f.toPowerSeries j)) =
      subst (Sum.elim (inBlk 0 fun l => subst u (f.toPowerSeries l))
        (inBlk 1 fun l => subst u (f.toPowerSeries l))) (Φ.toPowerSeries j)
    rw [subst_comp_subst_apply hu.hasSubst hA]
    have hfam : (fun n => subst (WittLaw.addFam p R) (u n)) =
        fun n => subst (WittLaw.pairFam u) (WittLaw.addFam p R n) := funext hu.subst_addFam
    rw [hfam, ← subst_comp_subst_apply hA hP, f.subst_addFam, subst_subst_elim Φ
      (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hP]
    congr 1
    funext s
    rcases s with l | l
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 0 (f.toPowerSeries l)
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 1 (f.toPowerSeries l)

/--
@isnad1 id=eq.1h6v.s6.b39e31cae6a4 from=translated src=- shape=7ba80f46 vocab=9def2c35
-/
@[simp] theorem toPowerSeries_precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (f : CartierModule p Φ) :
    (precompFun hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl

def precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) :
    CartierModule p Φ →+ CartierModule p Φ where
  toFun := precompFun hu
  map_zero' := CartierModule.ext (funext fun j => by
    show subst u (0 : MvPowerSeries ℕ R) = 0
    rw [← coe_substAlgHom hu.hasSubst, map_zero])
  map_add' f g := CartierModule.ext (funext fun j =>
    subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero hu.hasSubst j)

/--
@isnad1 id=eq.1h6v.s8.538182f69698 from=translated src=- shape=e3e4ae74 vocab=45577eb1
-/
@[simp] theorem toPowerSeries_precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    (precomp hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl

/--
@isnad1 id=eq.2h8v.s9.b1b64608dddd from=translated src=- shape=bb8668c9 vocab=45577eb1
-/
theorem precomp_precomp [Φ.IsComm] {u v : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (hv : WittLaw.IsEndo p v) (f : CartierModule p Φ) (j : Fin d) :
    (precomp hv (precomp hu f)).toPowerSeries j = subst (fun n => subst v (u n)) (f.toPowerSeries j) := by
  show subst v (subst u (f.toPowerSeries j)) = _
  rw [subst_comp_subst_apply hu.hasSubst hv.hasSubst]

def frobenius [Φ.IsComm] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_verFam

/--
@isnad1 id=eq.0h5v.s8.100013583c70 from=translated src=- shape=57839958 vocab=5feef824
-/
@[simp] theorem toPowerSeries_frobenius [Φ.IsComm] (f : CartierModule p Φ) :
    (frobenius f).toPowerSeries = fun j => subst (WittLaw.verFam R) (f.toPowerSeries j) := rfl

def verschiebung [Φ.IsComm] [CharP R p] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_frobFam

/--
@isnad1 id=eq.0h5v.s8.c4c3a85767ff from=translated src=- shape=2a361b59 vocab=f8576d3f
-/
@[simp] theorem toPowerSeries_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    (verschiebung f).toPowerSeries = fun j => subst (WittLaw.frobFam p R) (f.toPowerSeries j) := rfl

theorem _root_.Tengoku.FltAnthropic.MvFormalGroup.Hom.subst_subst_elim {τ : Type*} {F : MvFormalGroup d R}
    {G : MvFormalGroup d' R} (φ : F.Hom G) {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin d') :
    subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (φ.toPowerSeries i) =
      subst (Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j))
        (G.toPowerSeries i) := by
  have hab : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hXl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hLR : HasSubst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) :=
    hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j))
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
  have key := congrArg (subst (Sum.elim a b)) (φ.subst_eq i)
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab, subst_comp_subst_apply hLR hab] at key
  rw [key]
  congr 1
  funext s
  rcases s with j | j
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst a (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXl hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inl l)
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst b (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXr hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inr l)

def mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) : CartierModule p Φ' where
  toPowerSeries := fun i => subst f.toPowerSeries (φ.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_eq_zero f.hasSubst_toPowerSeries f.constantCoeff_eq_zero
      (φ.constantCoeff_eq_zero i)
  subst_eq := by
    intro i
    have hf := f.constantCoeff_eq_zero
    show subst (WittLaw.addFam p R) (subst f.toPowerSeries (φ.toPowerSeries i)) =
      subst (Sum.elim (inBlk 0 fun l => subst f.toPowerSeries (φ.toPowerSeries l))
        (inBlk 1 fun l => subst f.toPowerSeries (φ.toPowerSeries l))) (Φ'.toPowerSeries i)
    rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_addFam p R)]
    have hfam : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfam, φ.subst_subst_elim (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) i]
    congr 1
    funext s
    rcases s with l | l
    · show subst (inBlk 0 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 0) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 0)]
      rfl
    · show subst (inBlk 1 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 1) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 1)]
      rfl

/--
@isnad1 id=eq.0h8v.s6.2d9a285ec353 from=translated src=- shape=3b397071 vocab=013df522
-/
@[simp] theorem toPowerSeries_mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (mapFun φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl

def map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') : CartierModule p Φ →+ CartierModule p Φ' where
  toFun := mapFun φ
  map_zero' := CartierModule.ext (funext fun i =>
    subst_zero_of_constantCoeff_eq_zero (φ.constantCoeff_eq_zero i))
  map_add' f g := CartierModule.ext (funext fun i =>
    φ.subst_subst_elim f.constantCoeff_eq_zero g.constantCoeff_eq_zero i)

/--
@isnad1 id=eq.0h8v.s8.27c566ff90fd from=translated src=- shape=6db7393a vocab=a9a29b38
-/
@[simp] theorem toPowerSeries_map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (map φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl

/--
@isnad1 id=eq.0h5v.s8.40fc46b99445 from=translated src=- shape=0f035a55 vocab=f495039c
-/
theorem map_id [Φ.IsComm] (f : CartierModule p Φ) : map (MvFormalGroup.Hom.id Φ) f = f :=
  CartierModule.ext (funext fun i => subst_X f.hasSubst_toPowerSeries i)

/--
@isnad1 id=eq.0h11v.s9.e9adbe34d5b9 from=translated src=- shape=b14db86b vocab=3e2d4277
-/
theorem map_comp [Φ.IsComm] [Φ'.IsComm] [Φ''.IsComm] (ψ : Φ'.Hom Φ'') (φ : Φ.Hom Φ')
    (f : CartierModule p Φ) : map (ψ.comp φ) f = map ψ (map φ f) :=
  CartierModule.ext (funext fun i =>
    subst_comp_subst_apply φ.hasSubst_toPowerSeries f.hasSubst_toPowerSeries (ψ.toPowerSeries i))

/--
@isnad1 id=eq.0h9v.s9.43dcdeffc2c9 from=translated src=- shape=75839ca6 vocab=77a92d0d
-/
theorem map_add_hom [Φ.IsComm] [Φ'.IsComm] (φ ψ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map (φ + ψ) f = map φ f + map ψ f :=
  CartierModule.ext (funext fun i =>
    subst_subst_elim Φ' φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero f.hasSubst_toPowerSeries i)

/--
@isnad1 id=eq.0h7v.s8.a55a604b3fa9 from=translated src=- shape=c80903da vocab=da438a26
-/
theorem map_zero_hom [Φ.IsComm] [Φ'.IsComm] (f : CartierModule p Φ) :
    map (0 : Φ.Hom Φ') f = 0 :=
  CartierModule.ext (funext fun i => by
    show subst f.toPowerSeries (0 : MvPowerSeries (Fin d) R) = 0
    rw [← coe_substAlgHom f.hasSubst_toPowerSeries, map_zero])

/--
@isnad1 id=eq.1h9v.s10.390d6b271cfe from=translated src=- shape=18978649 vocab=c39dbb11
-/
theorem map_precomp [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    map φ (precomp hu f) = precomp hu (map φ f) :=
  CartierModule.ext (funext fun i =>
    (subst_comp_subst_apply f.hasSubst_toPowerSeries hu.hasSubst (φ.toPowerSeries i)).symm)

def endAct [Φ.IsComm] : MvFormalGroup.End Φ →+* AddMonoid.End (CartierModule p Φ) where
  toFun φ := map φ
  map_one' := AddMonoidHom.ext map_id
  map_mul' φ ψ := AddMonoidHom.ext (map_comp φ ψ)
  map_zero' := AddMonoidHom.ext map_zero_hom
  map_add' φ ψ := AddMonoidHom.ext (map_add_hom φ ψ)

/--
@isnad1 id=eq.0h6v.s9.5c2ac87c686b from=translated src=- shape=77c0dfdf vocab=b0cf2435
-/
@[simp] theorem endAct_apply [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ f = map φ f := rfl

end CartierModule

namespace WittLaw

def nsmulFam (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (n : ℕ) : ℕ → MvPowerSeries ℕ R :=
  fun k => ((MvPolynomial.map (Int.castRingHom R)
    (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n k)) : MvPolynomial ℕ R) :
      MvPowerSeries ℕ R)

omit hp in

/--
@isnad1 id=hassubst.2h4v.s6.eb92450c585e from=translated src=- shape=c6c5d8af vocab=6a28a291
-/
theorem hasSubst_finCases {τ : Type*} {u₀ u₁ : ℕ → MvPowerSeries τ R} (h₀ : HasSubst u₀)
    (h₁ : HasSubst u₁) :
    HasSubst (fun im : Fin 2 × ℕ => (Fin.cases (u₀ im.2) (fun _ => u₁ im.2) im.1 : MvPowerSeries τ R)) := by
  refine ⟨fun ⟨i, m⟩ => Fin.cases (h₀.const_coeff m) (fun _ => h₁.const_coeff m) i, fun e => ?_⟩
  refine (((h₀.coeff_zero e).image (Prod.mk 0)).union ((h₁.coeff_zero e).image (Prod.mk 1))).subset ?_
  rintro ⟨i, m⟩ him
  revert him
  refine Fin.cases (fun him => Or.inl ⟨m, him, rfl⟩) (fun l him => Or.inr ⟨m, him, ?_⟩) i
  fin_cases l; rfl

variable (p R) in

def stepFam (n : ℕ) : Fin 2 × ℕ → MvPowerSeries ℕ R :=
  fun im => Fin.cases (nsmulFam p R n im.2) (fun _ => X im.2) im.1

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

def tangent [Φ.IsComm] : CartierModule p Φ →+ (Fin d → R) where
  toFun f := fun j => coeff (Finsupp.single 0 1) (f.toPowerSeries j)
  map_zero' := by
    funext j
    simp
  map_add' f g := by
    funext j
    show coeff (Finsupp.single 0 1) (subst (Sum.elim f.toPowerSeries g.toPowerSeries)
      (Φ.toPowerSeries j)) = _
    have h0 : ∀ s, ((Sum.elim f.toPowerSeries g.toPowerSeries) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [f.constantCoeff_eq_zero l, g.constantCoeff_eq_zero l]
    rw [coeff_single_subst h0, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Φ.coeff_single_inl, Φ.coeff_single_inr, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl

/--
@isnad1 id=eq.0h6v.s8.9ad4ed119c00 from=translated src=- shape=26bdaa14 vocab=c8f0d4c6
-/
@[simp] theorem tangent_apply [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    tangent f j = coeff (Finsupp.single 0 1) (f.toPowerSeries j) := rfl

def curveFam (R : Type u) [CommRing R] : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | _ + 1 => 0

def curve (f : CartierModule p Φ) : Fin d → PowerSeries R :=
  fun j => subst (curveFam R) (f.toPowerSeries j)

namespace Examples

def addLinear (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] (v : Fin d → R) :
    CartierModule p (addMv d R) where
  toPowerSeries := fun i => v i • (X 0 : MvPowerSeries ℕ R)
  constantCoeff_eq_zero := fun i => by simp
  subst_eq := by
    intro i
    have hc : ∀ l, ((fun l => v l • (X 0 : MvPowerSeries ℕ R)) l).constantCoeff = 0 :=
      fun l => by simp
    have h0 : ∀ s, ((Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R))) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [constantCoeff_inBlk 0 hc l, constantCoeff_inBlk 1 hc l]
    show subst (WittLaw.addFam p R) (v i • (X 0 : MvPowerSeries ℕ R)) =
      subst (Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R)))
        ((X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) + X (Sum.inr i))
    rw [subst_X_add_X h0]
    simp only [Sum.elim_inl, Sum.elim_inr, inBlk_apply]
    rw [← coe_substAlgHom (hasSubst_addFam p R), ← coe_substAlgHom (hasSubst_blk 0),
      ← coe_substAlgHom (hasSubst_blk 1), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower,
      AlgHom.map_smul_of_tower, coe_substAlgHom, coe_substAlgHom, coe_substAlgHom,
      subst_X (hasSubst_addFam p R), subst_X (hasSubst_blk 0), subst_X (hasSubst_blk 1),
      WittLaw.addFam, WittVector.wittAdd_zero, ← smul_add]
    congr 1
    simp [WittLaw.blk]

/--
@isnad1 id=eq.0h5v.s6.d3405ff7f974 from=translated src=- shape=69e1783c vocab=f38ed3fd
-/
@[simp] theorem toPowerSeries_addLinear (v : Fin d → R) (i : Fin d) :
    (addLinear p v).toPowerSeries i = v i • (X 0 : MvPowerSeries ℕ R) := rfl

end Examples

end CartierModule

end Tengoku.FltAnthropic.MvFormalGroup

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
