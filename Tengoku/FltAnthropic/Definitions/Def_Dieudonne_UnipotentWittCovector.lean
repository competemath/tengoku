import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_FontaineHodge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Function

universe u v w u' v'

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {S : Type v} [CommRing S]

/--
@isnad1 id=directed.0h2v.s7.b3db1d1f7e0c from=translated src=- shape=2ae80427 vocab=c8c75c05
-/
instance shiftLE_directedSystem :
    DirectedSystem (fun n => TruncatedWittVector p n S)
      fun _ _ h => (shiftLE (p := p) (R := S) h) where
  map_self _ x := shiftLE_refl x
  map_map _ _ _ h₁ h₂ x := shiftLE_shiftLE h₁ h₂ x

/--
@isnad1 id=ex.2h5v.s8.b1c86b416711 from=translated src=- shape=187d699c vocab=7583be0d
-/
theorem exists_shiftLE_eq_of_forall_coeff_eq_zero {n m : ℕ} (h : n ≤ m)
    (y : TruncatedWittVector p m S) (hy : ∀ i : Fin m, (i : ℕ) < m - n → y.coeff i = 0) :
    ∃ x : TruncatedWittVector p n S, shiftLE h x = y := by
  refine ⟨TruncatedWittVector.mk p fun j : Fin n => y.coeff ⟨j + (m - n), by omega⟩, ?_⟩
  refine TruncatedWittVector.ext fun i => ?_
  rw [coeff_shiftLE]
  split_ifs with hi
  · rw [TruncatedWittVector.coeff_mk]
    congr 1
    exact Fin.ext (by simp only; omega)
  · exact (hy i (by omega)).symm

theorem eq_zero_of_length_zero (x : TruncatedWittVector p 0 S) : x = 0 :=
  TruncatedWittVector.ext fun i => i.elim0

/--
@isnad1 id=eq.1h4v.s7.59eff959b9af from=translated src=- shape=e1c9564e vocab=98827b55
-/
theorem truncate_self {n : ℕ} (h : n ≤ n) (x : TruncatedWittVector p n S) :
    TruncatedWittVector.truncate h x = x :=
  TruncatedWittVector.ext fun i => by
    rw [TruncatedWittVector.coeff_truncate]
    congr 1

noncomputable def frobeniusAddHom {n : ℕ} (hS : (p : S) = 0) :
    TruncatedWittVector p n S →+ TruncatedWittVector p n S where
  toFun := frobeniusFun
  map_zero' := frobeniusFun_zero
  map_add' := frobeniusFun_add hS

/--
@isnad1 id=eq.1h4v.s7.cd3fcb326322 from=translated src=- shape=fd74b819 vocab=bbc01a90
-/
@[simp] theorem frobeniusAddHom_apply {n : ℕ} (hS : (p : S) = 0) (x : TruncatedWittVector p n S) :
    frobeniusAddHom hS x = frobeniusFun x := rfl

end TruncWitt

def UnipotentWittCovector (p : ℕ) [Fact p.Prime] (S : Type v) [CommRing S] : Type v :=
  AddCommGroup.DirectLimit (fun n => TruncatedWittVector p n S) fun _ _ h => TruncWitt.shiftLE h

namespace UnipotentWittCovector

section Basic

variable (p : ℕ) [hp : Fact p.Prime] (S : Type v) [CommRing S]

noncomputable instance instAddCommGroup : AddCommGroup (UnipotentWittCovector p S) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (fun n => TruncatedWittVector p n S) fun _ _ h => TruncWitt.shiftLE h))

noncomputable instance instInhabited : Inhabited (UnipotentWittCovector p S) := ⟨0⟩

noncomputable def of (n : ℕ) : TruncatedWittVector p n S →+ UnipotentWittCovector p S :=
  AddCommGroup.DirectLimit.of (fun n => TruncatedWittVector p n S) (fun _ _ h => TruncWitt.shiftLE h) n

variable {p S}
variable {n m : ℕ}

/--
@isnad1 id=eq.1h5v.s9.eb4f5f158fca from=translated src=- shape=b554ceb8 vocab=b3b7d5cd
-/
@[simp] theorem of_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n S) :
    of p S m (TruncWitt.shiftLE h x) = of p S n x :=
  AddCommGroup.DirectLimit.of_f _ _

/--
@isnad1 id=eq.0h4v.s9.e16a77a1d962 from=translated src=- shape=a37a2d55 vocab=d949598c
-/
@[simp] theorem of_shift (x : TruncatedWittVector p n S) :
    of p S (n + 1) (TruncWitt.shift x) = of p S n x := by
  rw [← TruncWitt.shiftLE_succ, of_shiftLE]

/--
@isnad1 id=var.0h5v.s7.e6968673ee79 from=translated src=- shape=bb13feb0 vocab=e7bd197b
-/
@[elab_as_elim]
protected theorem induction_on {C : UnipotentWittCovector p S → Prop} (z : UnipotentWittCovector p S)
    (ih : ∀ (n : ℕ) (x : TruncatedWittVector p n S), C (of p S n x)) : C z :=
  AddCommGroup.DirectLimit.induction_on z ih

/--
@isnad1 id=ex.0h3v.s7.81fce4670eb8 from=translated src=- shape=3e9cdfa3 vocab=e7bd197b
-/
theorem exists_of (z : UnipotentWittCovector p S) :
    ∃ (n : ℕ) (x : TruncatedWittVector p n S), of p S n x = z :=
  UnipotentWittCovector.induction_on z fun n x => ⟨n, x, rfl⟩

/--
@isnad1 id=ex.1h4v.s8.490429949a23 from=translated src=- shape=5fa4e2fa vocab=b3b7d5cd
-/
theorem exists_shiftLE_eq_zero_of_of_eq_zero {x : TruncatedWittVector p n S} (hx : of p S n x = 0) :
    ∃ (m : ℕ) (h : n ≤ m), TruncWitt.shiftLE h x = 0 :=
  AddCommGroup.DirectLimit.of.zero_exact (f := fun _ _ h => TruncWitt.shiftLE (p := p) (R := S) h)
    n x hx

/--
@isnad1 id=injectiv.0h3v.s7.649c6c59e78e from=translated src=- shape=e3a8e32a vocab=04996e56
-/
theorem of_injective (n : ℕ) : Injective (of p S n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨m, h, hm⟩ := exists_shiftLE_eq_zero_of_of_eq_zero hx
  exact TruncWitt.shiftLE_injective h (by rw [hm, map_zero])

/--
@isnad1 id=iff.0h6v.s9.85561a3e2e72 from=translated src=- shape=c0538b6f vocab=cf449e1f
-/
theorem of_eq_of_iff (x : TruncatedWittVector p n S) (y : TruncatedWittVector p m S) :
    of p S n x = of p S m y ↔
      TruncWitt.shiftLE (le_max_left n m) x = TruncWitt.shiftLE (le_max_right n m) y := by
  constructor
  · intro h
    apply of_injective (max n m)
    rwa [of_shiftLE, of_shiftLE]
  · intro h
    rw [← of_shiftLE (le_max_left n m) x, h, of_shiftLE]

/--
@isnad1 id=eq.0h3v.s8.91da4cb9edaa from=translated src=- shape=1303e70d vocab=e7bd197b
-/
theorem of_zero_eq_zero (x : TruncatedWittVector p 0 S) : of p S 0 x = 0 := by
  rw [TruncWitt.eq_zero_of_length_zero x, map_zero]

section Lift

variable {P : Type w} [AddCommGroup P]

/--
@isnad1 id=eq.2h7v.s10.4d4015d8c25d from=translated src=- shape=c42d30ac vocab=7982ba8a
-/
theorem compat_shiftLE (g : ∀ n, TruncatedWittVector p n S →+ P)
    (hg : ∀ (n : ℕ) (x : TruncatedWittVector p n S), g (n + 1) (TruncWitt.shift x) = g n x)
    (h : n ≤ m) (x : TruncatedWittVector p n S) : g m (TruncWitt.shiftLE h x) = g n x := by
  induction h with
  | refl => rw [TruncWitt.shiftLE_refl]
  | @step m h ih =>
    rw [← TruncWitt.shiftLE_shiftLE h (Nat.le_succ m), TruncWitt.shiftLE_succ, hg, ih]

variable (p S) in

noncomputable def lift (g : ∀ n, TruncatedWittVector p n S →+ P)
    (hg : ∀ (n : ℕ) (x : TruncatedWittVector p n S), g (n + 1) (TruncWitt.shift x) = g n x) :
    UnipotentWittCovector p S →+ P :=
  AddCommGroup.DirectLimit.lift (fun n => TruncatedWittVector p n S) (fun _ _ h => TruncWitt.shiftLE h)
    P g fun _ _ h x => compat_shiftLE g hg h x

/--
@isnad1 id=eq.1h6v.s10.59602e08c9c1 from=translated src=- shape=073f2052 vocab=0c2200df
-/
@[simp] theorem lift_of (g : ∀ n, TruncatedWittVector p n S →+ P)
    (hg : ∀ (n : ℕ) (x : TruncatedWittVector p n S), g (n + 1) (TruncWitt.shift x) = g n x)
    (x : TruncatedWittVector p n S) : lift p S g hg (of p S n x) = g n x :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

/--
@isnad1 id=eq.1h5v.s9.5500823d4079 from=translated src=- shape=21f58f3c vocab=3706d4d6
-/
theorem hom_ext {f g : UnipotentWittCovector p S →+ P}
    (h : ∀ (n : ℕ) (x : TruncatedWittVector p n S), f (of p S n x) = g (of p S n x)) : f = g :=
  AddMonoidHom.ext fun z => UnipotentWittCovector.induction_on z h

end Lift

variable (p S) in

noncomputable def verschiebung : UnipotentWittCovector p S →+ UnipotentWittCovector p S :=
  lift p S (fun n => (of p S n).comp (TruncWitt.verschiebung (p := p) (n := n) (R := S))) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← TruncWitt.shiftLE_succ,
      TruncWitt.verschiebung_shiftLE, of_shiftLE]

/--
@isnad1 id=eq.0h4v.s9.b5eedc52d3b5 from=translated src=- shape=c63e2cab vocab=61e70a86
-/
@[simp] theorem verschiebung_of (x : TruncatedWittVector p n S) :
    verschiebung p S (of p S n x) = of p S n (TruncWitt.verschiebung x) :=
  lift_of _ _ _

/--
@isnad1 id=eq.0h4v.s9.d80864953321 from=translated src=- shape=e453426d vocab=9999e81a
-/
theorem verschiebung_of_succ (y : TruncatedWittVector p (n + 1) S) :
    verschiebung p S (of p S (n + 1) y) =
      of p S n (TruncatedWittVector.truncate (Nat.le_succ n) y) := by
  rw [verschiebung_of, ← TruncWitt.shift_truncate_succ, of_shift]

/--
@isnad1 id=eq.1h5v.s9.9e5e3d2da63c from=translated src=- shape=790d72a4 vocab=e175a3f3
-/
theorem verschiebung_iterate_of_le (h : n ≤ m) (y : TruncatedWittVector p m S) :
    (verschiebung p S)^[m - n] (of p S m y) = of p S n (TruncatedWittVector.truncate h y) := by
  induction h with
  | refl =>
    rw [Nat.sub_self, Function.iterate_zero_apply]
    exact congrArg (of p S n) (TruncWitt.truncate_self _ y).symm
  | @step m h ih =>
    rw [Nat.succ_sub h, Function.iterate_succ_apply, verschiebung_of_succ, ih,
      TruncatedWittVector.truncate_truncate]

/--
@isnad1 id=eq.0h4v.s8.dfca9212b1ad from=translated src=- shape=be852c3a vocab=1000f399
-/
theorem verschiebung_iterate_of (x : TruncatedWittVector p n S) :
    (verschiebung p S)^[n] (of p S n x) = 0 := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, of_zero_eq_zero]
  | succ n ih => rw [Function.iterate_succ_apply, verschiebung_of_succ, ih]

/--
@isnad1 id=ex.0h3v.s8.4a1a27c9f514 from=translated src=- shape=1044adbe vocab=7c96ce6b
-/
theorem exists_verschiebung_iterate_eq_zero (z : UnipotentWittCovector p S) :
    ∃ n : ℕ, (verschiebung p S)^[n] z = 0 := by
  obtain ⟨n, x, rfl⟩ := exists_of z
  exact ⟨n, verschiebung_iterate_of x⟩

/--
@isnad1 id=ex.1h4v.s8.f69fbebfe983 from=translated src=- shape=c4b50092 vocab=1000f399
-/
theorem exists_of_eq_of_verschiebung_iterate_eq_zero {z : UnipotentWittCovector p S}
    (hz : (verschiebung p S)^[n] z = 0) : ∃ x : TruncatedWittVector p n S, of p S n x = z := by
  obtain ⟨m, y, rfl⟩ := exists_of z

  set y' : TruncatedWittVector p (m + n) S := TruncWitt.shiftLE (Nat.le_add_right m n) y with hy'
  have hyy' : of p S (m + n) y' = of p S m y := of_shiftLE _ _
  have hit := verschiebung_iterate_of_le (Nat.le_add_right m n) y'
  rw [Nat.add_sub_cancel_left, hyy', hz] at hit
  replace hz := hit.symm

  have htr : TruncatedWittVector.truncate (Nat.le_add_right m n) y' = 0 :=
    of_injective m (by rw [hz, map_zero])
  obtain ⟨x, hx⟩ := TruncWitt.exists_shiftLE_eq_of_forall_coeff_eq_zero (Nat.le_add_left n m) y'
    (fun i hi => by
      have hi' : (i : ℕ) < m := by omega
      have := congrArg (fun z => TruncatedWittVector.coeff ⟨(i : ℕ), hi'⟩ z) htr
      simpa only [TruncatedWittVector.coeff_truncate, TruncatedWittVector.coeff_zero, Fin.castLE_mk,
        Fin.eta] using this)
  exact ⟨x, by rw [← hyy', ← hx, of_shiftLE]⟩

/--
@isnad1 id=iff.0h4v.s8.1d841f893e62 from=translated src=- shape=3cdf793d vocab=1000f399
-/
theorem verschiebung_iterate_eq_zero_iff (z : UnipotentWittCovector p S) :
    (verschiebung p S)^[n] z = 0 ↔ ∃ x : TruncatedWittVector p n S, of p S n x = z :=
  ⟨exists_of_eq_of_verschiebung_iterate_eq_zero, by rintro ⟨x, rfl⟩; exact verschiebung_iterate_of x⟩

/--
@isnad1 id=iff.0h3v.s9.d2351d24ab19 from=translated src=- shape=f82db27d vocab=443aa953
-/
theorem verschiebung_eq_zero_iff (z : UnipotentWittCovector p S) :
    verschiebung p S z = 0 ↔ ∃ x : TruncatedWittVector p 1 S, of p S 1 x = z :=
  verschiebung_iterate_eq_zero_iff (n := 1) z

section Map

variable {T : Type w} [CommRing T] {U : Type u'} [CommRing U]

variable (p) in

noncomputable def map (f : S →+* T) : UnipotentWittCovector p S →+ UnipotentWittCovector p T :=
  lift p S (fun n => (of p T n).comp (TruncWitt.map (p := p) (n := n) f).toAddMonoidHom) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddMonoidHom.coe_coe, TruncWitt.map_shift,
      of_shift]

/--
@isnad1 id=eq.0h6v.s9.47f60227a956 from=translated src=- shape=282e1b8e vocab=1826fa7e
-/
@[simp] theorem map_of (f : S →+* T) (x : TruncatedWittVector p n S) :
    map p f (of p S n x) = of p T n (TruncWitt.map f x) :=
  lift_of _ _ _

/--
@isnad1 id=eq.0h3v.s7.359cae2d43db from=translated src=- shape=132a13ce vocab=35f17ce0
-/
theorem map_id (z : UnipotentWittCovector p S) : map p (RingHom.id S) z = z := by
  induction z using UnipotentWittCovector.induction_on with
  | ih n x => rw [map_of, TruncWitt.map_id]

/--
@isnad1 id=eq.0h7v.s9.999d0d909e90 from=translated src=- shape=9928f400 vocab=f5ceac46
-/
theorem map_map (f : S →+* T) (g : T →+* U) (z : UnipotentWittCovector p S) :
    map p g (map p f z) = map p (g.comp f) z := by
  induction z using UnipotentWittCovector.induction_on with
  | ih n x => rw [map_of, map_of, map_of, TruncWitt.map_map]

/--
@isnad1 id=eq.0h6v.s8.5031ac27529e from=translated src=- shape=35ae91f9 vocab=8c0483d6
-/
theorem map_comp (f : S →+* T) (g : T →+* U) :
    (map p g).comp (map p f) = map p (g.comp f) :=
  AddMonoidHom.ext fun z => map_map f g z

/--
@isnad1 id=eq.0h5v.s9.cfa675678679 from=translated src=- shape=c3d48b90 vocab=34a196cf
-/
theorem map_verschiebung (f : S →+* T) (z : UnipotentWittCovector p S) :
    map p f (verschiebung p S z) = verschiebung p T (map p f z) := by
  induction z using UnipotentWittCovector.induction_on with
  | ih n x => rw [verschiebung_of, map_of, map_of, verschiebung_of, TruncWitt.map_verschiebung]

/--
@isnad1 id=injectiv.1h4v.s8.846211be3539 from=translated src=- shape=5caa9e7f vocab=6613e3cc
-/
theorem map_injective {f : S →+* T} (hf : Injective f) : Injective (map p f) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [map_of] at hz
  have hx : TruncWitt.map f x = 0 := of_injective n (by rw [hz, map_zero])
  rw [TruncWitt.map_injective hf (hx.trans (map_zero _).symm), map_zero]

end Map

end Basic

section Frobenius

noncomputable def frobenius (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (S : Type v) [CommRing S] [Algebra R S] : UnipotentWittCovector p S →+ UnipotentWittCovector p S :=
  lift p S (fun n => (of p S n).comp (TruncWitt.frobeniusAddHom (natCast_eq_zero_of_algebra R p S)))
    fun n x => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, TruncWitt.frobeniusAddHom_apply,
        TruncWitt.frobeniusAddHom_apply, TruncWitt.frobeniusFun_shift, of_shift]

variable (R : Type u) [CommRing R] {p : ℕ} [hp : Fact p.Prime] [CharP R p]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {n : ℕ}

/--
@isnad1 id=eq.0h5v.s9.12cc24b1af7c from=translated src=- shape=b035d81a vocab=f4638d8d
-/
@[simp] theorem frobenius_of (x : TruncatedWittVector p n S) :
    frobenius R p S (of p S n x) = of p S n (TruncWitt.frobeniusFun x) :=
  lift_of _ _ _

/--
@isnad1 id=eq.0h4v.s8.7eeaaf9cfaa7 from=translated src=- shape=df9b2beb vocab=3afef600
-/
theorem frobenius_verschiebung (z : UnipotentWittCovector p S) :
    frobenius R p S (verschiebung p S z) = (p : ℤ) • z := by
  induction z using UnipotentWittCovector.induction_on with
  | ih n x =>
    rw [verschiebung_of, frobenius_of,
      TruncWitt.frobeniusFun_verschiebung_eq_smul (natCast_eq_zero_of_algebra R p S), map_zsmul]

/--
@isnad1 id=eq.0h4v.s8.a01c47e6443f from=translated src=- shape=dea23958 vocab=3afef600
-/
theorem verschiebung_frobenius (z : UnipotentWittCovector p S) :
    verschiebung p S (frobenius R p S z) = (p : ℤ) • z := by
  induction z using UnipotentWittCovector.induction_on with
  | ih n x =>
    rw [frobenius_of, verschiebung_of,
      TruncWitt.verschiebung_frobeniusFun (natCast_eq_zero_of_algebra R p S), map_zsmul]

/--
@isnad1 id=eq.0h4v.s9.cc58997a5006 from=translated src=- shape=a18ee6bf vocab=93f2a4a1
-/
theorem frobenius_verschiebung_comm (z : UnipotentWittCovector p S) :
    frobenius R p S (verschiebung p S z) = verschiebung p S (frobenius R p S z) := by
  rw [frobenius_verschiebung, verschiebung_frobenius]

variable (p S) in

noncomputable def dieudonneDatum : DieudonneDatum (p : ℤ) (UnipotentWittCovector p S) where
  F := (frobenius R p S).toIntLinearMap
  V := (verschiebung p S).toIntLinearMap
  fv := LinearMap.ext fun z => frobenius_verschiebung R z
  vf := LinearMap.ext fun z => verschiebung_frobenius R z

/--
@isnad1 id=eq.0h4v.s8.a8566e021259 from=translated src=- shape=8dec93c5 vocab=2754b755
-/
@[simp] theorem dieudonneDatum_F_apply (z : UnipotentWittCovector p S) :
    (dieudonneDatum R p S).F z = frobenius R p S z := rfl

/--
@isnad1 id=eq.0h4v.s8.db5af9d533a3 from=translated src=- shape=3fd72f51 vocab=c552aa53
-/
@[simp] theorem dieudonneDatum_V_apply (z : UnipotentWittCovector p S) :
    (dieudonneDatum R p S).V z = verschiebung p S z := rfl

/--
@isnad1 id=eq.1h4v.s8.1da406f57856 from=translated src=- shape=6dcaf015 vocab=0ea01517
-/
theorem pow_nsmul_of (hS : (p : S) = 0) (x : TruncatedWittVector p n S) : p ^ n • of p S n x = 0 := by
  rw [← map_nsmul, TruncWitt.pow_card_nsmul_eq_zero hS, map_zero]

/--
@isnad1 id=ex.1h3v.s7.5d101af89cf2 from=translated src=- shape=f5ac1731 vocab=409ffbca
-/
theorem exists_pow_nsmul_eq_zero (hS : (p : S) = 0) (z : UnipotentWittCovector p S) :
    ∃ n : ℕ, p ^ n • z = 0 := by
  obtain ⟨n, x, rfl⟩ := exists_of z
  exact ⟨n, pow_nsmul_of hS x⟩

/--
@isnad1 id=eq.0h7v.s9.ea798836d78f from=translated src=- shape=4f270be7 vocab=62decc33
-/
theorem map_frobenius {T : Type w} [CommRing T] (R' : Type u') [CommRing R'] [CharP R' p]
    [Algebra R' T] (f : S →+* T) (z : UnipotentWittCovector p S) :
    map p f (frobenius R p S z) = frobenius R' p T (map p f z) := by
  induction z using UnipotentWittCovector.induction_on with
  | ih n x => rw [frobenius_of, map_of, map_of, frobenius_of, TruncWitt.map_frobeniusFun]

end Frobenius

section WKer

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A]

noncomputable def wKer (π : ℛ →+* A) : AddSubgroup (UnipotentWittCovector p A) where
  carrier := {z | ∃ (n : ℕ) (x : TruncatedWittVector p n A),
    x ∈ TruncWitt.fontaineKer p n π ∧ of p A n x = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, x, hx, rfl⟩ ⟨m, y, hy, rfl⟩
    refine ⟨max n m, TruncWitt.shiftLE (le_max_left n m) x + TruncWitt.shiftLE (le_max_right n m) y,
      add_mem (TruncWitt.shiftLE_mem_fontaineKer _ hx) (TruncWitt.shiftLE_mem_fontaineKer _ hy), ?_⟩
    rw [map_add, of_shiftLE, of_shiftLE]
  neg_mem' := by
    rintro _ ⟨n, x, hx, rfl⟩
    exact ⟨n, -x, neg_mem hx, map_neg _ _⟩

variable {p} {π : ℛ →+* A}

/--
@isnad1 id=iff.0h5v.s8.0027e91bed52 from=translated src=- shape=95f8ddf6 vocab=e27bd49f
-/
theorem mem_wKer_iff (z : UnipotentWittCovector p A) :
    z ∈ wKer p π ↔ ∃ (n : ℕ) (x : TruncatedWittVector p n A),
      x ∈ TruncWitt.fontaineKer p n π ∧ of p A n x = z :=
  Iff.rfl

/--
@isnad1 id=mem.1h6v.s8.a66cac79fcb6 from=translated src=- shape=8ff76a0a vocab=e27bd49f
-/
theorem of_mem_wKer {x : TruncatedWittVector p n A} (hx : x ∈ TruncWitt.fontaineKer p n π) :
    of p A n x ∈ wKer p π :=
  ⟨n, x, hx, rfl⟩

/--
@isnad1 id=iff.3h6v.s9.5b8d9fbac249 from=translated src=- shape=a654884f vocab=3d397340
-/
theorem of_mem_wKer_iff (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π) (x : TruncatedWittVector p n A) :
    of p A n x ∈ wKer p π ↔ x ∈ TruncWitt.fontaineKer p n π := by
  refine ⟨?_, of_mem_wKer⟩
  rintro ⟨m, y, hy, hxy⟩
  rw [of_eq_of_iff] at hxy
  have hy' : TruncWitt.shiftLE (le_max_left m n) y ∈ TruncWitt.fontaineKer p (max m n) π :=
    TruncWitt.shiftLE_mem_fontaineKer _ hy
  rw [hxy] at hy'
  exact TruncWitt.mem_fontaineKer_of_shiftLE_mem hp' hπ hπs (le_max_right m n) hy'

/--
@isnad1 id=le.1h9v.s8.e2a57836b522 from=translated src=- shape=5373cf7f vocab=fb0c1f4d
-/
theorem map_wKer_le {ℛ' : Type w} [CommRing ℛ'] {A' : Type u'} [CommRing A']
    (f : ℛ →+* ℛ') (g : A →+* A') (π' : ℛ' →+* A') (hcomm : π'.comp f = g.comp π) :
    (wKer p π).map (map p g) ≤ wKer p π' := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, x, hx, rfl⟩ := hz
  exact ⟨n, TruncWitt.map g x, TruncWitt.map_mem_fontaineKer f g π' hcomm hx, (map_of g x).symm⟩

/--
@isnad1 id=mem.2h10v.s8.7da5faa214ad from=translated src=- shape=e64a82b4 vocab=ec197c7f
-/
theorem map_mem_wKer {ℛ' : Type w} [CommRing ℛ'] {A' : Type u'} [CommRing A']
    (f : ℛ →+* ℛ') (g : A →+* A') (π' : ℛ' →+* A') (hcomm : π'.comp f = g.comp π)
    {z : UnipotentWittCovector p A} (hz : z ∈ wKer p π) : map p g z ∈ wKer p π' :=
  map_wKer_le f g π' hcomm ⟨z, hz, rfl⟩

end WKer

end UnipotentWittCovector

namespace DieudonneModule

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra R A]

noncomputable def toCovector : DieudonneModule R p A →+ UnipotentWittCovector p A :=
  lift R p A (fun n => (UnipotentWittCovector.of p A n).comp (wittHom R p n A).subtype) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply,
      AddSubgroup.subtype_apply, coe_wittHomShift, UnipotentWittCovector.of_shift]

variable {R p A}
variable {n : ℕ}

/--
@isnad1 id=eq.0h5v.s11.733a3b28c304 from=translated src=- shape=666d62be vocab=23a831e0
-/
@[simp] theorem toCovector_of (x : wittHom R p n A) :
    toCovector R p A (of R p A n x) = UnipotentWittCovector.of p A n x :=
  lift_of _ _ _

/--
@isnad1 id=injectiv.0h3v.s8.2382232c69e6 from=translated src=- shape=716635d0 vocab=da034483
-/
theorem toCovector_injective : Injective (toCovector R p A) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [toCovector_of] at hz
  have : (x : TruncatedWittVector p n A) = 0 :=
    UnipotentWittCovector.of_injective n (hz.trans (map_zero _).symm)
  rw [show x = 0 from Subtype.ext this, map_zero]

/--
@isnad1 id=eq.0h4v.s9.e8f20cb84b40 from=translated src=- shape=14238aa1 vocab=5b57b6ad
-/
theorem toCovector_verschiebung (z : DieudonneModule R p A) :
    toCovector R p A (verschiebung R p A z) =
      UnipotentWittCovector.verschiebung p A (toCovector R p A z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [verschiebung_of, toCovector_of, toCovector_of, UnipotentWittCovector.verschiebung_of,
      coe_wittHomVerschiebung]

/--
@isnad1 id=eq.0h4v.s9.c8abc55611c8 from=translated src=- shape=332eb140 vocab=eb259b30
-/
theorem toCovector_frobenius [CharP R p] (z : DieudonneModule R p A) :
    toCovector R p A (frobenius R p A z) =
      UnipotentWittCovector.frobenius R p A (toCovector R p A z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [frobenius_of, toCovector_of, toCovector_of, UnipotentWittCovector.frobenius_of,
      coe_wittHomFrobenius]

/--
@isnad1 id=eq.0h6v.s10.699c7bdad344 from=translated src=- shape=cf8697b6 vocab=1b1e7d12
-/
theorem toCovector_map {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (z : DieudonneModule R p A) :
    toCovector R p B (map R p φ z) =
      UnipotentWittCovector.map p (φ : A →ₐ[R] B).toRingHom (toCovector R p A z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of, toCovector_of, toCovector_of, UnipotentWittCovector.map_of, coe_wittHomMap]

/--
@isnad1 id=mem.1h6v.s9.420bcb0cdddf from=translated src=- shape=85e97da1 vocab=2d6f7b5b
-/
theorem toCovector_mem_wKer_of_mem_fontaineHodge {ℛ : Type w} [CommRing ℛ] {π : ℛ →+* A}
    {z : DieudonneModule R p A} (hz : z ∈ fontaineHodge R p π) :
    toCovector R p A z ∈ UnipotentWittCovector.wKer p π := by
  obtain ⟨n, x, hx, rfl⟩ := hz
  rw [toCovector_of]
  exact UnipotentWittCovector.of_mem_wKer hx

/--
@isnad1 id=iff.3h6v.s9.807fc37797b8 from=translated src=- shape=7e474d1a vocab=6c8fb6b7
-/
theorem toCovector_mem_wKer_iff {ℛ : Type w} [CommRing ℛ] {π : ℛ →+* A}
    (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ) (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    (hπs : Surjective π) (z : DieudonneModule R p A) :
    toCovector R p A z ∈ UnipotentWittCovector.wKer p π ↔ z ∈ fontaineHodge R p π := by
  refine ⟨fun hz => ?_, toCovector_mem_wKer_of_mem_fontaineHodge⟩
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [toCovector_of, UnipotentWittCovector.of_mem_wKer_iff hp' hπ hπs] at hz
  exact of_mem_fontaineHodge hz

section Eval

variable {T : Type w} [CommRing T] [Algebra R T]

variable (R p) in

noncomputable def eval (f : A →ₐ[R] T) : DieudonneModule R p A →+ UnipotentWittCovector p T :=
  (UnipotentWittCovector.map p f.toRingHom).comp (toCovector R p A)

/--
@isnad1 id=eq.0h6v.s9.fd0f0585a32d from=translated src=- shape=ade6a159 vocab=04ee4e56
-/
theorem eval_apply (f : A →ₐ[R] T) (z : DieudonneModule R p A) :
    eval R p f z = UnipotentWittCovector.map p f.toRingHom (toCovector R p A z) := rfl

/--
@isnad1 id=eq.0h7v.s11.6fdfef756c40 from=translated src=- shape=2e2d98d1 vocab=8c7fc7f2
-/
@[simp] theorem eval_of (f : A →ₐ[R] T) (x : wittHom R p n A) :
    eval R p f (of R p A n x) =
      UnipotentWittCovector.of p T n (TruncWitt.map f.toRingHom (x : TruncatedWittVector p n A)) := by
  rw [eval_apply, toCovector_of, UnipotentWittCovector.map_of]

/--
@isnad1 id=eq.0h4v.s9.cb534191397e from=translated src=- shape=a16db467 vocab=eaf04a9d
-/
theorem eval_id (z : DieudonneModule R p A) : eval R p (AlgHom.id R A) z = toCovector R p A z := by
  rw [eval_apply]
  exact UnipotentWittCovector.map_id _

/--
@isnad1 id=eq.0h7v.s10.30084ef0d3cd from=translated src=- shape=98aa6ac2 vocab=f659b900
-/
theorem eval_convMul (f g : WithConv (A →ₐ[R] T)) (z : DieudonneModule R p A) :
    eval R p (f * g).ofConv z = eval R p f.ofConv z + eval R p g.ofConv z := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [eval_of, eval_of, eval_of, map_convMul_of_mem_wittHom x.2 f g, map_add]

/--
@isnad1 id=eq.0h5v.s8.8508d4ff17c6 from=translated src=- shape=63935258 vocab=6ab9c64f
-/
theorem eval_convOne (z : DieudonneModule R p A) :
    eval R p (1 : WithConv (A →ₐ[R] T)).ofConv z = 0 := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [eval_of]
    have hfac : (1 : WithConv (A →ₐ[R] T)).ofConv.toRingHom =
        (algebraMap R T).comp (Bialgebra.counitAlgHom R A).toRingHom := by
      refine RingHom.ext fun c => ?_
      simp [AlgHom.convOne_apply]
    rw [hfac, ← TruncWitt.map_map, map_counit_of_mem_wittHom x.2, map_zero, map_zero]

variable (R p A T) in

noncomputable def evalMonoidHom :
    WithConv (A →ₐ[R] T) →* Multiplicative (DieudonneModule R p A →+ UnipotentWittCovector p T) where
  toFun f := Multiplicative.ofAdd (eval R p f.ofConv)
  map_one' := by
    rw [← ofAdd_zero]
    exact congrArg _ (AddMonoidHom.ext fun z => eval_convOne z)
  map_mul' f g := by
    rw [← ofAdd_add]
    exact congrArg _ (AddMonoidHom.ext fun z => eval_convMul f g z)

/--
@isnad1 id=eq.0h5v.s11.da95c5bb738e from=translated src=- shape=2d35d1a4 vocab=0ea0571b
-/
@[simp] theorem evalMonoidHom_apply (f : WithConv (A →ₐ[R] T)) :
    evalMonoidHom R p A T f = Multiplicative.ofAdd (eval R p f.ofConv) := rfl

/--
@isnad1 id=eq.0h6v.s10.bc03c496d2a2 from=translated src=- shape=549c0689 vocab=658e621b
-/
theorem eval_verschiebung (f : A →ₐ[R] T) (z : DieudonneModule R p A) :
    eval R p f (verschiebung R p A z) = UnipotentWittCovector.verschiebung p T (eval R p f z) := by
  rw [eval_apply, eval_apply, toCovector_verschiebung, UnipotentWittCovector.map_verschiebung]

/--
@isnad1 id=eq.0h6v.s10.a2f5ce45a8ff from=translated src=- shape=12983928 vocab=21d40f32
-/
theorem eval_frobenius [CharP R p] (f : A →ₐ[R] T) (z : DieudonneModule R p A) :
    eval R p f (frobenius R p A z) = UnipotentWittCovector.frobenius R p T (eval R p f z) := by
  rw [eval_apply, eval_apply, toCovector_frobenius, UnipotentWittCovector.map_frobenius R R]

/--
@isnad1 id=eq.0h7v.s8.9f7ff80ec9d6 from=translated src=- shape=59b3d4b5 vocab=e4922ad7
-/
theorem map_comp_eval {T' : Type u'} [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T') (f : A →ₐ[R] T) :
    (UnipotentWittCovector.map p g.toRingHom).comp (eval R p f) = eval R p (g.comp f) := by
  refine AddMonoidHom.ext fun z => ?_
  rw [AddMonoidHom.comp_apply, eval_apply, eval_apply, UnipotentWittCovector.map_map]
  rfl

/--
@isnad1 id=eq.0h8v.s9.d7ae77329914 from=translated src=- shape=ca748ded vocab=93d46352
-/
theorem map_eval {T' : Type u'} [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T') (f : A →ₐ[R] T)
    (z : DieudonneModule R p A) :
    UnipotentWittCovector.map p g.toRingHom (eval R p f z) = eval R p (g.comp f) z :=
  DFunLike.congr_fun (map_comp_eval g f) z

/--
@isnad1 id=eq.0h8v.s9.50072daf4819 from=translated src=- shape=25364c5a vocab=eee8f441
-/
theorem map_eval_ringHom {T' : Type u'} [CommRing T'] (g : T →+* T') (f : A →ₐ[R] T)
    (z : DieudonneModule R p A) :
    UnipotentWittCovector.map p g (eval R p f z) =
      UnipotentWittCovector.map p (g.comp f.toRingHom) (toCovector R p A z) := by
  rw [eval_apply, UnipotentWittCovector.map_map]

/--
@isnad1 id=eq.0h8v.s10.15dd83fd5d89 from=translated src=- shape=5692eaca vocab=3f812a3d
-/
theorem eval_comp_bialgHom {B : Type u'} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (f : B →ₐ[R] T) (z : DieudonneModule R p A) :
    eval R p (f.comp (φ : A →ₐ[R] B)) z = eval R p f (map R p φ z) := by
  rw [eval_apply, eval_apply, toCovector_map, UnipotentWittCovector.map_map]
  rfl

/--
@isnad1 id=mem.2h11v.s9.fc6edf9ee452 from=translated src=- shape=c0cce6af vocab=09b7349f
-/
theorem eval_mem_wKer_of_mem_fontaineHodge {ℛ : Type u'} [CommRing ℛ] {ℛ' : Type v'} [CommRing ℛ']
    (π : ℛ →+* A) (π' : ℛ' →+* T) (F : ℛ →+* ℛ') (f : A →ₐ[R] T)
    (hcomm : π'.comp F = f.toRingHom.comp π) {z : DieudonneModule R p A}
    (hz : z ∈ fontaineHodge R p π) : eval R p f z ∈ UnipotentWittCovector.wKer p π' :=
  UnipotentWittCovector.map_mem_wKer F f.toRingHom π' hcomm
    (toCovector_mem_wKer_of_mem_fontaineHodge hz)

end Eval

end DieudonneModule

namespace UnipotentWittCovector.Examples

variable (p : ℕ) [hp : Fact p.Prime] (S : Type v) [CommRing S]

noncomputable def one : UnipotentWittCovector p S :=
  of p S 1 (TruncatedWittVector.mk p fun _ : Fin 1 => (1 : S))

/--
@isnad1 id=ne.0h2v.s6.586116707f29 from=translated src=- shape=ad307b7d vocab=279d57da
-/
theorem of_one_ne_zero [Nontrivial S] : one p S ≠ 0 := by
  intro h
  have h1 := of_injective (p := p) (S := S) 1 (h.trans (map_zero _).symm)
  have h2 := congrArg (TruncatedWittVector.coeff (0 : Fin 1)) h1
  rw [TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_zero] at h2
  exact one_ne_zero h2

/--
@isnad1 id=eq.0h2v.s7.2c40e7f4aab0 from=translated src=- shape=ec762cfa vocab=301e7678
-/
theorem verschiebung_one : verschiebung p S (one p S) = 0 :=
  (verschiebung_eq_zero_iff _).2 ⟨_, rfl⟩

/--
@isnad1 id=ne.0h2v.s12.3a7d601bf8f2 from=translated src=- shape=40ac344b vocab=91b5daab
-/
theorem eval_coordinate_ne_zero (R : Type u) [CommRing R] [Nontrivial R] :
    DieudonneModule.eval R p (AlgHom.id R (DieudonneModule.Examples.Ga R))
      (DieudonneModule.of R p (DieudonneModule.Examples.Ga R) 1
        ⟨TruncatedWittVector.mk p (fun _ : Fin 1 => DieudonneModule.Examples.coordinate R),
          DieudonneModule.Examples.coordinate_mem_wittHom R p⟩) ≠ 0 := by
  rw [DieudonneModule.eval_id]
  intro h
  exact DieudonneModule.Examples.of_coordinate_ne_zero R p (DieudonneModule.toCovector_injective
    (h.trans (map_zero _).symm))

end UnipotentWittCovector.Examples

end Deformation
