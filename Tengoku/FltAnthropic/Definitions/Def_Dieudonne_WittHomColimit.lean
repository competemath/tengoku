import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

noncomputable def verschiebungIter (k : ℕ) : WittVector p R →+ WittVector p R where
  toFun x := (WittVector.verschiebung (p := p) (R := R))^[k] x
  map_zero' := iterate_map_zero _ _
  map_add' := iterate_map_add _ _

/--
@isnad1 id=eq.0h4v.s8.88c1f7f36ab6 from=translated src=- shape=4b0bd389 vocab=e4dd2ad8
-/
@[simp] theorem verschiebungIter_apply (k : ℕ) (x : WittVector p R) :
    verschiebungIter k x = (WittVector.verschiebung (p := p) (R := R))^[k] x := rfl

noncomputable def shiftLE (h : n ≤ m) :
    TruncatedWittVector p n R →+ TruncatedWittVector p m R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate m).toAddMonoidHom.comp (verschiebungIter (m - n)),
      fun x hx => by
        change (WittVector.truncate n) x = 0 at hx
        rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
        change (WittVector.truncate m) ((WittVector.verschiebung (p := p) (R := R))^[m - n] x) = 0
        ext ⟨i, hi⟩
        simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
        by_cases him : i < m - n
        · exact WittVector.iterate_verschiebung_coeff_eq_zero x him
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + (m - n) := ⟨i - (m - n), by omega⟩
          rw [WittVector.iterate_verschiebung_coeff]
          exact hx k (by omega)⟩

/--
@isnad1 id=eq.1h5v.s9.ebbb09ec7c33 from=translated src=- shape=655af660 vocab=ea568ac6
-/
@[simp] theorem shiftLE_truncate (h : n ≤ m) (x : WittVector p R) :
    shiftLE h (WittVector.truncate n x) =
      WittVector.truncate m ((WittVector.verschiebung (p := p) (R := R))^[m - n] x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _
    (fun x => TruncatedWittVector.truncateFun_out x) _ _

/--
@isnad1 id=eq.1h6v.s8.d2ff0658709e from=translated src=- shape=06e73c62 vocab=734abb0f
-/
theorem coeff_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin m) :
    (shiftLE h x).coeff i =
      if hi : m - n ≤ (i : ℕ) then x.coeff ⟨i - (m - n), by omega⟩ else 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, WittVector.coeff_truncate]
  split_ifs with hi
  · rw [WittVector.coeff_truncate]
    have hk : (i : ℕ) = (i - (m - n)) + (m - n) := by omega
    conv_lhs => rw [hk]
    exact WittVector.iterate_verschiebung_coeff x (m - n) _
  · exact WittVector.iterate_verschiebung_coeff_eq_zero x (by omega)

/--
@isnad1 id=eq.2h6v.s7.d9c26a3a5e74 from=translated src=- shape=2fa827cf vocab=7583be0d
-/
theorem coeff_shiftLE_of_lt (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin m)
    (hi : (i : ℕ) < m - n) : (shiftLE h x).coeff i = 0 := by
  rw [coeff_shiftLE, dite_eq_right (by omega)]

/--
@isnad1 id=eq.1h6v.s7.47b1fc01f9a2 from=translated src=- shape=4c09b83f vocab=b260706d
-/
theorem coeff_shiftLE_add (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin n) :
    (shiftLE h x).coeff ⟨i + (m - n), by omega⟩ = x.coeff i := by
  rw [coeff_shiftLE, dite_eq_left (by simp)]
  congr 1
  ext
  simp

/--
@isnad1 id=eq.0h4v.s7.e0fc4d0afb6b from=translated src=- shape=4ac0ffa2 vocab=ed91ad2f
-/
@[simp] theorem shiftLE_refl (x : TruncatedWittVector p n R) : shiftLE le_rfl x = x :=
  TruncatedWittVector.ext fun i => by
    rw [coeff_shiftLE, dite_eq_left (by simp)]
    congr 1
    exact Fin.ext (by simp)

/--
@isnad1 id=eq.2h6v.s9.7da410a0e2cf from=translated src=- shape=a32313aa vocab=5523aabc
-/
theorem shiftLE_shiftLE (h₁ : n ≤ m) (h₂ : m ≤ l) (x : TruncatedWittVector p n R) :
    shiftLE h₂ (shiftLE h₁ x) = shiftLE (h₁.trans h₂) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, shiftLE_truncate, shiftLE_truncate, ← Function.iterate_add_apply]
  congr 2
  omega

/--
@isnad1 id=eq.0h4v.s9.2b5ff6a9d6a7 from=translated src=- shape=7e6d49d4 vocab=64c04702
-/
theorem shiftLE_succ (x : TruncatedWittVector p n R) :
    shiftLE (Nat.le_succ n) x = shift x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, shift_truncate, Nat.succ_sub (le_refl n), Nat.sub_self,
    Function.iterate_one]

/--
@isnad1 id=injectiv.1h4v.s7.ff27307b36d8 from=translated src=- shape=8668d430 vocab=42d0d546
-/
theorem shiftLE_injective (h : n ≤ m) : Injective (shiftLE (p := p) (R := R) h) :=
  fun x y hxy => TruncatedWittVector.ext fun i => by
    rw [← coeff_shiftLE_add h x i, ← coeff_shiftLE_add h y i, hxy]

/--
@isnad1 id=eq.1h7v.s9.b90ee30099d0 from=translated src=- shape=de97cfd5 vocab=6ed7412f
-/
theorem map_shiftLE (f : R →+* S) (h : n ≤ m) (x : TruncatedWittVector p n R) :
    map f (shiftLE h x) = shiftLE h (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, coeff_shiftLE]
    split_ifs
    · rfl
    · exact map_zero f

/--
@isnad1 id=eq.1h5v.s8.44833f803526 from=translated src=- shape=6d1cc757 vocab=0e8d2720
-/
theorem frobeniusFun_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n R) :
    frobeniusFun (shiftLE h x) = shiftLE h (frobeniusFun x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, coeff_shiftLE]
    split_ifs
    · rfl
    · exact zero_pow hp.out.ne_zero

/--
@isnad1 id=eq.1h5v.s9.6017e6382c2c from=translated src=- shape=5c3e0235 vocab=43519856
-/
theorem verschiebung_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n R) :
    verschiebung (shiftLE h x) = shiftLE h (verschiebung x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, verschiebung_truncate, verschiebung_truncate, shiftLE_truncate,
    ← Function.iterate_succ_apply' (f := WittVector.verschiebung),
    Function.iterate_succ_apply (f := WittVector.verschiebung)]

/--
@isnad1 id=eq.0h4v.s7.7badae56a543 from=translated src=- shape=369b50a6 vocab=95c3e226
-/
theorem verschiebung_iterate_eq_zero (x : TruncatedWittVector p n R) :
    (verschiebung (p := p) (R := R))^[n] x = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  have key : ∀ k : ℕ, (verschiebung (p := p) (n := n) (R := R))^[k] (WittVector.truncate n x) =
      WittVector.truncate n ((WittVector.verschiebung (p := p) (R := R))^[k] x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, verschiebung_truncate,
        ← Function.iterate_succ_apply' (f := WittVector.verschiebung)]
  rw [key]
  ext ⟨i, hi⟩
  rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
  exact WittVector.iterate_verschiebung_coeff_eq_zero x hi

/--
@isnad1 id=eq.1h4v.s6.8d9d4308bfbd from=translated src=- shape=c59ef7b8 vocab=b3a03d6d
-/
theorem pow_card_nsmul_eq_zero (hR : (p : R) = 0) (x : TruncatedWittVector p n R) :
    p ^ n • x = 0 := by
  rcases subsingleton_or_charP hR with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, mul_comm,
      ← WittVector.iterate_verschiebung_iterate_frobenius]
    ext ⟨i, hi⟩
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
    exact WittVector.iterate_verschiebung_coeff_eq_zero _ hi

end TruncWitt

section WittHom

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra R A]

open TruncWitt

/--
@isnad1 id=mem.2h6v.s8.76df22971f93 from=translated src=- shape=37daf8f2 vocab=281f01d5
-/
theorem shiftLE_mem_wittHom (h : n ≤ m) {x : TruncatedWittVector p n A}
    (hx : x ∈ wittHom R p n A) : TruncWitt.shiftLE h x ∈ wittHom R p m A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shiftLE, map_shiftLE, map_shiftLE, hx, map_add]

/--
@isnad1 id=iff.1h6v.s8.b5ca23654dea from=translated src=- shape=a3c60887 vocab=281f01d5
-/
theorem shiftLE_mem_wittHom_iff (h : n ≤ m) (x : TruncatedWittVector p n A) :
    TruncWitt.shiftLE h x ∈ wittHom R p m A ↔ x ∈ wittHom R p n A := by
  refine ⟨fun hx => ?_, shiftLE_mem_wittHom h⟩
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shiftLE, map_shiftLE, map_shiftLE, ← map_add] at hx
  exact shiftLE_injective h hx

variable (R p A) in

noncomputable def wittHomShiftLE (h : n ≤ m) : wittHom R p n A →+ wittHom R p m A where
  toFun x := ⟨TruncWitt.shiftLE h x, shiftLE_mem_wittHom h x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/--
@isnad1 id=eq.1h6v.s11.812fd7fc9d9c from=translated src=- shape=7819a5b5 vocab=506b2bca
-/
@[simp] theorem coe_wittHomShiftLE (h : n ≤ m) (x : wittHom R p n A) :
    (wittHomShiftLE R p A h x : TruncatedWittVector p m A) = TruncWitt.shiftLE h x := rfl

/--
@isnad1 id=eq.0h5v.s11.1bd3ffdd90f9 from=translated src=- shape=1536fa98 vocab=5e4e4e83
-/
@[simp] theorem wittHomShiftLE_refl (x : wittHom R p n A) : wittHomShiftLE R p A le_rfl x = x :=
  Subtype.ext (shiftLE_refl _)

/--
@isnad1 id=eq.2h7v.s13.a5088b1c6d15 from=translated src=- shape=39ea285e vocab=0032a220
-/
theorem wittHomShiftLE_shiftLE (h₁ : n ≤ m) (h₂ : m ≤ l) (x : wittHom R p n A) :
    wittHomShiftLE R p A h₂ (wittHomShiftLE R p A h₁ x) = wittHomShiftLE R p A (h₁.trans h₂) x :=
  Subtype.ext (shiftLE_shiftLE h₁ h₂ _)

/--
@isnad1 id=eq.0h5v.s13.2b6257ff2554 from=translated src=- shape=4939ff70 vocab=f67fcaa7
-/
theorem wittHomShiftLE_succ (x : wittHom R p n A) :
    wittHomShiftLE R p A (Nat.le_succ n) x = wittHomShift R p n A x :=
  Subtype.ext (shiftLE_succ _)

/--
@isnad1 id=injectiv.1h5v.s11.2c4492024cd6 from=translated src=- shape=bde91f0f vocab=107d2a7d
-/
theorem wittHomShiftLE_injective (h : n ≤ m) : Injective (wittHomShiftLE R p A h) :=
  fun _ _ hxy => Subtype.ext (shiftLE_injective h (congrArg Subtype.val hxy))

/--
@isnad1 id=eq.1h6v.s13.a286d10a2a9a from=translated src=- shape=b492d883 vocab=067c8cc4
-/
theorem wittHomShiftLE_verschiebung (h : n ≤ m) (x : wittHom R p n A) :
    wittHomShiftLE R p A h (wittHomVerschiebung R p n A x) =
      wittHomVerschiebung R p m A (wittHomShiftLE R p A h x) :=
  Subtype.ext (verschiebung_shiftLE h _).symm

/--
@isnad1 id=eq.1h6v.s13.0693b4f246dc from=translated src=- shape=57d85a88 vocab=029526c6
-/
theorem wittHomShiftLE_frobenius [CharP R p] (h : n ≤ m) (x : wittHom R p n A) :
    wittHomShiftLE R p A h (wittHomFrobenius R p n A x) =
      wittHomFrobenius R p m A (wittHomShiftLE R p A h x) :=
  Subtype.ext (frobeniusFun_shiftLE h _).symm

/--
@isnad1 id=eq.1h8v.s13.09bf64fc5cbe from=translated src=- shape=16e88784 vocab=248db9ee
-/
theorem wittHomMap_shiftLE {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (h : n ≤ m) (x : wittHom R p n A) :
    wittHomMap p m φ (wittHomShiftLE R p A h x) = wittHomShiftLE R p B h (wittHomMap p n φ x) :=
  Subtype.ext (map_shiftLE _ h _)

/--
@isnad1 id=eq.0h5v.s11.989a2a3e95af from=translated src=- shape=34055443 vocab=7bbac4b4
-/
theorem wittHomVerschiebung_iterate_eq_zero (x : wittHom R p n A) :
    (wittHomVerschiebung R p n A)^[n] x = 0 := by
  apply Subtype.ext
  have : ∀ k : ℕ, (((wittHomVerschiebung R p n A)^[k] x : wittHom R p n A) :
      TruncatedWittVector p n A) = (TruncWitt.verschiebung (p := p) (R := A))^[k] x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
  rw [this]
  exact verschiebung_iterate_eq_zero _

/--
@isnad1 id=eq.0h5v.s9.57930fcd27be from=translated src=- shape=ca9ef5d1 vocab=0058f430
-/
theorem pow_nsmul_wittHom_eq_zero [CharP R p] (x : wittHom R p n A) : p ^ n • x = 0 :=
  Subtype.ext (by
    rw [AddSubgroupClass.coe_nsmul, ZeroMemClass.coe_zero]
    exact pow_card_nsmul_eq_zero (natCast_eq_zero_of_algebra R p A) _)

/--
@isnad1 id=directed.0h3v.s11.50429e730608 from=translated src=- shape=c8124135 vocab=adb90a6d
-/
instance wittHomShiftLE_directedSystem :
    DirectedSystem (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h where
  map_self _ x := wittHomShiftLE_refl x
  map_map _ _ _ h₁ h₂ x := wittHomShiftLE_shiftLE h₁ h₂ x

end WittHom

section Colimit

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra R A]

def DieudonneModule : Type v :=
  AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h

namespace DieudonneModule

noncomputable instance instAddCommGroup : AddCommGroup (DieudonneModule R p A) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h))

noncomputable instance instInhabited : Inhabited (DieudonneModule R p A) := ⟨0⟩

noncomputable def of (n : ℕ) : wittHom R p n A →+ DieudonneModule R p A :=
  AddCommGroup.DirectLimit.of (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h) n

variable {R p A}
variable {n m : ℕ}

/--
@isnad1 id=eq.1h6v.s12.02f5891a5a30 from=translated src=- shape=826cf821 vocab=19866d34
-/
@[simp] theorem of_shiftLE (h : n ≤ m) (x : wittHom R p n A) :
    of R p A m (wittHomShiftLE R p A h x) = of R p A n x :=
  AddCommGroup.DirectLimit.of_f _ _

/--
@isnad1 id=eq.0h5v.s13.f5d4d047b644 from=translated src=- shape=e494f9d9 vocab=626cc120
-/
@[simp] theorem of_shift (x : wittHom R p n A) :
    of R p A (n + 1) (wittHomShift R p n A x) = of R p A n x := by
  rw [← wittHomShiftLE_succ, of_shiftLE]

/--
@isnad1 id=var.0h6v.s10.52c1c306f133 from=translated src=- shape=a051152e vocab=eab9ca0d
-/
@[elab_as_elim]
protected theorem induction_on {C : DieudonneModule R p A → Prop} (z : DieudonneModule R p A)
    (ih : ∀ (n : ℕ) (x : wittHom R p n A), C (of R p A n x)) : C z :=
  AddCommGroup.DirectLimit.induction_on z ih

/--
@isnad1 id=ex.0h4v.s10.48b86bad3922 from=translated src=- shape=3e5e31b1 vocab=eab9ca0d
-/
theorem exists_of (z : DieudonneModule R p A) : ∃ (n : ℕ) (x : wittHom R p n A), of R p A n x = z :=
  DieudonneModule.induction_on z fun n x => ⟨n, x, rfl⟩

/--
@isnad1 id=ex.1h5v.s12.72c987d561a5 from=translated src=- shape=4ed23ebf vocab=19866d34
-/
theorem exists_shiftLE_eq_zero_of_of_eq_zero {x : wittHom R p n A} (hx : of R p A n x = 0) :
    ∃ (m : ℕ) (h : n ≤ m), wittHomShiftLE R p A h x = 0 :=
  AddCommGroup.DirectLimit.of.zero_exact (f := fun _ _ h => wittHomShiftLE R p A h) n x hx

/--
@isnad1 id=injectiv.0h4v.s10.cf81c740f883 from=translated src=- shape=87e0c342 vocab=8797c947
-/
theorem of_injective (n : ℕ) : Injective (of R p A n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨m, h, hm⟩ := exists_shiftLE_eq_zero_of_of_eq_zero hx
  exact wittHomShiftLE_injective h (by rw [hm, map_zero])

/--
@isnad1 id=iff.0h7v.s13.51c362bb6ec2 from=translated src=- shape=fd4c2edf vocab=218bd7ba
-/
theorem of_eq_of_iff (x : wittHom R p n A) (y : wittHom R p m A) :
    of R p A n x = of R p A m y ↔
      wittHomShiftLE R p A (le_max_left n m) x = wittHomShiftLE R p A (le_max_right n m) y := by
  constructor
  · intro h
    apply of_injective (max n m)
    rwa [of_shiftLE, of_shiftLE]
  · intro h
    rw [← of_shiftLE (le_max_left n m) x, h, of_shiftLE]

section Lift

variable {P : Type w} [AddCommGroup P]

/--
@isnad1 id=eq.2h8v.s14.24b5b4bf71f8 from=translated src=- shape=dfd2f5a2 vocab=3a704aa9
-/
theorem compat_shiftLE (g : ∀ n, wittHom R p n A →+ P)
    (hg : ∀ (n : ℕ) (x : wittHom R p n A), g (n + 1) (wittHomShift R p n A x) = g n x)
    (h : n ≤ m) (x : wittHom R p n A) : g m (wittHomShiftLE R p A h x) = g n x := by
  induction h with
  | refl => rw [wittHomShiftLE_refl]
  | @step m h ih =>
    rw [← wittHomShiftLE_shiftLE h (Nat.le_succ m), wittHomShiftLE_succ, hg, ih]

variable (R p A) in

noncomputable def lift (g : ∀ n, wittHom R p n A →+ P)
    (hg : ∀ (n : ℕ) (x : wittHom R p n A), g (n + 1) (wittHomShift R p n A x) = g n x) :
    DieudonneModule R p A →+ P :=
  AddCommGroup.DirectLimit.lift (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h)
    P g fun _ _ h x => compat_shiftLE g hg h x

/--
@isnad1 id=eq.1h7v.s13.4cc0549c2146 from=translated src=- shape=e755717f vocab=b5bae2d5
-/
@[simp] theorem lift_of (g : ∀ n, wittHom R p n A →+ P)
    (hg : ∀ (n : ℕ) (x : wittHom R p n A), g (n + 1) (wittHomShift R p n A x) = g n x)
    (x : wittHom R p n A) : lift R p A g hg (of R p A n x) = g n x :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

/--
@isnad1 id=eq.1h6v.s11.cc03c6c6cc3a from=translated src=- shape=046a5db5 vocab=4d90c025
-/
theorem hom_ext {f g : DieudonneModule R p A →+ P}
    (h : ∀ (n : ℕ) (x : wittHom R p n A), f (of R p A n x) = g (of R p A n x)) : f = g :=
  AddMonoidHom.ext fun z => DieudonneModule.induction_on z h

end Lift

variable (R p A) in

noncomputable def verschiebung : DieudonneModule R p A →+ DieudonneModule R p A :=
  lift R p A (fun n => (of R p A n).comp (wittHomVerschiebung R p n A)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← wittHomShift_verschiebung, of_shift]

/--
@isnad1 id=eq.0h5v.s12.f14ae103f6f2 from=translated src=- shape=11af46e2 vocab=f8c41b78
-/
@[simp] theorem verschiebung_of (x : wittHom R p n A) :
    verschiebung R p A (of R p A n x) = of R p A n (wittHomVerschiebung R p n A x) :=
  lift_of _ _ _

section CharP

variable [CharP R p]

variable (R p A) in

noncomputable def frobenius : DieudonneModule R p A →+ DieudonneModule R p A :=
  lift R p A (fun n => (of R p A n).comp (wittHomFrobenius R p n A)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← wittHomShift_frobenius, of_shift]

/--
@isnad1 id=eq.0h5v.s12.028f07e2f0ce from=translated src=- shape=cfa6800c vocab=c6f318d5
-/
@[simp] theorem frobenius_of (x : wittHom R p n A) :
    frobenius R p A (of R p A n x) = of R p A n (wittHomFrobenius R p n A x) :=
  lift_of _ _ _

/--
@isnad1 id=eq.0h4v.s9.3af60fe5bde1 from=translated src=- shape=521cc4d3 vocab=431cf2d0
-/
theorem frobenius_verschiebung (z : DieudonneModule R p A) :
    frobenius R p A (verschiebung R p A z) = (p : ℤ) • z := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [verschiebung_of, frobenius_of, wittHomFrobenius_verschiebung, map_zsmul]

/--
@isnad1 id=eq.0h4v.s9.ed938bd20d68 from=translated src=- shape=521cc4d3 vocab=431cf2d0
-/
theorem verschiebung_frobenius (z : DieudonneModule R p A) :
    verschiebung R p A (frobenius R p A z) = (p : ℤ) • z := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [frobenius_of, verschiebung_of, wittHomVerschiebung_frobenius, map_zsmul]

variable (R p A) in

noncomputable def dieudonneDatum : DieudonneDatum (p : ℤ) (DieudonneModule R p A) where
  F := (frobenius R p A).toIntLinearMap
  V := (verschiebung R p A).toIntLinearMap
  fv := LinearMap.ext fun z => frobenius_verschiebung z
  vf := LinearMap.ext fun z => verschiebung_frobenius z

/--
@isnad1 id=eq.0h4v.s9.1040efd057aa from=translated src=- shape=42a276d4 vocab=2b28038f
-/
@[simp] theorem dieudonneDatum_F_apply (z : DieudonneModule R p A) :
    (dieudonneDatum R p A).F z = frobenius R p A z := rfl

/--
@isnad1 id=eq.0h4v.s9.dcdb7e2f82a7 from=translated src=- shape=42a276d4 vocab=e616462a
-/
@[simp] theorem dieudonneDatum_V_apply (z : DieudonneModule R p A) :
    (dieudonneDatum R p A).V z = verschiebung R p A z := rfl

/--
@isnad1 id=eq.0h5v.s10.d83c356184ae from=translated src=- shape=e4f697a0 vocab=cb288442
-/
theorem pow_nsmul_of (x : wittHom R p n A) : p ^ n • of R p A n x = 0 := by
  rw [← map_nsmul, pow_nsmul_wittHom_eq_zero, map_zero]

/--
@isnad1 id=ex.0h4v.s7.cac262062d99 from=translated src=- shape=2fcb13fa vocab=f80c1ba3
-/
theorem exists_pow_nsmul_eq_zero (z : DieudonneModule R p A) : ∃ n : ℕ, p ^ n • z = 0 := by
  obtain ⟨n, x, rfl⟩ := exists_of z
  exact ⟨n, pow_nsmul_of x⟩

end CharP

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

variable (R p) in

noncomputable def map (φ : A →ₐc[R] B) : DieudonneModule R p A →+ DieudonneModule R p B :=
  lift R p A (fun n => (of R p B n).comp (wittHomMap p n φ)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, wittHomMap_shift, of_shift]

/--
@isnad1 id=eq.0h7v.s12.10eb93d20100 from=translated src=- shape=b4119e02 vocab=77e47fec
-/
@[simp] theorem map_of (φ : A →ₐc[R] B) (x : wittHom R p n A) :
    map R p φ (of R p A n x) = of R p B n (wittHomMap p n φ x) :=
  lift_of _ _ _

/--
@isnad1 id=eq.0h6v.s10.c2c19e1aac6a from=translated src=- shape=1c2e63a1 vocab=d9ddfc7e
-/
theorem map_verschiebung (φ : A →ₐc[R] B) (z : DieudonneModule R p A) :
    map R p φ (verschiebung R p A z) = verschiebung R p B (map R p φ z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [verschiebung_of, map_of, map_of, verschiebung_of, wittHomMap_verschiebung]

/--
@isnad1 id=eq.0h6v.s10.7faf59fa67de from=translated src=- shape=33dfc663 vocab=f29c17dd
-/
theorem map_frobenius [CharP R p] (φ : A →ₐc[R] B) (z : DieudonneModule R p A) :
    map R p φ (frobenius R p A z) = frobenius R p B (map R p φ z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [frobenius_of, map_of, map_of, frobenius_of, wittHomMap_frobenius]

/--
@isnad1 id=eq.0h4v.s8.463dea238352 from=translated src=- shape=275653fb vocab=40b5a101
-/
theorem map_id (z : DieudonneModule R p A) : map R p (BialgHom.id R A) z = z := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of]
    congr 1
    exact Subtype.ext (TruncWitt.map_id _)

/--
@isnad1 id=eq.0h8v.s10.d29c88f049d1 from=translated src=- shape=e0334f61 vocab=342e68d6
-/
theorem map_comp {C : Type*} [CommRing C] [Bialgebra R C] (φ : A →ₐc[R] B) (ψ : B →ₐc[R] C)
    (z : DieudonneModule R p A) : map R p (ψ.comp φ) z = map R p ψ (map R p φ z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of, map_of, map_of]
    congr 1
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    simp only [coe_wittHomMap, TruncWitt.coeff_map]
    rfl

/--
@isnad1 id=injectiv.1h5v.s9.a428078dc1a3 from=translated src=- shape=2a3671d2 vocab=4a5d5260
-/
theorem map_injective {φ : A →ₐc[R] B} (hφ : Injective φ) : Injective (map R p φ) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [map_of] at hz
  have hx : wittHomMap p n φ x = 0 := of_injective n (by rw [hz, map_zero])
  rw [wittHomMap_injective hφ (hx.trans (map_zero _).symm), map_zero]

end Map

end DieudonneModule

end Colimit

namespace DieudonneModule.Examples

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev Ga : Type u := SymmetricAlgebra R R

noncomputable def coordinate : Ga R := SymmetricAlgebra.ι R R 1

/--
@isnad1 id=ne.0h1v.s7.d43083de5c2e from=translated src=- shape=37fa0090 vocab=58b4bc01
-/
theorem coordinate_ne_zero [Nontrivial R] : coordinate R ≠ 0 := by
  intro h
  have := congrArg (SymmetricAlgebra.lift (LinearMap.id : R →ₗ[R] R)) h
  rw [coordinate, SymmetricAlgebra.lift_ι_apply, map_zero, LinearMap.id_apply] at this
  exact one_ne_zero this

/--
@isnad1 id=eq.0h4v.s7.31bac3c04915 from=translated src=- shape=c25f7f92 vocab=048cfc75
-/
theorem coeff_zero_add_of_length_one {S : Type v} [CommRing S] (x y : TruncatedWittVector p 1 S) :
    (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p 1 S x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p 1 S y
  rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.add_coeff_zero x y

/--
@isnad1 id=mem.0h2v.s8.13f1c98ab6b4 from=translated src=- shape=1ba07a2b vocab=d29bfeb4
-/
theorem coordinate_mem_wittHom :
    TruncatedWittVector.mk p (fun _ : Fin 1 => coordinate R) ∈ wittHom R p 1 (Ga R) := by
  rw [mem_wittHom_iff]
  refine TruncatedWittVector.ext fun i => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [coeff_zero_add_of_length_one, TruncWitt.coeff_map, TruncWitt.coeff_map,
    TruncWitt.coeff_map, TruncatedWittVector.coeff_mk]
  change Coalgebra.comul (R := R) (coordinate R) = _
  rw [coordinate, SymmetricAlgebra.comul_ι]
  rfl

/--
@isnad1 id=ne.0h2v.s12.a0433a7d516b from=translated src=- shape=2b42df5a vocab=79f5eddb
-/
theorem of_coordinate_ne_zero [Nontrivial R] :
    DieudonneModule.of R p (Ga R) 1
      ⟨TruncatedWittVector.mk p (fun _ : Fin 1 => coordinate R), coordinate_mem_wittHom R p⟩ ≠ 0 := by
  intro h
  have h1 := DieudonneModule.of_injective 1 (h.trans (map_zero _).symm)
  have h2 := congrArg (fun x : wittHom R p 1 (Ga R) => (x : TruncatedWittVector p 1 (Ga R)).coeff 0) h1
  simp only [TruncatedWittVector.coeff_mk, AddSubgroup.coe_zero,
    TruncatedWittVector.coeff_zero] at h2
  exact coordinate_ne_zero R h2

end DieudonneModule.Examples

end Deformation
