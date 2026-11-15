import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

noncomputable def map (f : R →+* S) : TruncatedWittVector p n R →+* TruncatedWittVector p n S :=
  RingHom.liftOfRightInverse (WittVector.truncate n) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate n).comp (WittVector.map f), fun x hx => by
      rw [WittVector.mem_ker_truncate] at hx
      simp only [RingHom.mem_ker, RingHom.comp_apply, TruncatedWittVector.ext_iff,
        WittVector.coeff_truncate, WittVector.map_coeff, TruncatedWittVector.coeff_zero]
      exact fun i => by rw [hx i i.isLt]; exact map_zero f⟩

/--
@isnad1 id=eq.0h6v.s8.35a989b16e55 from=translated src=- shape=d0dbe78a vocab=bb8e9f2d
-/
@[simp] theorem map_truncate (f : R →+* S) (x : WittVector p R) :
    map f (WittVector.truncate n x) = WittVector.truncate n (WittVector.map f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

/--
@isnad1 id=eq.0h7v.s7.f530b0d9eb45 from=translated src=- shape=d07507b9 vocab=01a7d7e6
-/
@[simp] theorem coeff_map (f : R →+* S) (x : TruncatedWittVector p n R) (i : Fin n) :
    (map f x).coeff i = f (x.coeff i) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [WittVector.coeff_truncate, WittVector.map_coeff]

/--
@isnad1 id=eq.0h8v.s8.9e5312a43553 from=translated src=- shape=7ac89059 vocab=8ec3427a
-/
theorem map_map (f : R →+* S) (g : S →+* T) (x : TruncatedWittVector p n R) :
    map g (map f x) = map (g.comp f) x :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, RingHom.comp_apply]

/--
@isnad1 id=eq.0h7v.s7.095444082e76 from=translated src=- shape=b3a8da2f vocab=ed2c9081
-/
theorem map_comp (f : R →+* S) (g : S →+* T) :
    (map (p := p) (n := n) g).comp (map f) = map (g.comp f) :=
  RingHom.ext fun x => map_map f g x

/--
@isnad1 id=eq.0h4v.s7.c2c98dd3b494 from=translated src=- shape=67d185c3 vocab=6afebcb7
-/
@[simp] theorem map_id (x : TruncatedWittVector p n R) : map (RingHom.id R) x = x :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, RingHom.id_apply]

/--
@isnad1 id=injectiv.1h5v.s7.227845b883f5 from=translated src=- shape=b1f47f2c vocab=82810a31
-/
theorem map_injective {f : R →+* S} (hf : Injective f) :
    Injective (map (p := p) (n := n) f) := fun x y h =>
  TruncatedWittVector.ext fun i => hf (by
    have := congrArg (TruncatedWittVector.coeff i) h
    simpa only [coeff_map] using this)

/--
@isnad1 id=eq.1h7v.s8.6dbd2ac12b4b from=translated src=- shape=bfb047f5 vocab=01a7d7e6
-/
theorem map_congr {f g : R →+* S} {x : TruncatedWittVector p n R}
    (h : ∀ i, f (x.coeff i) = g (x.coeff i)) : map f x = map g x :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, h i]

noncomputable def verschiebung : TruncatedWittVector p n R →+ TruncatedWittVector p n R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate n).toAddMonoidHom.comp WittVector.verschiebung, fun x hx => by
      change (WittVector.truncate n) x = 0 at hx
      rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
      change (WittVector.truncate n) (WittVector.verschiebung x) = 0
      ext ⟨i, hi⟩
      simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero x
      | succ j =>
        rw [WittVector.verschiebung_coeff_succ]
        exact hx j (Nat.lt_of_succ_lt hi)⟩

/--
@isnad1 id=eq.0h4v.s9.40b35a34a861 from=translated src=- shape=3205e12e vocab=9451709b
-/
@[simp] theorem verschiebung_truncate (x : WittVector p R) :
    verschiebung (WittVector.truncate n x) = WittVector.truncate n (WittVector.verschiebung x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _
    (fun x => TruncatedWittVector.truncateFun_out x) _ _

/--
@isnad1 id=eq.0h4v.s9.9fd6ec05d416 from=translated src=- shape=a5e4030e vocab=711e45eb
-/
theorem coeff_verschiebung_zero (x : TruncatedWittVector p (n + 1) R) :
    (verschiebung x).coeff 0 = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  rw [verschiebung_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_zero x

/--
@isnad1 id=eq.1h5v.s7.6890b6c373be from=translated src=- shape=f4af9037 vocab=d759f0ba
-/
theorem coeff_verschiebung_succ (x : TruncatedWittVector p n R) (i : ℕ) (hi : i + 1 < n) :
    (verschiebung x).coeff ⟨i + 1, hi⟩ = x.coeff ⟨i, Nat.lt_of_succ_lt hi⟩ := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [verschiebung_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_succ x i

/--
@isnad1 id=eq.0h6v.s9.60638457087d from=translated src=- shape=a83915b5 vocab=0c4af5bd
-/
theorem map_verschiebung (f : R →+* S) (x : TruncatedWittVector p n R) :
    map f (verschiebung x) = verschiebung (map f x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [verschiebung_truncate, map_truncate, map_truncate, verschiebung_truncate,
    WittVector.map_verschiebung]

def frobeniusFun (x : TruncatedWittVector p n R) : TruncatedWittVector p n R :=
  TruncatedWittVector.mk p fun i => x.coeff i ^ p

omit hp in
/--
@isnad1 id=eq.0h5v.s5.296a966387c4 from=translated src=- shape=04cf7880 vocab=cf8ce0e4
-/
@[simp] theorem coeff_frobeniusFun (x : TruncatedWittVector p n R) (i : Fin n) :
    (frobeniusFun x).coeff i = x.coeff i ^ p :=
  TruncatedWittVector.coeff_mk _ _

/--
@isnad1 id=eq.0h6v.s8.a57f9d11509a from=translated src=- shape=b427efed vocab=7163f787
-/
theorem map_frobeniusFun (f : R →+* S) (x : TruncatedWittVector p n R) :
    map f (frobeniusFun x) = frobeniusFun (map f x) :=
  TruncatedWittVector.ext fun i => by simp only [coeff_map, coeff_frobeniusFun, map_pow]

/--
@isnad1 id=eq.0h4v.s8.0c5ecc5bfc00 from=translated src=- shape=d37f7827 vocab=61e145ff
-/
theorem frobeniusFun_verschiebung (x : TruncatedWittVector p n R) :
    frobeniusFun (verschiebung x) = verschiebung (frobeniusFun x) := by
  refine TruncatedWittVector.ext fun ⟨i, hi⟩ => ?_
  cases n with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ m =>
    cases i with
    | zero =>
      change (frobeniusFun (verschiebung x)).coeff 0 = (verschiebung (frobeniusFun x)).coeff 0
      rw [coeff_frobeniusFun, coeff_verschiebung_zero, coeff_verschiebung_zero,
        zero_pow hp.out.ne_zero]
    | succ j =>
      rw [coeff_frobeniusFun, coeff_verschiebung_succ _ _ hi, coeff_verschiebung_succ _ _ hi,
        coeff_frobeniusFun]

/--
@isnad1 id=or.1h2v.s5.006b6aab421d from=translated src=- shape=97c84484 vocab=219901fa
-/
theorem subsingleton_or_charP (hR : (p : R) = 0) : Subsingleton R ∨ CharP R p := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact Or.inl h
  · refine Or.inr ((CharP.charP_iff_prime_eq_zero hp.out).2 hR)

/--
@isnad1 id=subsingl.0h3v.s3.afa85aa7ec95 from=translated src=- shape=cb8cfdb7 vocab=66a763ef
-/
instance instSubsingleton [Subsingleton R] : Subsingleton (TruncatedWittVector p n R) :=
  ⟨fun _ _ => TruncatedWittVector.ext fun _ => Subsingleton.elim _ _⟩

/--
@isnad1 id=eq.0h4v.s8.75ca7767e710 from=translated src=- shape=cddb8b2a vocab=d7bca927
-/
theorem frobeniusFun_truncate [CharP R p] (x : WittVector p R) :
    frobeniusFun (WittVector.truncate n x) = WittVector.truncate n (WittVector.frobenius x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, WittVector.coeff_truncate, WittVector.coeff_frobenius_charP]

/--
@isnad1 id=eq.1h5v.s6.bfe001230625 from=translated src=- shape=f60e5aac vocab=ffebf7c4
-/
theorem frobeniusFun_add (hR : (p : R) = 0) (x y : TruncatedWittVector p n R) :
    frobeniusFun (x + y) = frobeniusFun x + frobeniusFun y := by
  rcases subsingleton_or_charP hR with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
    obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n R y
    rw [← map_add, frobeniusFun_truncate, frobeniusFun_truncate, frobeniusFun_truncate,
      map_add, map_add]

/--
@isnad1 id=eq.0h3v.s5.bac38e8d70e6 from=translated src=- shape=04482f2b vocab=7d5a95eb
-/
theorem frobeniusFun_zero : frobeniusFun (0 : TruncatedWittVector p n R) = 0 :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, TruncatedWittVector.coeff_zero, zero_pow hp.out.ne_zero]

/--
@isnad1 id=eq.1h4v.s8.f66329cd52e9 from=translated src=- shape=ddaea7ca vocab=f6e2af2a
-/
theorem verschiebung_frobeniusFun (hR : (p : R) = 0) (x : TruncatedWittVector p n R) :
    verschiebung (frobeniusFun x) = (p : ℤ) • x := by
  rcases subsingleton_or_charP hR with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
    rw [frobeniusFun_truncate, verschiebung_truncate, WittVector.verschiebung_frobenius,
      ← nsmul_eq_mul', map_nsmul, natCast_zsmul]

/--
@isnad1 id=eq.1h4v.s8.fef7321b9612 from=translated src=- shape=b0bdd2f1 vocab=f6e2af2a
-/
theorem frobeniusFun_verschiebung_eq_smul (hR : (p : R) = 0) (x : TruncatedWittVector p n R) :
    frobeniusFun (verschiebung x) = (p : ℤ) • x := by
  rw [frobeniusFun_verschiebung, verschiebung_frobeniusFun hR]

noncomputable def shift : TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate (n + 1)).toAddMonoidHom.comp WittVector.verschiebung, fun x hx => by
      change (WittVector.truncate n) x = 0 at hx
      rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
      change (WittVector.truncate (n + 1)) (WittVector.verschiebung x) = 0
      ext ⟨i, hi⟩
      simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero x
      | succ j =>
        rw [WittVector.verschiebung_coeff_succ]
        exact hx j (Nat.lt_of_succ_lt_succ hi)⟩

/--
@isnad1 id=eq.0h4v.s9.3ee839234739 from=translated src=- shape=d771c796 vocab=991379b0
-/
@[simp] theorem shift_truncate (x : WittVector p R) :
    shift (WittVector.truncate n x) = WittVector.truncate (n + 1) (WittVector.verschiebung x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _
    (fun x => TruncatedWittVector.truncateFun_out x) _ _

/--
@isnad1 id=eq.0h4v.s8.daf1e8dca3d7 from=translated src=- shape=9b93015d vocab=34853578
-/
theorem coeff_shift_zero (x : TruncatedWittVector p n R) : (shift x).coeff 0 = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_zero x

/--
@isnad1 id=eq.0h5v.s8.3825b059a8d3 from=translated src=- shape=491e4581 vocab=c1361c58
-/
theorem coeff_shift_succ (x : TruncatedWittVector p n R) (i : Fin n) :
    (shift x).coeff i.succ = x.coeff i := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.verschiebung_coeff_succ x i

/--
@isnad1 id=injectiv.0h3v.s8.7786717fa19e from=translated src=- shape=c5da40dc vocab=3f364c54
-/
theorem shift_injective : Injective (shift (p := p) (n := n) (R := R)) := fun x y h =>
  TruncatedWittVector.ext fun i => by
    rw [← coeff_shift_succ x i, ← coeff_shift_succ y i, h]

/--
@isnad1 id=eq.0h6v.s10.d40943d87226 from=translated src=- shape=3adb9d9b vocab=15e68c3f
-/
theorem map_shift (f : R →+* S) (x : TruncatedWittVector p n R) :
    map f (shift x) = shift (map f x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, map_truncate, map_truncate, shift_truncate, WittVector.map_verschiebung]

/--
@isnad1 id=eq.0h4v.s9.3209b4173363 from=translated src=- shape=b8db7d02 vocab=666558a6
-/
theorem truncate_shift (x : TruncatedWittVector p n R) :
    TruncatedWittVector.truncate (Nat.le_succ n) (shift x) = verschiebung x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shift_truncate, TruncatedWittVector.truncate_wittVector_truncate, verschiebung_truncate]

/--
@isnad1 id=eq.0h4v.s10.defe08022952 from=translated src=- shape=0bb46924 vocab=666558a6
-/
theorem shift_truncate_succ (y : TruncatedWittVector p (n + 1) R) :
    shift (TruncatedWittVector.truncate (Nat.le_succ n) y) = verschiebung y := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 1) R y
  rw [TruncatedWittVector.truncate_wittVector_truncate, shift_truncate, verschiebung_truncate]

/--
@isnad1 id=eq.0h4v.s9.c091b9fe9e2d from=translated src=- shape=8408eb4e vocab=e6db4f33
-/
theorem frobeniusFun_shift (x : TruncatedWittVector p n R) :
    frobeniusFun (shift x) = shift (frobeniusFun x) := by
  refine TruncatedWittVector.ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [coeff_frobeniusFun, coeff_shift_zero, coeff_shift_zero, zero_pow hp.out.ne_zero]
  · rw [coeff_frobeniusFun, coeff_shift_succ, coeff_shift_succ, coeff_frobeniusFun]

/--
@isnad1 id=eq.1h7v.s9.3f015ff1b216 from=translated src=- shape=19d3dfa1 vocab=bdcbb8ee
-/
theorem map_truncateLE {m : ℕ} (hm : n ≤ m) (f : R →+* S) (x : TruncatedWittVector p m R) :
    map f (TruncatedWittVector.truncate hm x) = TruncatedWittVector.truncate hm (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, TruncatedWittVector.coeff_truncate]

/--
@isnad1 id=eq.1h5v.s9.2d0eeb5297f2 from=translated src=- shape=2f076306 vocab=655a9f8d
-/
theorem verschiebung_truncateLE {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m R) :
    verschiebung (TruncatedWittVector.truncate hm x) =
      TruncatedWittVector.truncate hm (verschiebung x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  rw [TruncatedWittVector.truncate_wittVector_truncate, verschiebung_truncate,
    verschiebung_truncate, TruncatedWittVector.truncate_wittVector_truncate]

/--
@isnad1 id=eq.1h5v.s8.999296b99724 from=translated src=- shape=e80bdadb vocab=63043871
-/
theorem frobeniusFun_truncateLE {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m R) :
    frobeniusFun (TruncatedWittVector.truncate hm x) =
      TruncatedWittVector.truncate hm (frobeniusFun x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, TruncatedWittVector.coeff_truncate]

end TruncWitt

section WittHom

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable (A : Type v) [CommRing A] [Bialgebra R A]

open TruncWitt

noncomputable abbrev comulRingHom : A →+* TensorProduct R A A :=
  (Bialgebra.comulAlgHom R A).toRingHom

noncomputable def wittHom : AddSubgroup (TruncatedWittVector p n A) where
  carrier := {x | map (comulRingHom R A) x =
    map (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom x +
    map (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom x}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
    rw [hx, hy]; abel
  neg_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, map_neg] at hx ⊢
    rw [hx]; abel

variable {R p n A}

/--
@isnad1 id=iff.0h5v.s12.856ffb885ed0 from=translated src=- shape=1c850c31 vocab=67b09a6e
-/
theorem mem_wittHom_iff (x : TruncatedWittVector p n A) :
    x ∈ wittHom R p n A ↔ map (comulRingHom R A) x =
      map (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom x +
      map (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom x :=
  Iff.rfl

/--
@isnad1 id=eq.1h8v.s9.657ac61c54af from=translated src=- shape=138c380d vocab=f9fe9759
-/
theorem map_convMul_of_mem_wittHom {T : Type w} [CommRing T] [Algebra R T]
    {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A)
    (f g : WithConv (A →ₐ[R] T)) :
    map (f * g).ofConv.toRingHom x = map f.ofConv.toRingHom x + map g.ofConv.toRingHom x := by
  have key : (f * g).ofConv.toRingHom =
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => Commute.all _ _)).toRingHom.comp
        (comulRingHom R A) := by
    refine RingHom.ext fun c => ?_
    change (f * g) c = _
    rw [AlgHom.convMul_apply]
    rfl
  rw [key, ← map_map, (mem_wittHom_iff x).1 hx, map_add, map_map, map_map]
  congr 1
  · exact congrArg (fun h : A →+* T => map h x)
      (congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft f.ofConv g.ofConv
        (fun _ _ => Commute.all _ _)))
  · exact congrArg (fun h : A →+* T => map h x)
      (congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight f.ofConv g.ofConv
        (fun _ _ => Commute.all _ _)))

/--
@isnad1 id=eq.1h5v.s8.4b687d3657bc from=translated src=- shape=4e6ecab6 vocab=f3ae7304
-/
theorem map_counit_of_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    map (Bialgebra.counitAlgHom R A).toRingHom x = 0 := by

  have h := map_convMul_of_mem_wittHom (T := A) hx 1 (WithConv.toConv (AlgHom.id R A))
  rw [one_mul] at h
  have h1 : map (1 : WithConv (A →ₐ[R] A)).ofConv.toRingHom x = 0 :=
    (add_right_cancel ((zero_add _).trans h)).symm

  have hfac : (1 : WithConv (A →ₐ[R] A)).ofConv.toRingHom =
      (algebraMap R A).comp (Bialgebra.counitAlgHom R A).toRingHom := by
    refine RingHom.ext fun c => ?_
    simp [AlgHom.convOne_apply]
  rw [hfac, ← map_map] at h1
  have hinj : Injective (map (p := p) (n := n) (algebraMap R A)) :=
    map_injective fun r s hrs => by
      simpa using congrArg (Coalgebra.counit (R := R) (A := A)) hrs
  exact hinj (by rw [h1, map_zero])

/--
@isnad1 id=eq.1h6v.s8.9f81f6a41db8 from=translated src=- shape=d850525e vocab=82bf4927
-/
theorem counit_coeff_of_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A)
    (i : Fin n) : Coalgebra.counit (R := R) (x.coeff i) = 0 := by
  have := congrArg (TruncatedWittVector.coeff i) (map_counit_of_mem_wittHom hx)
  simp only [coeff_map, TruncatedWittVector.coeff_zero] at this
  exact this

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

/--
@isnad1 id=mem.1h7v.s9.7ad00f293e9a from=translated src=- shape=b46d4b79 vocab=c573eac9
-/
theorem map_mem_wittHom (φ : A →ₐc[R] B) {x : TruncatedWittVector p n A}
    (hx : x ∈ wittHom R p n A) : map (φ : A →ₐ[R] B).toRingHom x ∈ wittHom R p n B := by
  rw [mem_wittHom_iff] at hx ⊢

  have hΔ : (comulRingHom R B).comp (φ : A →ₐ[R] B).toRingHom =
      (Algebra.TensorProduct.map (φ : A →ₐ[R] B) (φ : A →ₐ[R] B)).toRingHom.comp
        (comulRingHom R A) := by
    refine RingHom.ext fun a => ?_
    exact (AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom φ) a).symm
  have h₁ : (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B B).toRingHom.comp
      (φ : A →ₐ[R] B).toRingHom =
      (Algebra.TensorProduct.map (φ : A →ₐ[R] B) (φ : A →ₐ[R] B)).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp
  have h₂ : (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R B B).toRingHom.comp
      (φ : A →ₐ[R] B).toRingHom =
      (Algebra.TensorProduct.map (φ : A →ₐ[R] B) (φ : A →ₐ[R] B)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp
  rw [map_map, map_map, map_map, hΔ, h₁, h₂, ← map_map, ← map_map, ← map_map, hx, map_add]

variable (p n) in

noncomputable def wittHomMap (φ : A →ₐc[R] B) : wittHom R p n A →+ wittHom R p n B where
  toFun x := ⟨map (φ : A →ₐ[R] B).toRingHom x, map_mem_wittHom φ x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/--
@isnad1 id=eq.0h7v.s11.371aaed36a9e from=translated src=- shape=2fdb0f47 vocab=bfce86fd
-/
@[simp] theorem coe_wittHomMap (φ : A →ₐc[R] B) (x : wittHom R p n A) :
    (wittHomMap p n φ x : TruncatedWittVector p n B) = map (φ : A →ₐ[R] B).toRingHom x := rfl

/--
@isnad1 id=eq.0h8v.s11.0a52ec8de61e from=translated src=- shape=cb038c99 vocab=2840ac68
-/
theorem coeff_wittHomMap (φ : A →ₐc[R] B) (x : wittHom R p n A) (i : Fin n) :
    (wittHomMap p n φ x : TruncatedWittVector p n B).coeff i =
      φ ((x : TruncatedWittVector p n A).coeff i) :=
  coeff_map _ _ _

/--
@isnad1 id=injectiv.1h6v.s11.1218865913a4 from=translated src=- shape=c26c1ec2 vocab=464394d5
-/
theorem wittHomMap_injective {φ : A →ₐc[R] B} (hφ : Injective φ) :
    Injective (wittHomMap p n φ) := fun _ _ h =>
  Subtype.ext (map_injective (f := (φ : A →ₐ[R] B).toRingHom) hφ (congrArg Subtype.val h))

end Map

/--
@isnad1 id=mem.1h5v.s8.8f67d72920aa from=translated src=- shape=469b3c6f vocab=d3d90980
-/
theorem verschiebung_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    TruncWitt.verschiebung x ∈ wittHom R p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_verschiebung, map_verschiebung, map_verschiebung, hx, map_add]

variable (R p n A) in

noncomputable def wittHomVerschiebung : wittHom R p n A →+ wittHom R p n A where
  toFun x := ⟨TruncWitt.verschiebung x, verschiebung_mem_wittHom x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/--
@isnad1 id=eq.0h5v.s11.35662e0c642c from=translated src=- shape=71c675e2 vocab=29086fee
-/
@[simp] theorem coe_wittHomVerschiebung (x : wittHom R p n A) :
    (wittHomVerschiebung R p n A x : TruncatedWittVector p n A) = TruncWitt.verschiebung x := rfl

section CharP

variable [CharP R p]

variable (R p) in
omit hp in

/--
@isnad1 id=eq.0h3v.s5.191209d930e9 from=translated src=- shape=6ad4a932 vocab=d713ff55
-/
theorem natCast_eq_zero_of_algebra (B : Type w) [CommRing B] [Algebra R B] : (p : B) = 0 := by
  rw [← map_natCast (algebraMap R B), CharP.cast_eq_zero, map_zero]

/--
@isnad1 id=mem.1h5v.s7.55d6727ce005 from=translated src=- shape=af6e875a vocab=2918d79d
-/
theorem frobeniusFun_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    TruncWitt.frobeniusFun x ∈ wittHom R p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_frobeniusFun, map_frobeniusFun, map_frobeniusFun, hx,
    frobeniusFun_add (natCast_eq_zero_of_algebra R p _)]

variable (R p n A) in

noncomputable def wittHomFrobenius : wittHom R p n A →+ wittHom R p n A where
  toFun x := ⟨TruncWitt.frobeniusFun x, frobeniusFun_mem_wittHom x.2⟩
  map_zero' := Subtype.ext frobeniusFun_zero
  map_add' _ _ := Subtype.ext (frobeniusFun_add (natCast_eq_zero_of_algebra R p A) _ _)

/--
@isnad1 id=eq.0h5v.s11.e04e99904d6b from=translated src=- shape=56abfc92 vocab=1d112c88
-/
@[simp] theorem coe_wittHomFrobenius (x : wittHom R p n A) :
    (wittHomFrobenius R p n A x : TruncatedWittVector p n A) = TruncWitt.frobeniusFun x := rfl

/--
@isnad1 id=eq.0h6v.s11.975e0a68f7f7 from=translated src=- shape=273fc81e vocab=9cf48018
-/
theorem coeff_wittHomFrobenius (x : wittHom R p n A) (i : Fin n) :
    (wittHomFrobenius R p n A x : TruncatedWittVector p n A).coeff i =
      (x : TruncatedWittVector p n A).coeff i ^ p :=
  coeff_frobeniusFun _ _

/--
@isnad1 id=eq.0h5v.s12.119429f6e4cc from=translated src=- shape=e7f34f14 vocab=5c11dd87
-/
theorem wittHomFrobenius_verschiebung (x : wittHom R p n A) :
    wittHomFrobenius R p n A (wittHomVerschiebung R p n A x) = (p : ℤ) • x :=
  Subtype.ext (frobeniusFun_verschiebung_eq_smul (natCast_eq_zero_of_algebra R p A) _)

/--
@isnad1 id=eq.0h5v.s12.76af4b67044d from=translated src=- shape=e7f34f14 vocab=5c11dd87
-/
theorem wittHomVerschiebung_frobenius (x : wittHom R p n A) :
    wittHomVerschiebung R p n A (wittHomFrobenius R p n A x) = (p : ℤ) • x :=
  Subtype.ext (verschiebung_frobeniusFun (natCast_eq_zero_of_algebra R p A) _)

variable (R p n A) in

noncomputable def wittHomDieudonneDatum : DieudonneDatum (p : ℤ) (wittHom R p n A) where
  F := (wittHomFrobenius R p n A).toIntLinearMap
  V := (wittHomVerschiebung R p n A).toIntLinearMap
  fv := LinearMap.ext fun x => wittHomFrobenius_verschiebung x
  vf := LinearMap.ext fun x => wittHomVerschiebung_frobenius x

/--
@isnad1 id=eq.0h5v.s12.f46de517aeb6 from=translated src=- shape=586855df vocab=e846e55e
-/
@[simp] theorem wittHomDieudonneDatum_F_apply (x : wittHom R p n A) :
    (wittHomDieudonneDatum R p n A).F x = wittHomFrobenius R p n A x := rfl

/--
@isnad1 id=eq.0h5v.s12.bc5ef9b806c7 from=translated src=- shape=586855df vocab=6a0f0ef6
-/
@[simp] theorem wittHomDieudonneDatum_V_apply (x : wittHom R p n A) :
    (wittHomDieudonneDatum R p n A).V x = wittHomVerschiebung R p n A x := rfl

/--
@isnad1 id=eq.0h7v.s13.f405aff2e659 from=translated src=- shape=da4c720b vocab=233b8916
-/
theorem wittHomMap_frobenius {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (x : wittHom R p n A) :
    wittHomMap p n φ (wittHomFrobenius R p n A x) = wittHomFrobenius R p n B (wittHomMap p n φ x) :=
  Subtype.ext (map_frobeniusFun _ _)

end CharP

/--
@isnad1 id=eq.0h7v.s13.b4647c094708 from=translated src=- shape=ad9b61bb vocab=29d9ddc3
-/
theorem wittHomMap_verschiebung {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (x : wittHom R p n A) :
    wittHomMap p n φ (wittHomVerschiebung R p n A x) =
      wittHomVerschiebung R p n B (wittHomMap p n φ x) :=
  Subtype.ext (map_verschiebung _ _)

/--
@isnad1 id=mem.1h5v.s9.59e0f99c0206 from=translated src=- shape=3d5094ad vocab=ba9b4493
-/
theorem shift_mem_wittHom {x : TruncatedWittVector p n A} (hx : x ∈ wittHom R p n A) :
    TruncWitt.shift x ∈ wittHom R p (n + 1) A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shift, map_shift, map_shift, hx, map_add]

variable (R p n A) in

noncomputable def wittHomShift : wittHom R p n A →+ wittHom R p (n + 1) A where
  toFun x := ⟨TruncWitt.shift x, shift_mem_wittHom x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/--
@isnad1 id=eq.0h5v.s12.769b7f63fdf7 from=translated src=- shape=33515e7c vocab=70f0aec0
-/
@[simp] theorem coe_wittHomShift (x : wittHom R p n A) :
    (wittHomShift R p n A x : TruncatedWittVector p (n + 1) A) = TruncWitt.shift x := rfl

/--
@isnad1 id=injectiv.0h4v.s12.60aef5cf861b from=translated src=- shape=51f6346a vocab=6c80b356
-/
theorem wittHomShift_injective : Injective (wittHomShift R p n A) := fun _ _ h =>
  Subtype.ext (shift_injective (congrArg Subtype.val h))

/--
@isnad1 id=mem.2h6v.s8.0d0f52ca2695 from=translated src=- shape=ce76b42f vocab=565f7e3c
-/
theorem truncateLE_mem_wittHom {m : ℕ} (hm : n ≤ m) {x : TruncatedWittVector p m A}
    (hx : x ∈ wittHom R p m A) : TruncatedWittVector.truncate hm x ∈ wittHom R p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_truncateLE, map_truncateLE, map_truncateLE, hx, map_add]

variable (R p A) in

noncomputable def wittHomRestrict {m : ℕ} (hm : n ≤ m) : wittHom R p m A →+ wittHom R p n A where
  toFun x := ⟨TruncatedWittVector.truncate hm x, truncateLE_mem_wittHom hm x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/--
@isnad1 id=eq.1h6v.s11.b4c5ec12bcaa from=translated src=- shape=df79e019 vocab=d304b9cb
-/
@[simp] theorem coe_wittHomRestrict {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    (wittHomRestrict R p A hm x : TruncatedWittVector p n A) =
      TruncatedWittVector.truncate hm x := rfl

/--
@isnad1 id=eq.0h5v.s13.528366e7301e from=translated src=- shape=f47f7308 vocab=416e62e6
-/
theorem wittHomRestrict_shift (x : wittHom R p n A) :
    wittHomRestrict R p A (Nat.le_succ n) (wittHomShift R p n A x) = wittHomVerschiebung R p n A x :=
  Subtype.ext (truncate_shift _)

/--
@isnad1 id=eq.0h5v.s14.ae4b22a8fd78 from=translated src=- shape=bb756bc8 vocab=416e62e6
-/
theorem wittHomShift_restrict (y : wittHom R p (n + 1) A) :
    wittHomShift R p n A (wittHomRestrict R p A (Nat.le_succ n) y) =
      wittHomVerschiebung R p (n + 1) A y :=
  Subtype.ext (shift_truncate_succ _)

/--
@isnad1 id=eq.0h5v.s14.ca64d4cb77d5 from=translated src=- shape=d402cf0d vocab=98f42073
-/
theorem wittHomShift_verschiebung (x : wittHom R p n A) :
    wittHomShift R p n A (wittHomVerschiebung R p n A x) =
      wittHomVerschiebung R p (n + 1) A (wittHomShift R p n A x) :=
  Subtype.ext (by
    rw [coe_wittHomShift, coe_wittHomVerschiebung, coe_wittHomVerschiebung, coe_wittHomShift,
      ← truncate_shift, shift_truncate_succ])

/--
@isnad1 id=eq.0h5v.s14.da9b18eaf676 from=translated src=- shape=67303380 vocab=0ce6ca25
-/
theorem wittHomShift_frobenius [CharP R p] (x : wittHom R p n A) :
    wittHomShift R p n A (wittHomFrobenius R p n A x) =
      wittHomFrobenius R p (n + 1) A (wittHomShift R p n A x) :=
  Subtype.ext (frobeniusFun_shift _).symm

/--
@isnad1 id=eq.1h6v.s13.f8c9275eeef9 from=translated src=- shape=87b93473 vocab=88ed69af
-/
theorem wittHomRestrict_verschiebung {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    wittHomRestrict R p A hm (wittHomVerschiebung R p m A x) =
      wittHomVerschiebung R p n A (wittHomRestrict R p A hm x) :=
  Subtype.ext (verschiebung_truncateLE hm _).symm

/--
@isnad1 id=eq.1h6v.s13.9142b4c1157e from=translated src=- shape=2fb85035 vocab=f292e40b
-/
theorem wittHomRestrict_frobenius [CharP R p] {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    wittHomRestrict R p A hm (wittHomFrobenius R p m A x) =
      wittHomFrobenius R p n A (wittHomRestrict R p A hm x) :=
  Subtype.ext (frobeniusFun_truncateLE hm _).symm

/--
@isnad1 id=eq.0h7v.s14.491799978f19 from=translated src=- shape=d7acf3a4 vocab=06bf8831
-/
theorem wittHomMap_shift {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (x : wittHom R p n A) :
    wittHomMap p (n + 1) φ (wittHomShift R p n A x) = wittHomShift R p n B (wittHomMap p n φ x) :=
  Subtype.ext (map_shift _ _)

/--
@isnad1 id=eq.1h8v.s13.b4b8b4aafd22 from=translated src=- shape=3b1f7d6f vocab=fea56592
-/
theorem wittHomMap_restrict {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    {m : ℕ} (hm : n ≤ m) (x : wittHom R p m A) :
    wittHomMap p n φ (wittHomRestrict R p A hm x) = wittHomRestrict R p B hm (wittHomMap p m φ x) :=
  Subtype.ext (map_truncateLE hm _ _)

end WittHom

end Deformation
