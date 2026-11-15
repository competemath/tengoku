import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Function

universe u v w u'

namespace Deformation

namespace WittGhost

variable {p : ℕ} [hp : Fact p.Prime] {ℛ : Type u} [CommRing ℛ]

/--
@isnad1 id=eq.0h4v.s7.7a6d9711374e from=translated src=- shape=bb9de027 vocab=8aa0e8ce
-/
theorem ghostComponent_eq_sum (n : ℕ) (X : WittVector p ℛ) :
    WittVector.ghostComponent n X =
      ∑ i ∈ Finset.range (n + 1), (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i) := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]

/--
@isnad1 id=eq.0h6v.s8.a4975827211f from=translated src=- shape=3c048a01 vocab=540b8aaf
-/
theorem ghostComponent_map {S : Type v} [CommRing S] (f : ℛ →+* S) (n : ℕ) (X : WittVector p ℛ) :
    WittVector.ghostComponent n (WittVector.map f X) = f (WittVector.ghostComponent n X) := by
  simp only [ghostComponent_eq_sum, map_sum, map_mul, map_pow, map_natCast, WittVector.map_coeff]

omit hp in
/--
@isnad1 id=le.1h2v.s5.ed7b6973a8ec from=translated src=- shape=a1311e94 vocab=cc49959f
-/
theorem succ_le_prime_pow (hp1 : 1 < p) (k : ℕ) : k + 1 ≤ p ^ k := Nat.lt_pow_self hp1

/--
@isnad1 id=mem.2h5v.s8.18da8eddf1fb from=translated src=- shape=2fe8fc75 vocab=dead3ac1
-/
theorem pow_mul_pow_mem_span_pow {x : ℛ} (hx : x ∈ Ideal.span {(p : ℛ)}) {i n : ℕ} (hi : i ≤ n) :
    (p : ℛ) ^ i * x ^ p ^ (n - i) ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hx
  rw [← hb, mul_pow, Ideal.mem_span_singleton]
  have hle : n + 1 ≤ i + p ^ (n - i) := by
    have := succ_le_prime_pow hp.out.one_lt (n - i)
    omega
  calc (p : ℛ) ^ (n + 1) ∣ (p : ℛ) ^ (i + p ^ (n - i)) := pow_dvd_pow _ hle
    _ = (p : ℛ) ^ i * (p : ℛ) ^ p ^ (n - i) := pow_add _ _ _
    _ ∣ (p : ℛ) ^ i * (b ^ p ^ (n - i) * (p : ℛ) ^ p ^ (n - i)) :=
        mul_dvd_mul_left _ (dvd_mul_left _ _)

/--
@isnad1 id=mem.1h4v.s8.cf8131a4b7c6 from=translated src=- shape=18dbba02 vocab=00fa8b2b
-/
theorem ghostComponent_mem_span_pow_of_forall_coeff_mem {n : ℕ} {X : WittVector p ℛ}
    (hX : ∀ i ≤ n, X.coeff i ∈ Ideal.span {(p : ℛ)}) :
    WittVector.ghostComponent n X ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
  rw [ghostComponent_eq_sum]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact pow_mul_pow_mem_span_pow (hX i (Nat.le_of_lt_succ hi)) (Nat.le_of_lt_succ hi)

/--
@isnad1 id=mem.1h4v.s8.f4ab51739c85 from=translated src=- shape=ae4fb6a1 vocab=b2aaa1ba
-/
theorem ghostComponent_pred_mem_span_pow {n : ℕ} {X : WittVector p ℛ}
    (hX : ∀ i < n, X.coeff i ∈ Ideal.span {(p : ℛ)}) :
    WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} := by
  cases n with
  | zero => simp
  | succ k =>
    exact ghostComponent_mem_span_pow_of_forall_coeff_mem fun i hi => hX i (Nat.lt_succ_of_le hi)

/--
@isnad1 id=mem.1h4v.s8.93abc34a654c from=translated src=- shape=8185c872 vocab=92d05f46
-/
theorem ghostComponent_verschiebung_mem_span_pow {n : ℕ} {X : WittVector p ℛ}
    (hX : WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n}) :
    WittVector.ghostComponent n (WittVector.verschiebung X) ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
  cases n with
  | zero => rw [WittVector.ghostComponent_zero_verschiebung]; exact zero_mem _
  | succ k =>
    rw [WittVector.ghostComponent_verschiebung, Ideal.mem_span_singleton, pow_succ']
    exact mul_dvd_mul_left _ (Ideal.mem_span_singleton.1 hX)

end WittGhost

namespace TruncWitt

section FontaineKer

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] (π : ℛ →+* A)

noncomputable def fontaineKer : AddSubgroup (TruncatedWittVector p n A) where
  carrier := {a | ∃ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a ∧
    WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n}}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨X, rfl, hX⟩ ⟨Y, rfl, hY⟩
    exact ⟨X + Y, by simp, by rw [map_add]; exact add_mem hX hY⟩
  neg_mem' := by
    rintro a ⟨X, rfl, hX⟩
    exact ⟨-X, by simp, by rw [map_neg]; exact neg_mem hX⟩

variable {p n π}

/--
@isnad1 id=iff.0h6v.s9.df30c57dc200 from=translated src=- shape=8ee9c539 vocab=9ec90fac
-/
theorem mem_fontaineKer_iff (a : TruncatedWittVector p n A) :
    a ∈ fontaineKer p n π ↔ ∃ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a ∧
      WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} :=
  Iff.rfl

/--
@isnad1 id=mem.1h6v.s9.947a6928551f from=translated src=- shape=1cfeec63 vocab=9ec90fac
-/
theorem truncate_map_mem_fontaineKer {X : WittVector p ℛ}
    (hX : WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n}) :
    WittVector.truncate n (WittVector.map π X) ∈ fontaineKer p n π :=
  ⟨X, rfl, hX⟩

variable (p π) in

/--
@isnad1 id=eq.0h4v.s7.1eb1fb8cde23 from=translated src=- shape=1a4775e8 vocab=06915531
-/
theorem fontaineKer_zero : fontaineKer p 0 π = ⊤ :=
  eq_top_iff.2 fun a _ => ⟨0, TruncatedWittVector.ext fun i => i.elim0, by simp⟩

/--
@isnad1 id=mem.2h7v.s8.fe581ed85eb8 from=translated src=- shape=2e2fcba6 vocab=3ccd0f1c
-/
theorem coeff_mem_ker_of_truncate_map_eq_zero {X : WittVector p ℛ}
    (h : WittVector.truncate n (WittVector.map π X) = 0) (i : ℕ) (hi : i < n) :
    X.coeff i ∈ RingHom.ker π := by
  rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at h
  rw [RingHom.mem_ker, ← WittVector.map_coeff]
  exact h i hi

/--
@isnad1 id=mem.3h7v.s9.4c1cfa6f135c from=translated src=- shape=0bcb130e vocab=c2472f40
-/
theorem ghostComponent_pred_mem_of_truncate_map_eq (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    {X Y : WittVector p ℛ}
    (h : WittVector.truncate n (WittVector.map π X) = WittVector.truncate n (WittVector.map π Y))
    (hY : WittVector.ghostComponent (n - 1) Y ∈ Ideal.span {(p : ℛ) ^ n}) :
    WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} := by
  have hXY : WittVector.truncate n (WittVector.map π (X - Y)) = 0 := by
    rw [map_sub, map_sub, h, sub_self]
  have key : WittVector.ghostComponent (n - 1) (X - Y) ∈ Ideal.span {(p : ℛ) ^ n} :=
    WittGhost.ghostComponent_pred_mem_span_pow fun i hi =>
      hπ (coeff_mem_ker_of_truncate_map_eq_zero hXY i hi)
  have : X = X - Y + Y := (sub_add_cancel X Y).symm
  rw [this, map_add]
  exact add_mem key hY

/--
@isnad1 id=iff.1h6v.s9.ea3e5dc15345 from=translated src=- shape=1fa32768 vocab=01e1282a
-/
theorem truncate_map_mem_fontaineKer_iff (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    (X : WittVector p ℛ) :
    WittVector.truncate n (WittVector.map π X) ∈ fontaineKer p n π ↔
      WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} :=
  ⟨fun ⟨_, hYX, hY⟩ => ghostComponent_pred_mem_of_truncate_map_eq hπ hYX.symm hY,
    truncate_map_mem_fontaineKer⟩

/--
@isnad1 id=ex.1h6v.s8.a4f8fa512df6 from=translated src=- shape=25279280 vocab=ceaa581f
-/
theorem exists_truncate_map_eq (hπs : Surjective π) (a : TruncatedWittVector p n A) :
    ∃ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a := by
  obtain ⟨Z, rfl⟩ := WittVector.truncate_surjective p n A a
  obtain ⟨X, rfl⟩ := WittVector.map_surjective π hπs Z
  exact ⟨X, rfl⟩

/--
@isnad1 id=iff.2h6v.s9.badb4235a1a2 from=translated src=- shape=4523662e vocab=9f95151f
-/
theorem mem_fontaineKer_iff_forall (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π)
    (a : TruncatedWittVector p n A) :
    a ∈ fontaineKer p n π ↔ ∀ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a →
      WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} := by
  constructor
  · rintro ha X rfl
    exact (truncate_map_mem_fontaineKer_iff hπ X).1 ha
  · intro h
    obtain ⟨X, rfl⟩ := exists_truncate_map_eq hπs a
    exact truncate_map_mem_fontaineKer (h X rfl)

/--
@isnad1 id=eq.0h6v.s10.0f53b5962ea2 from=translated src=- shape=901b8077 vocab=7f403bf8
-/
theorem truncate_map_verschiebung (X : WittVector p ℛ) :
    WittVector.truncate (n + 1) (WittVector.map π (WittVector.verschiebung X)) =
      shift (WittVector.truncate n (WittVector.map π X)) := by
  rw [WittVector.map_verschiebung, shift_truncate]

/--
@isnad1 id=mem.1h6v.s9.1b6f3c3f4e06 from=translated src=- shape=18364ec7 vocab=74b9fab1
-/
theorem shift_mem_fontaineKer {a : TruncatedWittVector p n A} (ha : a ∈ fontaineKer p n π) :
    shift a ∈ fontaineKer p (n + 1) π := by
  obtain ⟨X, rfl, hX⟩ := ha
  refine ⟨WittVector.verschiebung X, truncate_map_verschiebung X, ?_⟩
  rw [Nat.add_sub_cancel]
  exact WittGhost.ghostComponent_verschiebung_mem_span_pow hX

/--
@isnad1 id=mem.2h7v.s8.77c44b54921c from=translated src=- shape=4bdcff1e vocab=960538a6
-/
theorem shiftLE_mem_fontaineKer {m : ℕ} (h : n ≤ m) {a : TruncatedWittVector p n A}
    (ha : a ∈ fontaineKer p n π) : shiftLE h a ∈ fontaineKer p m π := by
  induction h with
  | refl => rwa [shiftLE_refl]
  | @step m h ih =>
    rw [← shiftLE_shiftLE h (Nat.le_succ m), shiftLE_succ]
    exact shift_mem_fontaineKer ih

/--
@isnad1 id=mem.4h6v.s10.1e3fcf6361b7 from=translated src=- shape=2a3c3687 vocab=c8c11e98
-/
theorem mem_fontaineKer_of_shift_mem (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π)
    {a : TruncatedWittVector p n A} (ha : shift a ∈ fontaineKer p (n + 1) π) :
    a ∈ fontaineKer p n π := by
  obtain ⟨X, rfl⟩ := exists_truncate_map_eq hπs a
  rw [← truncate_map_verschiebung, truncate_map_mem_fontaineKer_iff hπ, Nat.add_sub_cancel] at ha
  refine truncate_map_mem_fontaineKer ?_
  cases n with
  | zero => simp
  | succ k =>
    rw [WittVector.ghostComponent_verschiebung, Ideal.mem_span_singleton] at ha
    obtain ⟨c, hc⟩ := ha
    rw [Nat.add_sub_cancel, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩

    have h0 : (WittVector.ghostComponent k X - (p : ℛ) ^ (k + 1) * c) * (p : ℛ) = 0 := by
      rw [sub_mul, mul_comm, hc]; ring
    exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_right.1 hp' _ h0)

/--
@isnad1 id=mem.5h7v.s9.a08fd89682e3 from=translated src=- shape=ed043d2e vocab=dc90aac3
-/
theorem mem_fontaineKer_of_shiftLE_mem (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π) {m : ℕ} (h : n ≤ m)
    {a : TruncatedWittVector p n A} (ha : shiftLE h a ∈ fontaineKer p m π) :
    a ∈ fontaineKer p n π := by
  induction h with
  | refl => rwa [shiftLE_refl] at ha
  | @step m h ih =>
    rw [← shiftLE_shiftLE h (Nat.le_succ m), shiftLE_succ] at ha
    exact ih (mem_fontaineKer_of_shift_mem hp' hπ hπs ha)

/--
@isnad1 id=iff.4h7v.s9.f65c205d02d1 from=translated src=- shape=4a1e4d0f vocab=dc90aac3
-/
theorem shiftLE_mem_fontaineKer_iff (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π) {m : ℕ} (h : n ≤ m)
    (a : TruncatedWittVector p n A) :
    shiftLE h a ∈ fontaineKer p m π ↔ a ∈ fontaineKer p n π :=
  ⟨mem_fontaineKer_of_shiftLE_mem hp' hπ hπs h, shiftLE_mem_fontaineKer h⟩

/--
@isnad1 id=mem.2h11v.s8.1202cd24ff58 from=translated src=- shape=327c94c0 vocab=fa5f2064
-/
theorem map_mem_fontaineKer {ℛ' : Type w} [CommRing ℛ'] {A' : Type u'} [CommRing A']
    (f : ℛ →+* ℛ') (g : A →+* A') (π' : ℛ' →+* A') (hcomm : π'.comp f = g.comp π)
    {a : TruncatedWittVector p n A} (ha : a ∈ fontaineKer p n π) :
    map g a ∈ fontaineKer p n π' := by
  obtain ⟨X, rfl, hX⟩ := ha
  refine ⟨WittVector.map f X, ?_, ?_⟩
  · rw [map_truncate]
    congr 1
    ext i
    simp only [WittVector.map_coeff]
    exact (RingHom.congr_fun hcomm (X.coeff i))
  · rw [WittGhost.ghostComponent_map, Ideal.mem_span_singleton, ← map_natCast f p, ← map_pow]
    exact map_dvd f (Ideal.mem_span_singleton.1 hX)

theorem eq_zero_of_mem_fontaineKer_one (hA : (p : A) = 0) {a : TruncatedWittVector p 1 A}
    (ha : a ∈ fontaineKer p 1 π) : a = 0 := by
  obtain ⟨X, rfl, hX⟩ := ha
  rw [Nat.sub_self, WittVector.ghostComponent_apply, wittPolynomial_zero, MvPolynomial.aeval_X,
    pow_one] at hX
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hX
  refine TruncatedWittVector.ext fun i => ?_
  rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero, WittVector.map_coeff,
    show ((i : Fin 1) : ℕ) = 0 from Subsingleton.elim (α := Fin 1) i 0 ▸ rfl, ← hb, map_mul,
    map_natCast, hA, mul_zero]

end FontaineKer

end TruncWitt

section Hodge

variable (R : Type w) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] [Bialgebra R A] (π : ℛ →+* A)

open TruncWitt DieudonneModule

noncomputable def fontaineHodgeLevel : AddSubgroup (wittHom R p n A) :=
  (fontaineKer p n π).addSubgroupOf (wittHom R p n A)

variable {R p n π}

/--
@isnad1 id=iff.0h7v.s10.0af8be5b1884 from=translated src=- shape=4412a303 vocab=fbe244ff
-/
theorem mem_fontaineHodgeLevel_iff (x : wittHom R p n A) :
    x ∈ fontaineHodgeLevel R p n π ↔ (x : TruncatedWittVector p n A) ∈ fontaineKer p n π :=
  Iff.rfl

/--
@isnad1 id=mem.2h8v.s12.dde7845ca343 from=translated src=- shape=f9c0a363 vocab=7d9e7a93
-/
theorem wittHomShiftLE_mem_fontaineHodgeLevel {m : ℕ} (h : n ≤ m) {x : wittHom R p n A}
    (hx : x ∈ fontaineHodgeLevel R p n π) :
    wittHomShiftLE R p A h x ∈ fontaineHodgeLevel R p m π :=
  shiftLE_mem_fontaineKer h hx

variable (R p π) in

noncomputable def fontaineHodgeAddSubgroup : AddSubgroup (DieudonneModule R p A) where
  carrier := {z | ∃ (n : ℕ) (x : wittHom R p n A),
    (x : TruncatedWittVector p n A) ∈ fontaineKer p n π ∧ DieudonneModule.of R p A n x = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, x, hx, rfl⟩ ⟨m, y, hy, rfl⟩
    refine ⟨max n m, wittHomShiftLE R p A (le_max_left n m) x +
      wittHomShiftLE R p A (le_max_right n m) y, ?_, ?_⟩
    · exact add_mem (shiftLE_mem_fontaineKer _ hx) (shiftLE_mem_fontaineKer _ hy)
    · rw [map_add, of_shiftLE, of_shiftLE]
  neg_mem' := by
    rintro _ ⟨n, x, hx, rfl⟩
    exact ⟨n, -x, neg_mem hx, map_neg _ _⟩

variable (R p π) in

noncomputable def fontaineHodge : Submodule ℤ (DieudonneModule R p A) :=
  (fontaineHodgeAddSubgroup R p π).toIntSubmodule

/--
@isnad1 id=iff.0h6v.s11.d14187597f78 from=translated src=- shape=acfdb51b vocab=42aa8293
-/
theorem mem_fontaineHodge_iff (z : DieudonneModule R p A) :
    z ∈ fontaineHodge R p π ↔ ∃ (n : ℕ) (x : wittHom R p n A),
      (x : TruncatedWittVector p n A) ∈ fontaineKer p n π ∧ DieudonneModule.of R p A n x = z :=
  Iff.rfl

/--
@isnad1 id=mem.1h7v.s11.9b3f4336a353 from=translated src=- shape=0db80d83 vocab=42aa8293
-/
theorem of_mem_fontaineHodge {x : wittHom R p n A}
    (hx : (x : TruncatedWittVector p n A) ∈ fontaineKer p n π) :
    DieudonneModule.of R p A n x ∈ fontaineHodge R p π :=
  ⟨n, x, hx, rfl⟩

/--
@isnad1 id=iff.3h7v.s11.ebc306d873cd from=translated src=- shape=80cf8b32 vocab=fd804bfd
-/
theorem of_mem_fontaineHodge_iff (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π) (x : wittHom R p n A) :
    DieudonneModule.of R p A n x ∈ fontaineHodge R p π ↔
      (x : TruncatedWittVector p n A) ∈ fontaineKer p n π := by
  refine ⟨?_, of_mem_fontaineHodge⟩
  rintro ⟨m, y, hy, hxy⟩
  rw [of_eq_of_iff] at hxy
  have hy' : (wittHomShiftLE R p A (le_max_left m n) y : TruncatedWittVector p (max m n) A) ∈
      fontaineKer p (max m n) π := shiftLE_mem_fontaineKer _ hy
  rw [hxy] at hy'
  exact mem_fontaineKer_of_shiftLE_mem hp' hπ hπs (le_max_right m n) hy'

/--
@isnad1 id=le.1h10v.s9.ae3a7437487f from=translated src=- shape=fd622361 vocab=ae9dfef2
-/
theorem map_fontaineHodge_le {ℛ' : Type u'} [CommRing ℛ'] {A' : Type v} [CommRing A'] [Bialgebra R A']
    (π' : ℛ' →+* A') (f : ℛ' →+* ℛ) (g : A' →ₐc[R] A)
    (hcomm : π.comp f = (g : A' →ₐ[R] A).toRingHom.comp π') :
    (fontaineHodge R p π').map (DieudonneModule.map R p g).toIntLinearMap ≤ fontaineHodge R p π := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, x, hx, rfl⟩ := hz
  refine ⟨n, wittHomMap p n g x, ?_, (map_of g x).symm⟩
  exact map_mem_fontaineKer f (g : A' →ₐ[R] A).toRingHom π hcomm hx

end Hodge

namespace SpecialFibre

open scoped TensorProduct
variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Algebra 𝓞 ℛ]

variable (𝓞 k ℛ) in

noncomputable abbrev reduction : ℛ →+* k ⊗[𝓞] ℛ :=
  (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom

/--
@isnad1 id=eq.0h4v.s8.843227627000 from=translated src=- shape=70d24eb3 vocab=ef914745
-/
theorem reduction_apply (r : ℛ) : reduction 𝓞 k ℛ r = (1 : k) ⊗ₜ[𝓞] r := rfl

/--
@isnad1 id=surjecti.1h3v.s8.bcc1c73b6330 from=translated src=- shape=2cb9a2f1 vocab=b66e935a
-/
theorem reduction_surjective (hk : Surjective (algebraMap 𝓞 k)) :
    Surjective (reduction 𝓞 k ℛ) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a r =>
    obtain ⟨o, rfl⟩ := hk a
    refine ⟨o • r, ?_⟩
    rw [reduction_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, map_add _ _ _⟩

/--
@isnad1 id=eq.1h3v.s8.dcc30f47a9ce from=translated src=- shape=65f324a2 vocab=fe4217c4
-/
theorem ker_reduction (hk : Surjective (algebraMap 𝓞 k)) :
    RingHom.ker (reduction 𝓞 k ℛ) = (RingHom.ker (algebraMap 𝓞 k)).map (algebraMap 𝓞 ℛ) := by
  set I := RingHom.ker (algebraMap 𝓞 k) with hI
  apply le_antisymm
  ·
    set J : Ideal ℛ := I.map (algebraMap 𝓞 ℛ) with hJ
    have hle : RingHom.ker (algebraMap 𝓞 k) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap 𝓞 ℛ)) := by
      intro o ho
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ho
    let κ₀ : k →+* ℛ ⧸ J := (algebraMap 𝓞 k).liftOfSurjective hk ⟨_, hle⟩
    have hκ₀ : ∀ o, κ₀ (algebraMap 𝓞 k o) = Ideal.Quotient.mk J (algebraMap 𝓞 ℛ o) := fun o =>
      (algebraMap 𝓞 k).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
    let κ : k →ₐ[𝓞] ℛ ⧸ J :=
      { κ₀ with commutes' := fun o => (hκ₀ o).trans rfl }
    let Ψ : k ⊗[𝓞] ℛ →ₐ[𝓞] ℛ ⧸ J :=
      Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ 𝓞 J) fun _ _ => Commute.all _ _
    intro r hr
    rw [RingHom.mem_ker, reduction_apply] at hr
    have : Ψ ((1 : k) ⊗ₜ[𝓞] r) = Ideal.Quotient.mk J r := by
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    rw [hr, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro o ho
    rw [RingHom.mem_ker] at ho
    rw [Ideal.mem_comap, RingHom.mem_ker, reduction_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, ho,
      TensorProduct.zero_tmul]

/--
@isnad1 id=eq.2h4v.s8.7d8a903d0e2d from=translated src=- shape=3e29c0f8 vocab=98b1a056
-/
theorem ker_reduction_eq_span (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (reduction 𝓞 k ℛ) = Ideal.span {(p : ℛ)} := by
  rw [ker_reduction hk, hker, Ideal.map_span, Set.image_singleton, map_natCast]

/--
@isnad1 id=eq.2h4v.s9.d168eae000ac from=translated src=- shape=982b8fcf vocab=4745febf
-/
theorem natCast_eq_zero (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : (p : k ⊗[𝓞] ℛ) = 0 := by
  have : (p : ℛ) ∈ RingHom.ker (reduction 𝓞 k ℛ) := by
    rw [ker_reduction_eq_span hk hker]; exact Ideal.mem_span_singleton_self _
  rwa [RingHom.mem_ker, map_natCast] at this

end SpecialFibre

end Deformation
