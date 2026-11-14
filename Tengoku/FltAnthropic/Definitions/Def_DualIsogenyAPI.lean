import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

structure IsDualPair (φ : A →+ B) (ψ : B →+ A) (n : ℤ) : Prop where

  comp_left : ∀ a, ψ (φ a) = n • a

  comp_right : ∀ b, φ (ψ b) = n • b

/--
@isnad1 id=isdualpa.2h9v.s7.e062debfeb52 from=translated src=- shape=bb10a193 vocab=49d1e904
-/
theorem IsDualPair.comp {φ' : A →+ B} {φ : B →+ A} {m : ℤ} {ψ' : B →+ C} {ψ : C →+ B}
    {n : ℤ} (hφ : IsDualPair φ' φ m) (hψ : IsDualPair ψ' ψ n) :
    IsDualPair (ψ'.comp φ') (φ.comp ψ) (m * n) := by
  refine ⟨fun a => ?_, fun c => ?_⟩
  · show φ (ψ (ψ' (φ' a))) = (m * n) • a
    rw [hψ.comp_left, map_zsmul, hφ.comp_left, mul_zsmul']
  · show ψ' (φ' (φ (ψ c))) = (m * n) • c
    rw [hφ.comp_right, map_zsmul, hψ.comp_right, mul_zsmul]

/--
@isnad1 id=isdualpa.0h2v.s6.859d6029c841 from=translated src=- shape=c647cbd0 vocab=2eef523e
-/
theorem isDualPair_intCast (m : ℤ) :
    IsDualPair (A := A) (B := A) (m : AddMonoid.End A) (m : AddMonoid.End A) (m ^ 2) := by
  have key : ∀ a : A, (m : AddMonoid.End A) ((m : AddMonoid.End A) a) = m ^ 2 • a := by
    intro a
    have h : (m : AddMonoid.End A) ((m : AddMonoid.End A) a)
        = ((m : AddMonoid.End A) * (m : AddMonoid.End A)) a := rfl
    rw [h, ← Int.cast_mul, AddMonoid.End.intCast_apply, sq]
  exact ⟨key, key⟩

/--
@isnad1 id=eq.3h6v.s8.9faee06dd2ed from=translated src=- shape=9ac84505 vocab=5161a283
-/
theorem IsDualPair.left_unique_of_surjective {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (h : IsDualPair φ ψ n) (hφ : Function.Surjective φ) {ψ' : B →+ A}
    (hψ' : ∀ a, ψ' (φ a) = n • a) : ψ' = ψ := by
  ext b
  obtain ⟨a, rfl⟩ := hφ b
  rw [hψ', h.comp_left]

end AddMonoidHom

namespace AddMonoid.End

variable {A : Type*} [AddCommGroup A]

structure DualEndData (φ : AddMonoid.End A) where

  dual : AddMonoid.End A

  trace : ℤ

  norm : ℤ

  add_dual : φ + dual = (trace : AddMonoid.End A)

  mul_dual : φ * dual = (norm : AddMonoid.End A)

  dual_mul : dual * φ = (norm : AddMonoid.End A)

namespace DualEndData

variable {φ : AddMonoid.End A}

/--
@isnad1 id=isdualpa.0h3v.s5.d51435293cd5 from=translated src=- shape=540cee05 vocab=d57a5453
-/
theorem isDualPair (D : DualEndData φ) :
    AddMonoidHom.IsDualPair (A := A) (B := A) φ D.dual D.norm := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h := DFunLike.congr_fun D.dual_mul a
    rwa [AddMonoid.End.intCast_apply] at h
  · have h := DFunLike.congr_fun D.mul_dual a
    rwa [AddMonoid.End.intCast_apply] at h

/--
@isnad1 id=eq.0h3v.s7.1a1babfed6af from=translated src=- shape=dc553a3a vocab=4c1127b5
-/
theorem dual_eq (D : DualEndData φ) : D.dual = (D.trace : AddMonoid.End A) - φ := by
  rw [← D.add_dual, add_sub_cancel_left]

/--
@isnad1 id=eq.0h3v.s8.401df5505311 from=translated src=- shape=1f180a28 vocab=b2733a0a
-/
theorem charPoly (D : DualEndData φ) :
    φ * φ - (D.trace : AddMonoid.End A) * φ + (D.norm : AddMonoid.End A) = 0 := by
  have h := D.dual_mul
  rw [D.dual_eq, sub_mul] at h
  rw [← h]; abel

/--
@isnad1 id=eq.0h4v.s7.e7b24f86d69c from=translated src=- shape=ae25811e vocab=e2a519d9
-/
theorem add_dual_apply (D : DualEndData φ) (a : A) :
    φ a + D.dual a = D.trace • a := by
  have h : (φ + D.dual) a = (D.trace : AddMonoid.End A) a := by rw [D.add_dual]
  rwa [AddMonoid.End.intCast_apply] at h

def symm (D : DualEndData φ) : DualEndData D.dual where
  dual := φ
  trace := D.trace
  norm := D.norm
  add_dual := by rw [← D.add_dual, add_comm]
  mul_dual := D.dual_mul
  dual_mul := D.mul_dual

/--
@isnad1 id=eq.0h3v.s5.226b45ab9b03 from=translated src=- shape=171db52f vocab=e3dfb11c
-/
@[simp] theorem symm_dual (D : DualEndData φ) : D.symm.dual = φ := rfl
/--
@isnad1 id=eq.0h3v.s5.e9f00a856b19 from=translated src=- shape=cb7bd2d8 vocab=21b98bb9
-/
@[simp] theorem symm_trace (D : DualEndData φ) : D.symm.trace = D.trace := rfl
/--
@isnad1 id=eq.0h3v.s5.fc51d1e22d64 from=translated src=- shape=cb7bd2d8 vocab=21fda46f
-/
@[simp] theorem symm_norm (D : DualEndData φ) : D.symm.norm = D.norm := rfl

private theorem intLin_apply (a b : ℤ) (ψ : AddMonoid.End A) (x : A) :
    ((a : AddMonoid.End A) + (b : AddMonoid.End A) * ψ) x = a • x + b • ψ x := by
  show (a : AddMonoid.End A) x + (b : AddMonoid.End A) (ψ x) = _
  rw [AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply]

/--
@isnad1 id=eq.0h5v.s9.0552784b56f5 from=translated src=- shape=3432ca9e vocab=1d711842
-/
theorem intLinComb_mul_dual (D : DualEndData φ) (a b : ℤ) :
    ((a : AddMonoid.End A) + (b : AddMonoid.End A) * φ)
      * ((a : AddMonoid.End A) + (b : AddMonoid.End A) * D.dual)
      = ((a ^ 2 + D.trace * a * b + D.norm * b ^ 2 : ℤ) : AddMonoid.End A) := by

  ext x
  show ((a : AddMonoid.End A) + b * φ)
      (((a : AddMonoid.End A) + b * D.dual) x)
    = ((a ^ 2 + D.trace * a * b + D.norm * b ^ 2 : ℤ) : AddMonoid.End A) x
  rw [intLin_apply, intLin_apply, AddMonoid.End.intCast_apply,
    map_add, map_zsmul, map_zsmul]
  have hcr : φ (D.dual x) = D.norm • x := D.isDualPair.comp_right x
  have hsum := D.add_dual_apply x
  calc a • (a • x + b • D.dual x) + b • (a • φ x + b • φ (D.dual x))
      = (a * a) • x + (a * b) • D.dual x + ((b * a) • φ x + (b * b) • φ (D.dual x)) := by
        simp only [zsmul_add, ← mul_zsmul]
    _ = (a * a) • x + (a * b) • (φ x + D.dual x) + (b * b) • φ (D.dual x) := by
        rw [zsmul_add, mul_comm b a]; abel
    _ = (a ^ 2 + D.trace * a * b + D.norm * b ^ 2) • x := by
        rw [hcr, hsum, ← mul_zsmul, ← mul_zsmul, ← add_zsmul, ← add_zsmul]
        congr 1; ring

def intLinComb (D : DualEndData φ) (a b : ℤ) :
    DualEndData ((a : AddMonoid.End A) + (b : AddMonoid.End A) * φ) where
  dual := (a : AddMonoid.End A) + (b : AddMonoid.End A) * D.dual
  trace := 2 * a + D.trace * b
  norm := a ^ 2 + D.trace * a * b + D.norm * b ^ 2
  add_dual := by
    have h : (a : AddMonoid.End A) + b * φ + ((a : AddMonoid.End A) + b * D.dual)
        = (a : AddMonoid.End A) + (a : AddMonoid.End A) + b * (φ + D.dual) := by
      rw [mul_add]; abel
    rw [h, D.add_dual]
    ext x
    show (a : AddMonoid.End A) x + (a : AddMonoid.End A) x
        + ((b : AddMonoid.End A) * (D.trace : AddMonoid.End A)) x
      = ((2 * a + D.trace * b : ℤ) : AddMonoid.End A) x
    rw [show ((b : AddMonoid.End A) * (D.trace : AddMonoid.End A)) x
          = (b : AddMonoid.End A) ((D.trace : AddMonoid.End A) x) from rfl,
      AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply,
      AddMonoid.End.intCast_apply, ← add_zsmul, ← mul_zsmul, ← add_zsmul]
    congr 1; ring
  mul_dual := D.intLinComb_mul_dual a b
  dual_mul := D.symm.intLinComb_mul_dual a b

/--
@isnad1 id=eq.0h5v.s8.fc576375dc63 from=translated src=- shape=697cc218 vocab=d450f26e
-/
@[simp] theorem intLinComb_norm (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).norm = a ^ 2 + D.trace * a * b + D.norm * b ^ 2 := rfl

/--
@isnad1 id=eq.0h5v.s8.ea2eb2b87edd from=translated src=- shape=b8b0ea86 vocab=55b41d71
-/
@[simp] theorem intLinComb_trace (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).trace = 2 * a + D.trace * b := rfl

/--
@isnad1 id=eq.0h5v.s8.2534f7208247 from=translated src=- shape=62556e25 vocab=c3346d54
-/
@[simp] theorem intLinComb_dual (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).dual = (a : AddMonoid.End A) + (b : AddMonoid.End A) * D.dual := rfl

/--
@isnad1 id=eq.0h5v.s9.89e5140a9a34 from=translated src=- shape=7f47c7ea vocab=09b89d22
-/
theorem intLinComb_disc (D : DualEndData φ) (a b : ℤ) :
    (D.intLinComb a b).trace ^ 2 - 4 * (D.intLinComb a b).norm
      = b ^ 2 * (D.trace ^ 2 - 4 * D.norm) := by
  simp only [intLinComb_trace, intLinComb_norm]; ring

end DualEndData

def DualEndData.ofCharPoly (φ : AddMonoid.End A) (t n : ℤ)
    (hchar : φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A) = 0) :
    DualEndData φ where
  dual := (t : AddMonoid.End A) - φ
  trace := t
  norm := n
  add_dual := by abel
  mul_dual := by
    have hc : φ * (t : AddMonoid.End A) = (t : AddMonoid.End A) * φ :=
      (Int.cast_commute t φ).eq.symm
    have := hchar; rw [mul_sub, hc, ← sub_eq_zero,
      show (t : AddMonoid.End A) * φ - φ * φ - (n : AddMonoid.End A)
        = -(φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A)) by abel,
      this, neg_zero]
  dual_mul := by
    have := hchar; rw [sub_mul, ← sub_eq_zero,
      show (t : AddMonoid.End A) * φ - φ * φ - (n : AddMonoid.End A)
        = -(φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A)) by abel,
      this, neg_zero]

/--
@isnad1 id=eq.1h4v.s8.bb2779862bc0 from=translated src=- shape=cf9a8e18 vocab=e3b1e921
-/
@[simp] theorem DualEndData.ofCharPoly_trace (φ : AddMonoid.End A) (t n : ℤ) (h) :
    (DualEndData.ofCharPoly φ t n h).trace = t := rfl

/--
@isnad1 id=eq.1h4v.s8.1c50767b6513 from=translated src=- shape=f56f2f5c vocab=5cdd758c
-/
@[simp] theorem DualEndData.ofCharPoly_norm (φ : AddMonoid.End A) (t n : ℤ) (h) :
    (DualEndData.ofCharPoly φ t n h).norm = n := rfl

/--
@isnad1 id=eq.1h4v.s9.bfc190e99f98 from=translated src=- shape=4a6548d6 vocab=9cc92bb2
-/
@[simp] theorem DualEndData.ofCharPoly_dual (φ : AddMonoid.End A) (t n : ℤ) (h) :
    (DualEndData.ofCharPoly φ t n h).dual = (t : AddMonoid.End A) - φ := rfl

def dualEndData_intCast (m : ℤ) : DualEndData (A := A) (m : AddMonoid.End A) where
  dual := (m : AddMonoid.End A)
  trace := 2 * m
  norm := m ^ 2
  add_dual := by push_cast; noncomm_ring
  mul_dual := by rw [← Int.cast_mul, ← sq]
  dual_mul := by rw [← Int.cast_mul, ← sq]

/--
@isnad1 id=eq.0h2v.s5.d283babd9634 from=translated src=- shape=0e43a16e vocab=2b077f42
-/
@[simp] theorem dualEndData_intCast_norm (m : ℤ) :
    (dualEndData_intCast (A := A) m).norm = m ^ 2 := rfl

/--
@isnad1 id=eq.0h2v.s5.8f45dc50a986 from=translated src=- shape=d9c75739 vocab=d193f73a
-/
@[simp] theorem dualEndData_intCast_trace (m : ℤ) :
    (dualEndData_intCast (A := A) m).trace = 2 * m := rfl

/--
@isnad1 id=eq.0h2v.s6.1941250362fd from=translated src=- shape=45e9bfca vocab=3d87b648
-/
@[simp] theorem dualEndData_intCast_dual (m : ℤ) :
    (dualEndData_intCast (A := A) m).dual = (m : AddMonoid.End A) := rfl

end AddMonoid.End

section NamedResiduals

variable {A : Type*} [AddCommGroup A]

def _root_.Tengoku.FltAnthropic.DualIsogenyExistence (S : Subring (AddMonoid.End A)) : Prop :=
  ∀ φ ∈ S, ∃ D : AddMonoid.End.DualEndData φ, D.dual ∈ S ∧ 0 ≤ D.norm

def _root_.Tengoku.FltAnthropic.DualAdditivityResidual (S : Subring (AddMonoid.End A)) : Prop :=
  ∀ φ ∈ S, ∀ ψ ∈ S, ∀ Dφ : AddMonoid.End.DualEndData φ, ∀ Dψ : AddMonoid.End.DualEndData ψ,
    ∃ D : AddMonoid.End.DualEndData (φ + ψ), D.dual = Dφ.dual + Dψ.dual

/--
@isnad1 id=dualisog.0h1v.s6.2d80c2b5b219 from=translated src=- shape=7d1e16a9 vocab=a5c5878a
-/
theorem _root_.Tengoku.FltAnthropic.dualIsogenyExistence_bot :
    DualIsogenyExistence (⊥ : Subring (AddMonoid.End A)) := by
  intro φ hφ
  obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hφ
  exact ⟨AddMonoid.End.dualEndData_intCast m, Subring.mem_bot.mpr ⟨m, rfl⟩, sq_nonneg m⟩

end NamedResiduals

section SatGates

private theorem one_charPoly_int :
    (1 : AddMonoid.End ℤ) * 1 - ((2 : ℤ) : AddMonoid.End ℤ) * 1
      + ((1 : ℤ) : AddMonoid.End ℤ) = 0 := by
  norm_num

/--
@isnad1 id=eq.0h0v.s8.5107edc8dca2 from=translated src=- shape=4bdf6bc3 vocab=85179f5e
-/
theorem _root_.Tengoku.FltAnthropic.gate_intLinComb_norm_at_one :

    ((AddMonoid.End.DualEndData.ofCharPoly (A := ℤ) 1 2 1
      one_charPoly_int).intLinComb 1 2).norm = 9 := by
  simp only [AddMonoid.End.DualEndData.intLinComb_norm,
    AddMonoid.End.DualEndData.ofCharPoly_trace, AddMonoid.End.DualEndData.ofCharPoly_norm]
  decide

/--
@isnad1 id=and.0h0v.s6.2efca66280a2 from=translated src=- shape=6d4c5092 vocab=9ffa4015
-/
theorem _root_.Tengoku.FltAnthropic.gate_dualEndData_intCast_three :
    (AddMonoid.End.dualEndData_intCast (A := ℤ) 3).norm = 9
    ∧ (AddMonoid.End.dualEndData_intCast (A := ℤ) 3).trace = 6 := ⟨rfl, rfl⟩

/--
@isnad1 id=eq.0h0v.s9.acc6fd9fed69 from=translated src=- shape=dbd45a1c vocab=34e9cf00
-/
theorem _root_.Tengoku.FltAnthropic.gate_intLinComb_disc_scaling :
    ((AddMonoid.End.DualEndData.ofCharPoly (A := ℤ) 1 2 1
      one_charPoly_int).intLinComb 0 2).trace ^ 2
        - 4 * ((AddMonoid.End.DualEndData.ofCharPoly (A := ℤ) 1 2 1
          one_charPoly_int).intLinComb 0 2).norm = 2 ^ 2 * (2 ^ 2 - 4 * 1) := by
  rw [AddMonoid.End.DualEndData.intLinComb_disc, AddMonoid.End.DualEndData.ofCharPoly_trace,
    AddMonoid.End.DualEndData.ofCharPoly_norm]

end SatGates
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
