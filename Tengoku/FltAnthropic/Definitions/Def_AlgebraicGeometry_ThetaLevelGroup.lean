import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry.ThetaLevel

section Heis

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ)

abbrev HH : Type := (i : Fin g) → ZMod (δ i)

noncomputable def iota (i : Fin g) : ZMod (δ i) →+ ZMod (2 * d) :=
  if hdiv : δ i ∣ 2 * d then
    ZMod.lift (δ i)
      ⟨(AddMonoidHom.mulLeft ((2 * d / δ i : ℕ) : ZMod (2 * d))).comp (Int.castAddHom (ZMod (2 * d))), by
        change ((2 * d / δ i : ℕ) : ZMod (2 * d)) * (((δ i : ℕ) : ℤ) : ZMod (2 * d)) = 0
        rw [Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hdiv, ZMod.natCast_self]⟩
  else 0

/--
@isnad1 id=eq.1h5v.s9.d613c28b19f3 from=translated src=- shape=53175bc6 vocab=20e4f45a
-/
theorem iota_natCast (i : Fin g) (hdiv : δ i ∣ 2 * d) (x : ℕ) :
    iota δ d i (x : ZMod (δ i)) = ((2 * d / δ i : ℕ) : ZMod (2 * d)) * (x : ZMod (2 * d)) := by
  rw [iota, dite_eq_left hdiv]
  have hx : ((x : ℤ) : ZMod (δ i)) = (x : ZMod (δ i)) := Int.cast_natCast x
  rw [← hx, ZMod.lift_coe]
  change ((2 * d / δ i : ℕ) : ZMod (2 * d)) * ((x : ℤ) : ZMod (2 * d)) = _
  rw [Int.cast_natCast]

noncomputable def pair (k h : HH δ) : ZMod (2 * d) := ∑ i, iota δ d i (k i * h i)

/--
@isnad1 id=eq.0h6v.s7.125deb23ba09 from=translated src=- shape=72690f85 vocab=3569bdd9
-/
theorem pair_add_left (k k' h : HH δ) : pair δ d (k + k') h = pair δ d k h + pair δ d k' h := by
  simp only [pair, Pi.add_apply, add_mul, map_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h6v.s7.129fb88513aa from=translated src=- shape=699fa677 vocab=3569bdd9
-/
theorem pair_add_right (k h h' : HH δ) : pair δ d k (h + h') = pair δ d k h + pair δ d k h' := by
  simp only [pair, Pi.add_apply, mul_add, map_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h4v.s7.5d40c6b6bf28 from=translated src=- shape=e49a4da9 vocab=3e4f5698
-/
theorem pair_zero_left (h : HH δ) : pair δ d 0 h = 0 := by
  simp [pair]

/--
@isnad1 id=eq.0h4v.s7.5c529917335d from=translated src=- shape=7d4c37dc vocab=3e4f5698
-/
theorem pair_zero_right (k : HH δ) : pair δ d k 0 = 0 := by
  simp [pair]

/--
@isnad1 id=eq.0h5v.s7.1594fa6e6c09 from=translated src=- shape=17cc1897 vocab=f6a497f7
-/
theorem pair_neg_right (k h : HH δ) : pair δ d k (-h) = -pair δ d k h := by
  simp only [pair, Pi.neg_apply, mul_neg, map_neg, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.0h5v.s7.51a699487e6b from=translated src=- shape=8e1a5d9b vocab=f6a497f7
-/
theorem pair_neg_left (k h : HH δ) : pair δ d (-k) h = -pair δ d k h := by
  simp only [pair, Pi.neg_apply, neg_mul, map_neg, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.0h5v.s5.04056d740b10 from=translated src=- shape=6a0003a5 vocab=3e4f5698
-/
theorem pair_comm (k h : HH δ) : pair δ d k h = pair δ d h k := by
  simp only [pair, mul_comm]

@[ext]
structure Heis : Type where
  a : ZMod (2 * d)
  h : HH δ
  k : HH δ

namespace Heis

variable {δ} {d}

instance instMul : Mul (Heis δ d) := ⟨fun z z' => ⟨z.a + z'.a + pair δ d z.k z'.h, z.h + z'.h, z.k + z'.k⟩⟩
instance instOne : One (Heis δ d) := ⟨⟨0, 0, 0⟩⟩
instance instInv : Inv (Heis δ d) := ⟨fun z => ⟨-z.a + pair δ d z.k z.h, -z.h, -z.k⟩⟩

/--
@isnad1 id=eq.0h5v.s8.f53f669045a5 from=translated src=- shape=cb250034 vocab=e90bc138
-/
@[simp] theorem mul_a (z z' : Heis δ d) : (z * z').a = z.a + z'.a + pair δ d z.k z'.h := rfl
/--
@isnad1 id=eq.0h5v.s6.c963dfebf71f from=translated src=- shape=f9948159 vocab=e6ba81a4
-/
@[simp] theorem mul_h (z z' : Heis δ d) : (z * z').h = z.h + z'.h := rfl
/--
@isnad1 id=eq.0h5v.s6.b968f343f8ee from=translated src=- shape=f9948159 vocab=fd5a3a3f
-/
@[simp] theorem mul_k (z z' : Heis δ d) : (z * z').k = z.k + z'.k := rfl
/--
@isnad1 id=eq.0h3v.s7.4533791cdb48 from=translated src=- shape=3bf69fe8 vocab=a90c9883
-/
@[simp] theorem one_a : (1 : Heis δ d).a = 0 := rfl
/--
@isnad1 id=eq.0h3v.s6.859e51dee1b8 from=translated src=- shape=c89db60a vocab=8bab9eee
-/
@[simp] theorem one_h : (1 : Heis δ d).h = 0 := rfl
/--
@isnad1 id=eq.0h3v.s6.c802c5d2be21 from=translated src=- shape=c89db60a vocab=19c0655e
-/
@[simp] theorem one_k : (1 : Heis δ d).k = 0 := rfl
/--
@isnad1 id=eq.0h4v.s8.01e1c91303f9 from=translated src=- shape=0d7d65c6 vocab=cd5e6025
-/
@[simp] theorem inv_a (z : Heis δ d) : z⁻¹.a = -z.a + pair δ d z.k z.h := rfl
/--
@isnad1 id=eq.0h4v.s6.7de10a8e40f1 from=translated src=- shape=f9c00ebf vocab=3bb70224
-/
@[simp] theorem inv_h (z : Heis δ d) : z⁻¹.h = -z.h := rfl
/--
@isnad1 id=eq.0h4v.s6.2b6c48a15e7b from=translated src=- shape=f9c00ebf vocab=247d9cdf
-/
@[simp] theorem inv_k (z : Heis δ d) : z⁻¹.k = -z.k := rfl

instance instGroup : Group (Heis δ d) where
  mul_assoc z z' z'' := by
    refine Heis.ext ?_ ?_ ?_
    · simp only [mul_a, mul_h, mul_k, pair_add_left, pair_add_right]; abel
    · simp only [mul_h]; abel
    · simp only [mul_k]; abel
  one_mul z := by refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_left]
  mul_one z := by refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_right]
  inv_mul_cancel z := by
    refine Heis.ext ?_ ?_ ?_
    · simp only [mul_a, inv_a, inv_k, one_a, pair_neg_left]; abel
    · simp only [mul_h, inv_h, one_h, neg_add_cancel]
    · simp only [mul_k, inv_k, one_k, neg_add_cancel]

instance instFintype [NeZero d] [∀ i, NeZero (δ i)] : Fintype (Heis δ d) :=
  Fintype.ofEquiv (ZMod (2 * d) × HH δ × HH δ)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩, invFun := fun z => ⟨z.a, z.h, z.k⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

instance instDecidableEq : DecidableEq (Heis δ d) := fun z z' =>
  decidable_of_iff (z.a = z'.a ∧ z.h = z'.h ∧ z.k = z'.k)
    ⟨fun hh => Heis.ext hh.1 hh.2.1 hh.2.2, fun hh => by subst hh; exact ⟨rfl, rfl, rfl⟩⟩

def cen (a : ZMod (2 * d)) : Heis δ d := ⟨a, 0, 0⟩

/--
@isnad1 id=eq.0h4v.s5.060b4363e9d5 from=translated src=- shape=0813b726 vocab=075ddd08
-/
@[simp] theorem cen_a (a : ZMod (2 * d)) : (cen a : Heis δ d).a = a := rfl
/--
@isnad1 id=eq.0h4v.s6.6a5fdc0bb9f2 from=translated src=- shape=0b3b3026 vocab=5cba8778
-/
@[simp] theorem cen_h (a : ZMod (2 * d)) : (cen a : Heis δ d).h = 0 := rfl
/--
@isnad1 id=eq.0h4v.s6.c2db6418fe36 from=translated src=- shape=0b3b3026 vocab=492757da
-/
@[simp] theorem cen_k (a : ZMod (2 * d)) : (cen a : Heis δ d).k = 0 := rfl

/--
@isnad1 id=eq.0h5v.s7.ac2d1e1b8041 from=translated src=- shape=22df897d vocab=db51b1ce
-/
theorem cen_mul (a : ZMod (2 * d)) (z : Heis δ d) : cen a * z = ⟨a + z.a, z.h, z.k⟩ := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, pair_zero_left]

/--
@isnad1 id=eq.0h5v.s7.d9d8eb050a67 from=translated src=- shape=6ff32e0d vocab=db51b1ce
-/
theorem mul_cen (a : ZMod (2 * d)) (z : Heis δ d) : z * cen a = ⟨z.a + a, z.h, z.k⟩ := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, pair_zero_right]

def theta (h : HH δ) : Heis δ d := ⟨0, h, 0⟩

def eta (k : HH δ) : Heis δ d := ⟨0, 0, k⟩

/--
@isnad1 id=eq.0h4v.s7.f57a80dd9fc9 from=translated src=- shape=2974c273 vocab=17f980c8
-/
@[simp] theorem theta_a (h : HH δ) : (theta h : Heis δ d).a = 0 := rfl
/--
@isnad1 id=eq.0h4v.s4.05e2a1e91a78 from=translated src=- shape=05bd24c4 vocab=e613be12
-/
@[simp] theorem theta_h (h : HH δ) : (theta h : Heis δ d).h = h := rfl
/--
@isnad1 id=eq.0h4v.s6.f1af5f82f68f from=translated src=- shape=6307e99e vocab=bcd9e2d7
-/
@[simp] theorem theta_k (h : HH δ) : (theta h : Heis δ d).k = 0 := rfl
/--
@isnad1 id=eq.0h4v.s7.0e424fcf8112 from=translated src=- shape=2974c273 vocab=38866129
-/
@[simp] theorem eta_a (k : HH δ) : (eta k : Heis δ d).a = 0 := rfl
/--
@isnad1 id=eq.0h4v.s6.471a8a020c68 from=translated src=- shape=6307e99e vocab=5657f8df
-/
@[simp] theorem eta_h (k : HH δ) : (eta k : Heis δ d).h = 0 := rfl
/--
@isnad1 id=eq.0h4v.s4.77a37f4062dc from=translated src=- shape=05bd24c4 vocab=614a0923
-/
@[simp] theorem eta_k (k : HH δ) : (eta k : Heis δ d).k = k := rfl

/--
@isnad1 id=eq.0h4v.s6.f82adad78049 from=translated src=- shape=296909c3 vocab=e38ffeb3
-/
theorem cen_mul_theta_mul_eta (z : Heis δ d) : cen z.a * theta z.h * eta z.k = z := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, theta, eta, pair_zero_left, pair_zero_right]

/--
@isnad1 id=eq.0h5v.s6.8cf1b6e8b135 from=translated src=- shape=cf12d639 vocab=752d588d
-/
theorem eta_mul_theta (h k : HH δ) : (eta k * theta h : Heis δ d) = cen (pair δ d k h) * theta h * eta k := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, theta, eta, pair_zero_left, pair_zero_right]

variable (δ d) in

def Gam : Subgroup (MulAut (Heis δ d)) where
  carrier := {γ | ∀ a, γ (cen a) = cen a}
  mul_mem' := by
    intro γ γ' hγ hγ' a
    show γ (γ' (cen a)) = cen a
    rw [hγ', hγ]
  one_mem' := by intro a; rfl
  inv_mem' := by
    intro γ hγ a
    show γ.symm (cen a) = cen a
    rw [MulEquiv.symm_apply_eq]
    exact (hγ a).symm

/--
@isnad1 id=finite.0h3v.s7.30acacf8b387 from=translated src=- shape=acd85243 vocab=8e5fc368
-/
instance Gam.instFinite [NeZero d] [∀ i, NeZero (δ i)] : Finite (Gam δ d) := by
  have : Finite (MulAut (Heis δ d)) :=
    Finite.of_injective (fun γ : MulAut (Heis δ d) => γ.toEquiv)
      (fun _ _ hh => MulEquiv.ext (fun x => congrFun (congrArg (⇑) hh) x))
  infer_instance

instance Gam.instFintype [NeZero d] [∀ i, NeZero (δ i)] : Fintype (Gam δ d) :=
  Fintype.ofFinite _

end Heis

end Heis

section Schrodinger

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

def omegaPow (a : ZMod (2 * d)) : B := ω ^ a.val

omit [NeZero d] in
/--
@isnad1 id=eq.0h3v.s7.328f32843201 from=translated src=- shape=b291797b vocab=bf70bb66
-/
theorem omegaPow_zero : omegaPow d B ω 0 = 1 := by
  simp [omegaPow]

/--
@isnad1 id=eq.1h4v.s6.3f56d16f03e4 from=translated src=- shape=96f5f6f1 vocab=87c448d2
-/
theorem omegaPow_aux_pow_mod_eq {M : Type} [Monoid M] (x : M) {m : ℕ} (hx : x ^ m = 1) (n : ℕ) :
    x ^ (n % m) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hx, one_pow, mul_one]

/--
@isnad1 id=eq.1h5v.s8.c4470e6c8650 from=translated src=- shape=0b521ea0 vocab=d70d127f
-/
theorem omegaPow_add (hω : ω ^ (2 * d) = 1) (a b : ZMod (2 * d)) :
    omegaPow d B ω (a + b) = omegaPow d B ω a * omegaPow d B ω b := by
  simp only [omegaPow]
  rw [ZMod.val_add, omegaPow_aux_pow_mod_eq ω hω, pow_add]

omit [NeZero d] in
/--
@isnad1 id=eq.1h4v.s7.44bccda3c81c from=translated src=- shape=19c3f1e6 vocab=9004d919
-/
theorem omegaPow_natCast (hω : ω ^ (2 * d) = 1) (n : ℕ) :
    omegaPow d B ω (n : ZMod (2 * d)) = ω ^ n := by
  simp only [omegaPow]
  rw [ZMod.val_natCast, omegaPow_aux_pow_mod_eq ω hω]

def thetaChar (k : HH δ) : HH δ → B := fun h => omegaPow d B ω (pair δ d k h)

def shiftOp (h : HH δ) : (HH δ → B) →ₗ[B] (HH δ → B) := LinearMap.funLeft B B (fun x => x - h)

def diagOp (c : HH δ → B) : (HH δ → B) →ₗ[B] (HH δ → B) := LinearMap.mulLeft B c

/--
@isnad1 id=eq.0h6v.s8.8aac9cb755b3 from=translated src=- shape=0d647695 vocab=eb272f8c
-/
@[simp] theorem shiftOp_apply (h : HH δ) (v : HH δ → B) (x : HH δ) : shiftOp δ B h v x = v (x - h) := rfl

/--
@isnad1 id=eq.0h6v.s8.b106a7aa700c from=translated src=- shape=8d0e5192 vocab=8921cb3c
-/
@[simp] theorem diagOp_apply (c : HH δ → B) (v : HH δ → B) (x : HH δ) : diagOp δ B c v x = c x * v x := rfl

def schrod (z : Heis δ d) : (HH δ → B) →ₗ[B] (HH δ → B) :=
  omegaPow d B ω z.a • (shiftOp δ B z.h ∘ₗ diagOp δ B (thetaChar δ d B ω z.k))

omit [NeZero d] in
/--
@isnad1 id=eq.0h8v.s8.e49b0c2472dc from=translated src=- shape=37f949dd vocab=65de4201
-/
theorem schrod_apply (z : Heis δ d) (v : HH δ → B) (x : HH δ) :
    schrod δ d B ω z v x = omegaPow d B ω z.a * (thetaChar δ d B ω z.k (x - z.h) * v (x - z.h)) := by
  simp [schrod]

/--
@isnad1 id=eq.1h7v.s8.bbf5d95ef2c8 from=translated src=- shape=5514a332 vocab=89cc1e6a
-/
theorem schrod_mul (hω : ω ^ (2 * d) = 1) (z z' : Heis δ d) :
    schrod δ d B ω (z * z') = schrod δ d B ω z ∘ₗ schrod δ d B ω z' := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp only [LinearMap.comp_apply, schrod_apply, Heis.mul_a, Heis.mul_h, Heis.mul_k, thetaChar,
    pair_add_left]
  have hx : x - (z.h + z'.h) = x - z.h - z'.h := by abel
  rw [hx, show pair δ d z.k (x - z.h - z'.h) = pair δ d z.k (x - z.h) + -pair δ d z.k z'.h by
    rw [sub_eq_add_neg (x - z.h), pair_add_right, pair_neg_right]]
  simp only [omegaPow_add d B ω hω]

  have hcancel : omegaPow d B ω (pair δ d z.k z'.h) * omegaPow d B ω (-pair δ d z.k z'.h) = 1 := by
    rw [← omegaPow_add d B ω hω, add_neg_cancel, omegaPow_zero]

  set A := omegaPow d B ω z.a
  set A' := omegaPow d B ω z'.a
  set P := omegaPow d B ω (pair δ d z.k z'.h)
  set Q := omegaPow d B ω (-pair δ d z.k z'.h)
  set R1 := omegaPow d B ω (pair δ d z.k (x - z.h))
  set R2 := omegaPow d B ω (pair δ d z'.k (x - z.h - z'.h))
  set w := v (x - z.h - z'.h)
  calc A * A' * P * (R1 * Q * R2 * w) = (P * Q) * (A * (R1 * (A' * (R2 * w)))) := by ring
    _ = A * (R1 * (A' * (R2 * w))) := by rw [hcancel, one_mul]

omit [NeZero d] in
/--
@isnad1 id=eq.0h5v.s7.ee0b856c7e4a from=translated src=- shape=77ad198f vocab=58022898
-/
theorem schrod_one : schrod δ d B ω 1 = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp [schrod_apply, thetaChar, pair_zero_left, omegaPow_zero]

def schrodHom (hω : ω ^ (2 * d) = 1) : Heis δ d →* Module.End B (HH δ → B) where
  toFun := schrod δ d B ω
  map_one' := schrod_one δ d B ω
  map_mul' z z' := by rw [schrod_mul δ d B ω hω]; rfl

end Schrodinger

section Matrices

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) (B : Type) [CommRing B] (ω : B) {n : ℕ} (e : Fin n ≃ HH δ)

def schrodMat (z : Heis δ d) : Matrix (Fin n) (Fin n) B :=
  fun i j => if e i = e j + z.h then omegaPow d B ω (z.a + pair δ d z.k (e j)) else 0

/--
@isnad1 id=eq.0h10v.s9.b23949cb5a7d from=translated src=- shape=87ba3ebd vocab=3c63f030
-/
theorem schrodMat_apply (z : Heis δ d) (i j : Fin n) :
    schrodMat δ d B ω e z i j = if e i = e j + z.h then omegaPow d B ω (z.a + pair δ d z.k (e j)) else 0 := rfl

def IsIntertwiner (γ : MulAut (Heis δ d)) (U : Matrix (Fin n) (Fin n) B) : Prop :=
  IsUnit U ∧ ∀ z : Heis δ d, U * schrodMat δ d B ω e z = schrodMat δ d B ω e (γ z) * U

def inter (γ : MulAut (Heis δ d)) : Matrix (Fin n) (Fin n) B := by
  classical
  exact if hU : ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U then hU.choose else 1

/--
@isnad1 id=isintert.1h8v.s6.4fba43861aec from=translated src=- shape=d780fe37 vocab=ec986e82
-/
theorem isIntertwiner_inter (γ : MulAut (Heis δ d)) (hU : ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U) :
    IsIntertwiner δ d B ω e γ (inter δ d B ω e γ) := by
  classical
  rw [inter, dite_eq_left hU]
  exact hU.choose_spec

/--
@isnad1 id=eq.1h8v.s6.ae3612c8c063 from=translated src=- shape=1d7373fe vocab=ec986e82
-/
theorem inter_of_not_exists (γ : MulAut (Heis δ d)) (hU : ¬ ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U) :
    inter δ d B ω e γ = 1 := by
  classical
  rw [inter, dite_eq_right hU]

end Matrices

end AlgebraicGeometry.ThetaLevel

end
