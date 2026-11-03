module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.RelPres.HNN

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-generator embedding, Checkpoint I: free families and the general HNN extension

Let `G` be any group and `x : ℕ → G` any sequence (repetitions, identity elements and torsion
are allowed).  Write `F₂ = FreeGroup (Fin 2)` with `a = of 0`, `b = of 1`, and
`Q = G ∗ F₂` (Mathlib's `Monoid.Coprod`).

* `conjFam p q : FreeGroup ℕ →* F₂`, `z_i ↦ (of p ^ i)⁻¹ * of q * of p ^ i`; for `p ≠ q` it is
  injective (`conjFam_injective`).  The proof uses the ascending HNN extension of the shift
  `z_i ↦ z_(i+1)` of `FreeGroup ℕ` and its base injectivity; no normal-form theorem is needed.
* `uHom : FreeGroup ℕ →* Q`, `u_i = a^(-i) b a^i`, and
  `vHom x : FreeGroup ℕ →* Q`, `v_0 = a`, `v_(n+1) = x_n b^(-(n+1)) a b^(n+1)`; both injective.
* `thetaEquiv x : range u ≃* range v` with `θ (u w) = v w`.
* `HX x` — the general HNN extension of `Q` along `θ`, with Mathlib's convention
  `t * of c = of (θ c) * t`, so `t u_i t⁻¹ = v_i`.
* `baseHX x : G →* HX x` is injective, and the explicit formulas
  `a = t b t⁻¹` (`HX_a_eq`) and `x_n = wVal b t (n+1)` (`HX_x_eq`), where
  `wVal B T m = T A^(-m) B A^m T⁻¹ B^(-m) A⁻¹ B^m` with `A = T B T⁻¹`.
-/

@[expose] public section

namespace TheoremA.RelPres

open HNNExtension

universe u

/-! ### The conjugate family in `F₂` -/

/-- The conjugate family `z_i ↦ (of p ^ i)⁻¹ * of q * of p ^ i`.-/
def conjFam (p q : Fin 2) : FreeGroup ℕ →* FreeGroup (Fin 2) :=
  FreeGroup.lift fun i => (FreeGroup.of p ^ i)⁻¹ * FreeGroup.of q * FreeGroup.of p ^ i

/--
@isnad1 id=eq.0h3v.s8.1a9767fa6a5b from=translated src=- shape=7ff74929 vocab=def7ee64
-/
@[simp] theorem conjFam_of (p q : Fin 2) (i : ℕ) :
    conjFam p q (FreeGroup.of i) =
      (FreeGroup.of p ^ i)⁻¹ * FreeGroup.of q * FreeGroup.of p ^ i := by
  simp [conjFam]

/-- The shift `z_i ↦ z_(i+1)` of `FreeGroup ℕ`.-/
def shiftHom : FreeGroup ℕ →* FreeGroup ℕ := FreeGroup.map Nat.succ

/--
@isnad1 id=injectiv.0h0v.s6.ff816de9d915 from=translated src=- shape=22d3d268 vocab=16b52dbe
-/
theorem shiftHom_injective : Function.Injective shiftHom := by
  have h : (FreeGroup.map Nat.pred).comp shiftHom = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ fun i => by simp [shiftHom]
  exact Function.LeftInverse.injective (g := FreeGroup.map Nat.pred)
    fun w => DFunLike.congr_fun h w

/-- In the ascending HNN extension of the shift, `t^i z_0 t^(-i) = z_i`.
@isnad1 id=eq.0h1v.s13.dea61789252f from=translated src=- shape=f8f5c3cb vocab=871cba59
-/
theorem shiftHNN_conj_pow (i : ℕ) :
    (t : ascHNN shiftHom shiftHom_injective) ^ i * of (FreeGroup.of 0) * (t ^ i)⁻¹ =
      of (FreeGroup.of i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_inv_rev, show ∀ a b c d : ascHNN shiftHom shiftHom_injective,
      a * b * c * (d * a⁻¹) = a * (b * c * d) * a⁻¹ from fun a b c d => by group, ih,
      ascHNN_conj]
    simp [shiftHom]

/-- **The conjugate family is free** (for two distinct letters).
@isnad1 id=injectiv.1h2v.s7.4db3c0fee41f from=translated src=- shape=c90e0572 vocab=480c9ab9
-/
theorem conjFam_injective {p q : Fin 2} (hpq : p ≠ q) : Function.Injective (conjFam p q) := by
  let E := ascHNN shiftHom shiftHom_injective
  let ev : FreeGroup (Fin 2) →* E :=
    FreeGroup.lift fun k => if k = p then (t : E)⁻¹ else of (FreeGroup.of 0)
  have h : ev.comp (conjFam p q) = (of : FreeGroup ℕ →* E) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp only [MonoidHom.comp_apply, conjFam_of, map_mul, map_inv, map_pow, ev,
      FreeGroup.lift_apply_of, ite_eq_right (Ne.symm hpq), ite_true, inv_pow]
    rw [inv_inv]
    exact shiftHNN_conj_pow i
  intro v w hvw
  apply HNNExtension.of_injective (G := FreeGroup ℕ) _
  rw [← h, MonoidHom.comp_apply, MonoidHom.comp_apply, hvw]

/-! ### The two families in `Q = G ∗ F₂` -/

section Families

variable {G : Type u} [Group G] (x : ℕ → G)

/-- The group `Q = G ∗ F(a,b)`.-/
abbrev QGrp (G : Type u) [Group G] : Type u := Monoid.Coprod G (FreeGroup (Fin 2))

/-- The `u`-family `u_i = a^(-i) b a^i` in `Q`.-/
def uHom (G : Type u) [Group G] : FreeGroup ℕ →* QGrp G :=
  Monoid.Coprod.inr.comp (conjFam 0 1)

/-- Generators of the `v`-family: `v_0 = a`, `v_(n+1) = x_n b^(-(n+1)) a b^(n+1)`.-/
def vGen : ℕ → QGrp G
  | 0 => Monoid.Coprod.inr (FreeGroup.of 0)
  | n + 1 => Monoid.Coprod.inl (x n) * Monoid.Coprod.inr
      ((FreeGroup.of 1 ^ (n + 1))⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 ^ (n + 1))

/-- The `v`-family homomorphism.-/
def vHom : FreeGroup ℕ →* QGrp G := FreeGroup.lift (vGen x)

/--
@isnad1 id=eq.0h2v.s9.2ceb4711b601 from=translated src=- shape=dcf94b1e vocab=baab8fb4
-/
@[simp] theorem uHom_of (i : ℕ) : uHom G (FreeGroup.of i) =
    Monoid.Coprod.inr ((FreeGroup.of 0 ^ i)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 ^ i) := by
  simp [uHom]

/--
@isnad1 id=eq.0h3v.s7.6cfa69306486 from=translated src=- shape=fd1954ad vocab=aa517ac0
-/
@[simp] theorem vHom_of (i : ℕ) : vHom x (FreeGroup.of i) = vGen x i := by simp [vHom]

/--
@isnad1 id=injectiv.0h1v.s7.a346acd687e3 from=translated src=- shape=716d50d3 vocab=cd20fd8e
-/
theorem uHom_injective : Function.Injective (uHom G) :=
  Monoid.Coprod.inr_injective.comp (conjFam_injective (by decide))

/-- Killing `G` sends the `v`-family to the swapped conjugate family.
@isnad1 id=eq.0h2v.s8.97353e38ae76 from=translated src=- shape=d8fdfdf6 vocab=15e62391
-/
theorem snd_comp_vHom : Monoid.Coprod.snd.comp (vHom x) = conjFam 1 0 := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  cases i <;> simp [vGen]

/--
@isnad1 id=injectiv.0h2v.s7.f5ac32be5f44 from=translated src=- shape=2b01c053 vocab=220381a3
-/
theorem vHom_injective : Function.Injective (vHom x) := by
  intro v w h
  apply conjFam_injective (p := 1) (q := 0) (by decide)
  rw [← snd_comp_vHom x, MonoidHom.comp_apply, MonoidHom.comp_apply, h]

/-- The isomorphism `θ : range u ≃* range v`, `θ (u w) = v w`.-/
noncomputable def thetaEquiv : (uHom G).range ≃* (vHom x).range :=
  (MonoidHom.ofInjective (uHom_injective (G := G))).symm.trans
    (MonoidHom.ofInjective (vHom_injective x))

/--
@isnad1 id=eq.0h3v.s11.6b8d4aa843d8 from=translated src=- shape=0e28598f vocab=ecd13dd2
-/
theorem thetaEquiv_apply (w : FreeGroup ℕ) :
    ((thetaEquiv x ⟨uHom G w, w, rfl⟩ : (vHom x).range) : QGrp G) = vHom x w := by
  have : (MonoidHom.ofInjective (uHom_injective (G := G))).symm ⟨uHom G w, w, rfl⟩ = w := by
    rw [MulEquiv.symm_apply_eq]; rfl
  simp only [thetaEquiv, MulEquiv.trans_apply, this]
  rfl

/-- **The general HNN extension** of `Q` along `θ : range u ≃* range v`.-/
abbrev HX : Type u := HNNExtension (QGrp G) (uHom G).range (vHom x).range (thetaEquiv x)

/-- The stable-letter relation on the whole associated subgroup: `t u(w) t⁻¹ = v(w)`.
@isnad1 id=eq.0h3v.s12.f39698d424d1 from=translated src=- shape=210cf214 vocab=b8246f32
-/
theorem HX_conj (w : FreeGroup ℕ) :
    (t : HX x) * of (uHom G w) * t⁻¹ = of (vHom x w) := by
  have h := t_mul_of (φ := thetaEquiv x) ⟨uHom G w, w, rfl⟩
  rw [thetaEquiv_apply] at h
  rw [h, mul_inv_cancel_right]

/-- The embedding `G →* H`.-/
noncomputable def baseHX : G →* HX x := (of : QGrp G →* HX x).comp Monoid.Coprod.inl

/-- **`G` embeds in `H`.**
@isnad1 id=injectiv.0h2v.s8.e47baf2c2a06 from=translated src=- shape=b86949fe vocab=da3d95e7
-/
theorem baseHX_injective : Function.Injective (baseHX x) :=
  (HNNExtension.of_injective _).comp Monoid.Coprod.inl_injective

end Families

/-! ### Explicit generator identities -/

/-- The group expression `W(B,T,m) = T A^(-m) B A^m T⁻¹ B^(-m) A⁻¹ B^m` with `A = T B T⁻¹`.-/
def wVal {K : Type*} [Group K] (B T : K) (m : ℕ) : K :=
  T * ((T * B * T⁻¹) ^ m)⁻¹ * B * (T * B * T⁻¹) ^ m * T⁻¹ * (B ^ m)⁻¹ * (T * B * T⁻¹)⁻¹ * B ^ m

/--
@isnad1 id=eq.0h6v.s7.57f9718b7841 from=translated src=- shape=47a6dc4f vocab=6f93ed8d
-/
theorem map_wVal {K K' : Type*} [Group K] [Group K'] (f : K →* K') (B T : K) (m : ℕ) :
    f (wVal B T m) = wVal (f B) (f T) m := by
  simp [wVal]

section Formulas

variable {G : Type u} [Group G] (x : ℕ → G)

/-- The image of `b` in `H`.-/
noncomputable def bHX : HX x := of (Monoid.Coprod.inr (FreeGroup.of 1))

/-- **`a = t b t⁻¹` in `H`** (the index-zero relation).
@isnad1 id=eq.0h2v.s11.e6d7263737c3 from=translated src=- shape=4d8bb03b vocab=6695edbc
-/
theorem HX_a_eq :
    (of (Monoid.Coprod.inr (FreeGroup.of 0)) : HX x) = t * bHX x * t⁻¹ := by
  have h := HX_conj x (FreeGroup.of 0)
  simp only [uHom_of, vHom_of, vGen, pow_zero, inv_one, one_mul, mul_one] at h
  exact h.symm

/-- **`x_n = t a^(-m) b a^m t⁻¹ b^(-m) a⁻¹ b^m` with `a = t b t⁻¹`, `m = n+1`, in `H`.**
@isnad1 id=eq.0h3v.s8.f7b8eb658753 from=translated src=- shape=fa52a6ca vocab=626f2423
-/
theorem HX_x_eq (n : ℕ) : baseHX x (x n) = wVal (bHX x) t (n + 1) := by
  have h := HX_conj x (FreeGroup.of (n + 1))
  have ha := HX_a_eq x
  simp only [uHom_of, vHom_of, vGen, map_mul, map_inv, map_pow] at h
  rw [ha] at h
  unfold bHX at h
  unfold wVal baseHX bHX
  simp only [MonoidHom.comp_apply]
  rw [eq_mul_inv_iff_mul_eq.mpr h.symm]
  group

end Formulas

end TheoremA.RelPres
