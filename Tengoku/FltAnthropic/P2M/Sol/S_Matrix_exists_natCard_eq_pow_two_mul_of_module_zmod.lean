import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_exists_natCard_eq_pow_two_mul_of_module_zmod

set_option autoImplicit false

open scoped Quaternion

namespace ASM21
namespace M2

variable {ℓ : ℕ}

def e (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![1, 0; 0, 0]

def f (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![0, 0; 0, 1]

def w (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![0, 1; 1, 0]

/--
@isnad1 id=eq.0h1v.s7.963e3afed5f7 from=translated src=- shape=8af0ebad vocab=73a93923
-/
theorem e_add_f : e ℓ + f ℓ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e, f]
/--
@isnad1 id=eq.0h1v.s6.cde0f69d8c22 from=translated src=- shape=178ba449 vocab=f93f5e57
-/
theorem e_mul_e : e ℓ * e ℓ = e ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e, Matrix.mul_apply, Fin.sum_univ_two]
/--
@isnad1 id=eq.0h1v.s7.2e8980a90bbf from=translated src=- shape=8af0ebad vocab=88bf52be
-/
theorem f_mul_e : f ℓ * e ℓ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e, f, Matrix.mul_apply, Fin.sum_univ_two]
/--
@isnad1 id=eq.0h1v.s7.1e884b54bc2f from=translated src=- shape=8af0ebad vocab=f35ccb9f
-/
theorem w_mul_w : w ℓ * w ℓ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]
/--
@isnad1 id=eq.0h1v.s7.4da3832cf406 from=translated src=- shape=4eaea968 vocab=011381de
-/
theorem w_mul_e : w ℓ * e ℓ = f ℓ * w ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]
/--
@isnad1 id=eq.0h1v.s7.25f0b6c3eefb from=translated src=- shape=cddfbc8e vocab=011381de
-/
theorem e_mul_w : e ℓ * w ℓ = w ℓ * f ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s9.584ad86631e7 from=translated src=- shape=e476e0a3 vocab=fbfcc91b
-/
theorem decomp (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :
    X = X 0 0 • e ℓ + X 0 1 • (e ℓ * w ℓ) + X 1 0 • (w ℓ * e ℓ) + X 1 1 • f ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]

end ASM21.M2

namespace ASM21
namespace M2

section module
variable {ℓ : ℕ} (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V]

def sc (c : ZMod ℓ) (v : V) : V := (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) c) • v

/--
@isnad1 id=eq.0h5v.s9.bf248fbad87d from=translated src=- shape=7725bfbf vocab=36b7368b
-/
theorem smul_matrix_smul (c : ZMod ℓ) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (v : V) : (c • X) • v = sc V c (X • v) := by
  rw [Algebra.smul_def, mul_smul]; rfl

/--
@isnad1 id=eq.0h5v.s9.eed6ed598c3a from=translated src=- shape=8fac1ffc vocab=36b7368b
-/
theorem X_sc (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (c : ZMod ℓ) (v : V) : X • sc V c v = sc V c (X • v) := by
  show X • ((algebraMap (ZMod ℓ) _ c) • v) = (algebraMap (ZMod ℓ) _ c) • (X • v)
  rw [← mul_smul, ← mul_smul, Algebra.commutes]

/--
@isnad1 id=eq.0h3v.s6.419cee91bdeb from=translated src=- shape=9fca410e vocab=f5af4cb8
-/
theorem sc_zero (c : ZMod ℓ) : sc V c (0 : V) = 0 := smul_zero _
/--
@isnad1 id=eq.0h5v.s6.7b1e61a54c25 from=translated src=- shape=46592251 vocab=aa65e551
-/
theorem mul_sc (c d : ZMod ℓ) (v : V) : sc V (c * d) v = sc V c (sc V d v) := by
  show (algebraMap (ZMod ℓ) _ (c * d)) • v = _; rw [map_mul, mul_smul]; rfl
/--
@isnad1 id=eq.0h3v.s6.3efbd2911631 from=translated src=- shape=5b72bc31 vocab=f5af4cb8
-/
theorem one_sc (v : V) : sc V (1 : ZMod ℓ) v = v := by
  show (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) 1) • v = v; rw [map_one, one_smul]
/--
@isnad1 id=eq.0h3v.s6.b73d8b103c00 from=translated src=- shape=57323f8d vocab=f5af4cb8
-/
theorem zero_sc (v : V) : sc V (0 : ZMod ℓ) v = 0 := by
  show (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) 0) • v = 0; rw [map_zero, zero_smul]
/--
@isnad1 id=eq.0h4v.s6.6e122017b147 from=translated src=- shape=2fc04f96 vocab=ef42b84d
-/
theorem neg_sc (c : ZMod ℓ) (v : V) : sc V (-c) v = -(sc V c v) := by
  show (algebraMap (ZMod ℓ) _ (-c)) • v = _; rw [map_neg, neg_smul]; rfl

/--
@isnad1 id=eq.0h3v.s8.64ce7607d8a4 from=translated src=- shape=b15c929b vocab=05a2b6c4
-/
theorem e_add_f_smul (v : V) : e ℓ • v + f ℓ • v = v := by rw [← add_smul, e_add_f, one_smul]
/--
@isnad1 id=eq.0h3v.s9.287fdb666464 from=translated src=- shape=f834ebb9 vocab=19eab176
-/
theorem e_e (v : V) : e ℓ • (e ℓ • v) = e ℓ • v := by rw [← mul_smul, e_mul_e]
/--
@isnad1 id=eq.0h3v.s8.656e5ffc5698 from=translated src=- shape=a538f934 vocab=ebda869e
-/
theorem f_e (v : V) : f ℓ • (e ℓ • v) = 0 := by rw [← mul_smul, f_mul_e, zero_smul]
/--
@isnad1 id=eq.0h3v.s8.cb8caa9eda93 from=translated src=- shape=22b07864 vocab=ae0aed44
-/
theorem w_w (v : V) : w ℓ • (w ℓ • v) = v := by rw [← mul_smul, w_mul_w, one_smul]
/--
@isnad1 id=eq.0h3v.s9.b8a561b983fc from=translated src=- shape=c7799b3c vocab=91dbdd4e
-/
theorem w_e (v : V) : w ℓ • (e ℓ • v) = f ℓ • (w ℓ • v) := by rw [← mul_smul, w_mul_e, mul_smul]
/--
@isnad1 id=eq.0h3v.s9.56727502b497 from=translated src=- shape=aa344622 vocab=91dbdd4e
-/
theorem e_w (v : V) : e ℓ • (w ℓ • v) = w ℓ • (f ℓ • v) := by rw [← mul_smul, e_mul_w, mul_smul]

/--
@isnad1 id=eq.1h3v.s9.b7ed153801d9 from=translated src=- shape=b4a34eb0 vocab=625dd1af
-/
theorem e_w_of_e {v : V} (hv : e ℓ • v = v) : e ℓ • (w ℓ • v) = 0 := by
  rw [e_w, ← hv, f_e, smul_zero]
/--
@isnad1 id=eq.1h3v.s8.311fcee37055 from=translated src=- shape=979a7616 vocab=ebda869e
-/
theorem f_of_e {v : V} (hv : e ℓ • v = v) : f ℓ • v = 0 := by rw [← hv, f_e]
/--
@isnad1 id=eq.1h3v.s9.ffa2881a2237 from=translated src=- shape=908f4e24 vocab=91dbdd4e
-/
theorem f_w_of_e {v : V} (hv : e ℓ • v = v) : f ℓ • (w ℓ • v) = w ℓ • v := by
  rw [← w_e, hv]

def split : V ≃ {v : V // e ℓ • v = v} × {v : V // e ℓ • v = v} where
  toFun v := (⟨e ℓ • v, e_e V v⟩, ⟨e ℓ • (w ℓ • v), e_e V _⟩)
  invFun p := (p.1 : V) + w ℓ • (p.2 : V)
  left_inv v := by
    show e ℓ • v + w ℓ • (e ℓ • (w ℓ • v)) = v
    rw [e_w, w_w, e_add_f_smul]
  right_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [smul_add, hx, e_w_of_e V hy, add_zero]
    · rw [smul_add, smul_add, e_w_of_e V hx, zero_add, w_w, hy]

/--
@isnad1 id=eq.1h2v.s8.ad6cf84d7a21 from=translated src=- shape=49d5abbd vocab=66d6a871
-/
theorem natCard_eFixed [Fact ℓ.Prime] [Finite V] (hV : Nat.card V = ℓ ^ 4) : Nat.card {v : V // e ℓ • v = v} = ℓ ^ 2 := by
  have h := Nat.card_congr (split V (ℓ := ℓ))
  rw [Nat.card_prod, hV] at h
  have : (Nat.card {v : V // e ℓ • v = v}) ^ 2 = (ℓ ^ 2) ^ 2 := by rw [sq, ← h]; ring
  exact Nat.pow_left_injective two_ne_zero this

/--
@isnad1 id=ex.1h2v.s9.a24d8333c8fe from=translated src=- shape=2ed27122 vocab=6afdb43c
-/
theorem exists_indep [Fact ℓ.Prime] [Finite V] (hV : Nat.card V = ℓ ^ 4) :
    ∃ v₁ v₂ : V, e ℓ • v₁ = v₁ ∧ e ℓ • v₂ = v₂ ∧
      ∀ α β : ZMod ℓ, sc V α v₁ + sc V β v₂ = 0 → α = 0 ∧ β = 0 := by
  classical
  have hcard := natCard_eFixed V hV
  have hℓ : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have h1 : 1 < Nat.card {v : V // e ℓ • v = v} := by
    rw [hcard]; exact Nat.one_lt_pow two_ne_zero hℓ
  haveI : Nontrivial {v : V // e ℓ • v = v} := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨v₁, hv₁⟩, hne⟩ := exists_ne (⟨0, smul_zero _⟩ : {v : V // e ℓ • v = v})
  have hv₁0 : v₁ ≠ 0 := fun h => hne (Subtype.ext h)
  let line : ZMod ℓ → {v : V // e ℓ • v = v} := fun c => ⟨sc V c v₁, by rw [X_sc, hv₁]⟩
  have hlt : Nat.card (Set.range line) < Nat.card {v : V // e ℓ • v = v} := by
    calc Nat.card (Set.range line) ≤ Nat.card (ZMod ℓ) := Finite.card_range_le line
      _ = ℓ := by rw [Nat.card_eq_fintype_card, ZMod.card]
      _ < ℓ ^ 2 := by nlinarith
      _ = _ := hcard.symm
  have hnot : ∃ v₂ : {v : V // e ℓ • v = v}, v₂ ∉ Set.range line := by
    by_contra h
    push_neg at h
    have : Set.range line = Set.univ := Set.eq_univ_of_forall h
    rw [this, Nat.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨⟨v₂, hv₂⟩, hv₂n⟩ := hnot
  refine ⟨v₁, v₂, hv₁, hv₂, fun α β hαβ => ?_⟩
  by_cases hβ : β = 0
  · refine ⟨?_, hβ⟩
    rw [hβ, zero_sc, add_zero] at hαβ
    by_contra hα
    apply hv₁0
    have := congrArg (sc V α⁻¹) hαβ
    rwa [← mul_sc, inv_mul_cancel₀ hα, one_sc, sc_zero] at this
  · exfalso
    apply hv₂n
    have h2 : sc V β v₂ = -(sc V α v₁) := eq_neg_of_add_eq_zero_right hαβ
    have h3 : v₂ = sc V (-(β⁻¹ * α)) v₁ := by
      have := congrArg (sc V β⁻¹) h2
      rw [← mul_sc, inv_mul_cancel₀ hβ, one_sc] at this
      rw [this, ← neg_sc, ← mul_sc, neg_mul_eq_mul_neg]
    exact ⟨-(β⁻¹ * α), Subtype.ext h3.symm⟩

theorem eq_zero_of_smul_gen_eq_zero [Fact ℓ.Prime] {v₁ v₂ : V} (hv₁ : e ℓ • v₁ = v₁) (hv₂ : e ℓ • v₂ = v₂)
    (hind : ∀ α β : ZMod ℓ, sc V α v₁ + sc V β v₂ = 0 → α = 0 ∧ β = 0)
    (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (hX : X • (v₁ + w ℓ • v₂) = 0) : X = 0 := by
  have a2 : (e ℓ * w ℓ) • v₁ = 0 := by rw [mul_smul, e_w_of_e V hv₁]
  have a3 : (w ℓ * e ℓ) • v₁ = w ℓ • v₁ := by rw [mul_smul, hv₁]
  have a4 : f ℓ • v₁ = 0 := f_of_e V hv₁
  have b1 : e ℓ • (w ℓ • v₂) = 0 := e_w_of_e V hv₂
  have b2 : (e ℓ * w ℓ) • (w ℓ • v₂) = v₂ := by rw [mul_smul, w_w, hv₂]
  have b3 : (w ℓ * e ℓ) • (w ℓ • v₂) = 0 := by rw [mul_smul, e_w_of_e V hv₂, smul_zero]
  have b4 : f ℓ • (w ℓ • v₂) = w ℓ • v₂ := f_w_of_e V hv₂
  have h0 := hX
  rw [decomp X] at h0
  simp only [add_smul, smul_add, smul_matrix_smul, hv₁, a2, a3, a4, b1, b2, b3, b4, sc_zero, add_zero, zero_add] at h0

  have he := congrArg (fun t => e ℓ • t) h0
  simp only [smul_add, smul_zero, X_sc, hv₁, hv₂, e_w_of_e V hv₁, e_w_of_e V hv₂, sc_zero, add_zero, zero_add] at he
  obtain ⟨ha, hb⟩ := hind _ _ he

  have hf := congrArg (fun t => w ℓ • (f ℓ • t)) h0
  simp only [smul_add, smul_zero, X_sc, a4, f_of_e V hv₂, b4, f_w_of_e V hv₁, w_w, sc_zero, add_zero, zero_add] at hf
  obtain ⟨hc, hd⟩ := hind _ _ hf
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

end module

end ASM21.M2

namespace ASM21
namespace M2A
open ASM21.M2

variable {ℓ : ℕ}

/--
@isnad1 id=ex.1h2v.s6.d9e9cd6d354f from=translated src=- shape=250be9ed vocab=0994de9d
-/
theorem exists_natCard_eq_pow (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Finite W] (hW : ∀ w : W, ℓ • w = 0) :
    ∃ n : ℕ, Nat.card W = ℓ ^ n := by
  have hp : IsPGroup ℓ (Multiplicative W) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    change Multiplicative.ofAdd ((ℓ : ℕ) • Multiplicative.toAdd g) = Multiplicative.ofAdd 0
    rw [hW]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  exact ⟨n, by rw [← hn]; exact Nat.card_congr Multiplicative.ofAdd⟩

variable (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V]

def eFixed : AddSubgroup V where
  carrier := {v | e ℓ • v = v}
  zero_mem' := smul_zero _
  add_mem' := by intro u v hu hv; show e ℓ • (u + v) = u + v; rw [smul_add, hu, hv]
  neg_mem' := by intro v hv; show e ℓ • (-v) = -v; rw [smul_neg, hv]

/--
@isnad1 id=eq.0h3v.s6.a9a621d9a705 from=translated src=- shape=e25d5a1f vocab=337f030a
-/
theorem nsmul_eq_zero [Fact ℓ.Prime] (v : V) : ℓ • v = 0 := by
  have h : ((ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [← Nat.cast_smul_eq_nsmul (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ℓ v, h, zero_smul]

/--
@isnad1 id=ex.0h2v.s6.a76a0486504f from=translated src=- shape=9c6c14ba vocab=9419c64a
-/
theorem main [Fact ℓ.Prime] [Finite V] : ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k) := by
  classical
  have hsplit : Nat.card V = Nat.card (eFixed V (ℓ := ℓ)) * Nat.card (eFixed V (ℓ := ℓ)) := by
    rw [Nat.card_congr (split V (ℓ := ℓ)), Nat.card_prod]; rfl
  haveI : Finite (eFixed V (ℓ := ℓ)) := inferInstance
  obtain ⟨j, hj⟩ := exists_natCard_eq_pow ℓ (eFixed V (ℓ := ℓ)) (fun w => by
    apply Subtype.ext
    show ((ℓ • w : eFixed V (ℓ := ℓ)) : V) = 0
    rw [AddSubgroup.coe_nsmul]; exact nsmul_eq_zero V (w : V))
  exact ⟨j, by rw [hsplit, hj, ← pow_add, two_mul]⟩

end ASM21.M2A

/--
@isnad1 id=ex.0h2v.s6.9ee147c6dcb0 from=translated src=- shape=f8d8de70 vocab=9419c64a
-/
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V] :
    ∃ k : ℕ, Nat.card V = ℓ ^ (2 * k) := by
  exact ASM21.M2A.main V
