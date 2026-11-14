/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.SymplecticMatrix
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.VectorSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/LinearAlgebra/SymplecticBasis.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 辛空间、辛正交补与有限维线性 Darboux 定理

从规范辛对出发，以二维辛平面和辛正交补的直和分解对维数作强归纳。

> **Entry**: linear-algebra.symplectic.basis
-/

namespace SandronesLibrary.LinearAlgebra.SymplecticBasis

universe u

open SandronesLibrary.LinearAlgebra.VectorSpace

variable {E : Type*} [AddCommGroup E] [LinearSpace ℝ E]

/-- 实向量空间上的辛形式：双线性、斜对称且非退化。-/
structure SymplecticForm (E : Type*) [AddCommGroup E] [LinearSpace ℝ E] where
  form : E → E → ℝ
  add_left : ∀ x y z, form (x + y) z = form x z + form y z
  smul_left : ∀ (a : ℝ) x y, form (a • x) y = a * form x y
  skew : ∀ x y, form x y = -form y x
  nondegenerate : ∀ x, (∀ y, form x y = 0) → x = 0

instance : CoeFun (SymplecticForm E) (fun _ => E → E → ℝ) := ⟨SymplecticForm.form⟩

variable (ω : SymplecticForm E)

/-- 辛形式对第二个变量也满足加法性。
@isnad1 id=eq.0h5v.s6.a5e61ac69125 from=translated src=- shape=fbf1515b vocab=694bb72d
-/
theorem add_right (x y z : E) : ω x (y + z) = ω x y + ω x z := by
  rw [ω.skew, ω.add_left, ω.skew y x, ω.skew z x]
  ring

/-- 辛形式对第二个变量也满足齐次性。
@isnad1 id=eq.0h5v.s6.cbe09ccea568 from=translated src=- shape=c4cc53a8 vocab=365e7af7
-/
theorem smul_right (a : ℝ) (x y : E) : ω x (a • y) = a * ω x y := by
  rw [ω.skew, ω.smul_left, ω.skew y x]
  ring

/-- 交替性：任意向量与自身的辛配对为零。
@isnad1 id=eq.0h3v.s5.10b749698e8c from=translated src=- shape=412f213f vocab=6ca54a2c
-/
theorem self_eq_zero (x : E) : ω x x = 0 := by
  have h := ω.skew x x
  linarith

/-- 一个集合的辛正交补。-/
def symplecticOrthogonal (S : Set E) : Set E :=
  {x | ∀ y ∈ S, ω x y = 0}

/-- 零向量属于每个集合的辛正交补。
@isnad1 id=mem.0h3v.s5.4a57cb1ec273 from=translated src=- shape=dfe2348b vocab=3dfed920
-/
theorem zero_mem_symplecticOrthogonal (S : Set E) :
    0 ∈ symplecticOrthogonal ω S := by
  intro y hy
  have h := ω.smul_left 0 0 y
  simpa using h

/-- 辛基：`pᵢ,qᵢ` 合起来构成基，且配对矩阵为标准辛矩阵。-/
def IsSymplecticBasis {n : ℕ} (p q : Fin n → E) : Prop :=
  IsBasis ℝ (Sum.elim p q) ∧
    (∀ i j, ω (p i) (p j) = 0) ∧
    (∀ i j, ω (q i) (q j) = 0) ∧
    (∀ i j, ω (p i) (q j) = if i = j then 1 else 0)

/-- 将教材式辛形式转成证明内部使用的双线性形式。-/
def SymplecticForm.toBilin : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ ω.form ω.add_left ω.smul_left (add_right ω) (smul_right ω)

/--
@isnad1 id=eq.0h4v.s8.4a01b474f74c from=translated src=- shape=500854ff vocab=f79a276f
-/
@[simp] theorem SymplecticForm.toBilin_apply (x y : E) : ω.toBilin x y = ω x y := rfl

private theorem bilin_self_eq_zero (B : LinearMap.BilinForm ℝ E)
    (hskew : ∀ x y, B x y = -B y x) (x : E) : B x x = 0 := by
  have h := hskew x x
  linarith

/-- 非零辛空间中可规范化出一对配对值为 `1` 的向量。-/
private theorem exists_normalized_pair (B : LinearMap.BilinForm ℝ E)
    (hnd : B.Nondegenerate) [Nontrivial E] : ∃ x y, B x y = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hex : ∃ y, B x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (hnd.1 x h)
  obtain ⟨y₀, hy₀⟩ := hex
  refine ⟨x, (B x y₀)⁻¹ • y₀, ?_⟩
  simp [hy₀]

/-- 规范辛对必线性无关。-/
private theorem normalized_pair_linearIndependent (B : LinearMap.BilinForm ℝ E)
    (hskew : ∀ x y, B x y = -B y x) {x y : E} (hxy : B x y = 1) :
    LinearIndependent ℝ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hy := congrArg (fun z => B z y) hab
  have hx := congrArg (fun z => B x z) hab
  simp [hxy, bilin_self_eq_zero B hskew] at hy hx
  constructor <;> linarith

/-- 由规范辛对张成的二维平面上，辛形式仍然非退化。-/
private theorem normalized_plane_nondegenerate (B : LinearMap.BilinForm ℝ E)
    (hskew : ∀ x y, B x y = -B y x) {x y : E} (hxy : B x y = 1) :
    (B.restrict (Submodule.span ℝ ({x, y} : Set E))).Nondegenerate := by
  let W : Submodule ℝ E := Submodule.span ℝ ({x, y} : Set E)
  have hxW : x ∈ W := Submodule.subset_span (by simp)
  have hyW : y ∈ W := Submodule.subset_span (by simp)
  constructor
  · rintro ⟨z, hz⟩ hzero
    obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair.mp hz)
    have hp := hzero ⟨y, hyW⟩
    have hq := hzero ⟨x, hxW⟩
    change B z y = 0 at hp
    change B z x = 0 at hq
    rw [← hab] at hp hq
    have hyx : B y x = -1 := by rw [hskew, hxy]
    simp [hxy, hyx, bilin_self_eq_zero B hskew] at hp hq
    have ha : a = 0 := by linarith
    have hb : b = 0 := by linarith
    apply Subtype.ext
    change z = 0
    rw [← hab, ha, hb]
    simp
  · rintro ⟨z, hz⟩ hzero
    obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair.mp hz)
    have hp := hzero ⟨y, hyW⟩
    have hq := hzero ⟨x, hxW⟩
    change B y z = 0 at hp
    change B x z = 0 at hq
    rw [← hab] at hp hq
    have hyx : B y x = -1 := by rw [hskew, hxy]
    simp [hxy, hyx, bilin_self_eq_zero B hskew] at hp hq
    have ha : a = 0 := by linarith
    have hb : b = 0 := by linarith
    apply Subtype.ext
    change z = 0
    rw [← hab, ha, hb]
    simp

/-- Darboux 递归的一步：剥离一个二维辛平面后，其辛正交补仍然非退化，
并且维数恰好下降二。-/
private theorem split_normalized_plane (B : LinearMap.BilinForm ℝ E)
    (hskew : ∀ x y, B x y = -B y x) (hnd : B.Nondegenerate)
    [IsFiniteDimensional ℝ E] [Nontrivial E] :
    ∃ (x y : E) (W U : Submodule ℝ E),
      B x y = 1 ∧ W = Submodule.span ℝ ({x, y} : Set E) ∧
      U = B.orthogonal W ∧ IsCompl W U ∧
      (B.restrict U).Nondegenerate ∧
      Module.finrank ℝ W = 2 ∧ Module.finrank ℝ U = Module.finrank ℝ E - 2 := by
  obtain ⟨x, y, hxy⟩ := exists_normalized_pair B hnd
  let W : Submodule ℝ E := Submodule.span ℝ ({x, y} : Set E)
  let U : Submodule ℝ E := B.orthogonal W
  have hrefl : B.IsRefl := by
    intro a b hab
    rw [hskew b a, hab, neg_zero]
  have hWnondeg : (B.restrict W).Nondegenerate := by
    simpa [W] using normalized_plane_nondegenerate B hskew hxy
  have hcompl : IsCompl W U := by
    simpa [U] using B.isCompl_orthogonal_of_restrict_nondegenerate hrefl hWnondeg
  have hUorth : B.orthogonal U = W := by
    simpa [U] using B.orthogonal_orthogonal hnd hrefl W
  have hUnondeg : (B.restrict U).Nondegenerate := by
    apply B.nondegenerate_restrict_of_disjoint_orthogonal hrefl
    rw [hUorth]
    exact hcompl.symm.disjoint
  have hlin : LinearIndependent ℝ ![x, y] :=
    normalized_pair_linearIndependent B hskew hxy
  have hWdim : Module.finrank ℝ W = 2 := by
    change Module.finrank ℝ (Submodule.span ℝ ({x, y} : Set E)) = 2
    rw [show ({x, y} : Set E) = Set.range ![x, y] by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp]
    simpa using finrank_span_eq_card hlin
  have hUdim : Module.finrank ℝ U = Module.finrank ℝ E - 2 := by
    rw [show U = B.orthogonal W by rfl, B.finrank_orthogonal hnd, hWdim]
  exact ⟨x, y, W, U, hxy, rfl, rfl, hcompl, hUnondeg, hWdim, hUdim⟩

private def sumInterchange (A B C D : Type*) :
    (A ⊕ B) ⊕ (C ⊕ D) ≃ (A ⊕ C) ⊕ (B ⊕ D) where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl c) => Sum.inl (Sum.inr c)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr c) => Sum.inr (Sum.inl c)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  left_inv z := by rcases z with ⟨a | b⟩ | ⟨c | d⟩ <;> rfl
  right_inv z := by rcases z with ⟨a | c⟩ | ⟨b | d⟩ <;> rfl

/-- 把“一个辛平面”和 `n` 对辛基的指标重新排列为 `n+1` 对。-/
private def darbouxIndexEquiv (n : ℕ) :
    ((Fin 1 ⊕ Fin 1) ⊕ (Fin n ⊕ Fin n)) ≃ (Fin (n + 1) ⊕ Fin (n + 1)) where
  toFun
    | Sum.inl (Sum.inl _) => Sum.inl 0
    | Sum.inl (Sum.inr _) => Sum.inr 0
    | Sum.inr (Sum.inl i) => Sum.inl i.succ
    | Sum.inr (Sum.inr i) => Sum.inr i.succ
  invFun
    | Sum.inl i => Fin.cases (Sum.inl (Sum.inl 0)) (fun j => Sum.inr (Sum.inl j)) i
    | Sum.inr i => Fin.cases (Sum.inl (Sum.inr 0)) (fun j => Sum.inr (Sum.inr j)) i
  left_inv z := by
    rcases z with ⟨a | b⟩ | ⟨c | d⟩
    · exact Fin.eq_zero a ▸ rfl
    · exact Fin.eq_zero b ▸ rfl
    · rfl
    · rfl
  right_inv z := by
    rcases z with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Darboux 递归的拼接步骤：二维辛平面与其正交补的辛基合并后，
得到整个空间的一组辛基。-/
private theorem prepend_normalized_pair
    (B : LinearMap.BilinForm ℝ E) (hskew : ∀ x y, B x y = -B y x)
    {x y : E} (hxy : B x y = 1)
    (W U : Submodule ℝ E) (hW : W = Submodule.span ℝ ({x, y} : Set E))
    (hU : U = B.orthogonal W) (hcompl : IsCompl W U)
    {n : ℕ} (bU : Module.Basis (Fin n ⊕ Fin n) ℝ U)
    (hpp : ∀ i j, B (bU (Sum.inl i)) (bU (Sum.inl j)) = 0)
    (hqq : ∀ i j, B (bU (Sum.inr i)) (bU (Sum.inr j)) = 0)
    (hpq : ∀ i j, B (bU (Sum.inl i)) (bU (Sum.inr j)) = if i = j then 1 else 0) :
    ∃ b : Module.Basis (Fin (n + 1) ⊕ Fin (n + 1)) ℝ E,
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) := by
  have hxW : x ∈ W := by rw [hW]; exact Submodule.subset_span (by simp)
  have hyW : y ∈ W := by rw [hW]; exact Submodule.subset_span (by simp)
  let vx : W := ⟨x, hxW⟩
  let vy : W := ⟨y, hyW⟩
  let vW : Fin 2 → W := ![vx, vy]
  have hliW : LinearIndependent ℝ vW := by
    rw [show vW = ![vx, vy] by rfl, LinearIndependent.pair_iff]
    intro a c hac
    have hac' := congrArg Subtype.val hac
    change a • x + c • y = 0 at hac'
    exact LinearIndependent.pair_iff.mp
      (normalized_pair_linearIndependent B hskew hxy) a c hac'
  have hspanW : ⊤ ≤ Submodule.span ℝ (Set.range vW) := by
    intro z hz
    have hzpair : (z : E) ∈ Submodule.span ℝ ({x, y} : Set E) := by
      rw [← hW]
      exact z.2
    obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp hzpair
    have hvx : vx ∈ Submodule.span ℝ (Set.range vW) :=
      Submodule.subset_span ⟨0, by simp [vW, vx]⟩
    have hvy : vy ∈ Submodule.span ℝ (Set.range vW) :=
      Submodule.subset_span ⟨1, by simp [vW, vy]⟩
    have hz' : (z : W) = a • vx + c • vy := by
      apply Subtype.ext
      exact hac.symm
    rw [hz']
    exact Submodule.add_mem _ (Submodule.smul_mem _ a hvx) (Submodule.smul_mem _ c hvy)
  let bW₂ : Module.Basis (Fin 2) ℝ W := Module.Basis.mk hliW hspanW
  let bW : Module.Basis (Fin 1 ⊕ Fin 1) ℝ W :=
    bW₂.reindex (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin (1 + 1)).symm
  let bProd : Module.Basis ((Fin 1 ⊕ Fin 1) ⊕ (Fin n ⊕ Fin n)) ℝ E :=
    (bW.prod bU).map (W.prodEquivOfIsCompl U hcompl)
  let b : Module.Basis (Fin (n + 1) ⊕ Fin (n + 1)) ℝ E :=
    bProd.reindex (darbouxIndexEquiv n)
  have bp_zero : b (Sum.inl 0) = x := by
    simp [b, bProd, bW, bW₂, vW, vx, darbouxIndexEquiv]
    rw [finSumFinEquiv_apply_left]
    rfl
  have bq_zero : b (Sum.inr 0) = y := by
    simp [b, bProd, bW, bW₂, vW, vy, darbouxIndexEquiv]
    rw [finSumFinEquiv_apply_right]
    rfl
  have bp_succ (i : Fin n) : b (Sum.inl i.succ) = bU (Sum.inl i) := by
    simp [b, bProd, darbouxIndexEquiv]
  have bq_succ (i : Fin n) : b (Sum.inr i.succ) = bU (Sum.inr i) := by
    simp [b, bProd, darbouxIndexEquiv]
  have hWself (z : W) : B (z : E) (z : E) = 0 := bilin_self_eq_zero B hskew z
  have hxx : B x x = 0 := bilin_self_eq_zero B hskew x
  have hyy : B y y = 0 := bilin_self_eq_zero B hskew y
  have hyx : B y x = -1 := by rw [hskew, hxy]
  have hWU (w : W) (u : U) : B (w : E) (u : E) = 0 := by
    have hu : (u : E) ∈ B.orthogonal W := by simpa [hU] using u.2
    exact hu w w.2
  have hUW (u : U) (w : W) : B (u : E) (w : E) = 0 := by
    have hu : (u : E) ∈ B.orthogonal W := by simpa [hU] using u.2
    rw [hskew, hu w w.2, neg_zero]
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [bp_zero] using hxx
    · rw [bp_zero, bp_succ]
      exact hWU ⟨x, hxW⟩ (bU (Sum.inl j))
    · rw [bp_succ, bp_zero]
      exact hUW (bU (Sum.inl i)) ⟨x, hxW⟩
    · simpa [bp_succ] using hpp i j
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [bq_zero] using hyy
    · rw [bq_zero, bq_succ]
      exact hWU ⟨y, hyW⟩ (bU (Sum.inr j))
    · rw [bq_succ, bq_zero]
      exact hUW (bU (Sum.inr i)) ⟨y, hyW⟩
    · simpa [bq_succ] using hqq i j
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [bp_zero, bq_zero] using hxy
    · rw [bp_zero, bq_succ]
      have hj : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simp [hj, hWU ⟨x, hxW⟩ (bU (Sum.inr j))]
    · rw [bp_succ, bq_zero]
      simpa using hUW (bU (Sum.inl i)) ⟨y, hyW⟩
    · simpa [bp_succ, bq_succ, Fin.succ_inj] using hpq i j
/-- 证明内部的纯双线性版本；递归过程只依赖斜对称与非退化。-/
private theorem exists_darbouxBasis_bilin
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hskew : ∀ x y, B x y = -B y x)
    (hnd : B.Nondegenerate) [Module.Finite ℝ V] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n ⊕ Fin n) ℝ V),
      Module.finrank ℝ V = 2 * n ∧
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) := by
  classical
  generalize hd : Module.finrank ℝ V = d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
      by_cases hd0 : d = 0
      · subst d
        have hfinzero : Module.finrank ℝ V = 0 := by omega
        haveI : Subsingleton V := Module.finrank_zero_iff.mp hfinzero
        let b : Module.Basis (Fin 0 ⊕ Fin 0) ℝ V := Module.Basis.empty V
        exact ⟨0, b, by simpa using hfinzero, by simp, by simp, by simp⟩
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hfinpos : 0 < Module.finrank ℝ V := by omega
        letI : Nontrivial V := Module.finrank_pos_iff.mp hfinpos
        letI : LinearSpace ℝ V := ⟨inferInstance⟩
        obtain ⟨x, y, W, U, hxy, hW, hU, hcompl, hUnd, hWdim, hUdim⟩ :=
          split_normalized_plane B hskew hnd
        have hd_ge_two : 2 ≤ d := by
          have hle : Module.finrank ℝ W ≤ Module.finrank ℝ V := Submodule.finrank_le W
          omega
        have hlt : Module.finrank ℝ U < d := by omega
        have hskewU : ∀ a b, B.restrict U a b = -B.restrict U b a := by
          intro a b
          exact hskew a b
        obtain ⟨n, bU, hdimU, hpp, hqq, hpq⟩ :=
          ih (Module.finrank ℝ U) hlt (V := U) (B.restrict U) hskewU hUnd rfl
        obtain ⟨b, hpp', hqq', hpq'⟩ :=
          prepend_normalized_pair B hskew hxy W U hW hU hcompl bU hpp hqq hpq
        refine ⟨n + 1, b, ?_, hpp', hqq', hpq'⟩
        omega

/-- 线性 Darboux 定理的内部核心版本。这里直接产出一组由 `Module.Basis`
携带完备性证明的标准辛基，随后再翻译回教材接口。-/
private theorem exists_darbouxBasis_core [IsFiniteDimensional ℝ E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n ⊕ Fin n) ℝ E),
      dim ℝ E = 2 * n ∧
      (∀ i j, ω (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, ω (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, ω (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) := by
  have hnd : ω.toBilin.Nondegenerate := by
    constructor
    · intro x hx
      exact ω.nondegenerate x hx
    · intro x hx
      apply ω.nondegenerate x
      intro y
      rw [ω.skew]
      simp only [SymplecticForm.toBilin_apply] at hx
      rw [hx y, neg_zero]
  simpa only [SymplecticForm.toBilin_apply] using
    exists_darbouxBasis_bilin ω.toBilin ω.skew hnd

/-- 有限维线性 Darboux 定理：每个辛空间都存在辛基。
@isnad1 id=ex.0h2v.s6.9a49c422904e from=translated src=- shape=8304f977 vocab=6967e66f
-/
theorem exists_symplecticBasis [IsFiniteDimensional ℝ E] :
    ∃ (n : ℕ) (p q : Fin n → E),
      dim ℝ E = 2 * n ∧ IsSymplecticBasis ω p q := by
  obtain ⟨n, b, hdim, hpp, hqq, hpq⟩ := exists_darbouxBasis_core ω
  let p : Fin n → E := fun i => b (Sum.inl i)
  let q : Fin n → E := fun i => b (Sum.inr i)
  refine ⟨n, p, q, hdim, ?_⟩
  refine ⟨?_, hpp, hqq, hpq⟩
  have hbfun : Sum.elim p q = (b : (Fin n ⊕ Fin n) → E) := by
    funext i
    cases i <;> rfl
  rw [hbfun]
  constructor
  · exact b.linearIndependent
  · exact b.span_eq

/-- 有限维辛空间的维数必为偶数。
@isnad1 id=even.0h2v.s5.70801be20a2a from=translated src=- shape=7c8ab7f4 vocab=8396777a
-/
theorem even_dim (ω : SymplecticForm E) [IsFiniteDimensional ℝ E] : Even (dim ℝ E) := by
  obtain ⟨n, p, q, hdim, hb⟩ := exists_symplecticBasis ω
  refine ⟨n, ?_⟩
  omega

end SandronesLibrary.LinearAlgebra.SymplecticBasis
