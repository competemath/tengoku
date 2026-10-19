/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Analysis.Complex.Convex
import Tengoku.Seed.Analysis.Complex.CoveringMap
import Tengoku.Seed.Analysis.Convex.Contractible
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Log
import Tengoku.Seed.GroupTheory.Archimedean
import Tengoku.Seed.Topology.Homotopy.Lifting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite coverings of a product with a punctured disc

Let `B` be a convex open subset of a real normed space `E` and let `Δ*` be the punctured unit
disc. The space `B × Δ*` has fundamental group `ℤ`, and its finite coverings are the Kummer
coverings `B × Δ* → B × Δ*, (b, u) ↦ (b, uᵏ)` and their finite disjoint unions.

The proof uses the universal covering `B × {Re w < 0} → B × Δ*, (b, w) ↦ (b, exp w)`. A covering
`p : X → B × Δ*` receives a lift `ψ` of the universal covering. The integers `j` for which `ψ` is
invariant under `w ↦ w + 2πij` form a subgroup `kℤ` of `ℤ`, which is non-zero because the fibres
of `p` are finite; then `(b, u) ↦ ψ(b, k log u)` identifies the Kummer covering of degree `k`
with the path component of `X` containing the image of `ψ`.

## Main definitions

- `Kummer.base B`: the set `B × Δ*` inside `E × ℂ`.
- `Kummer.cover B k`: the Kummer covering `(b, u) ↦ (b, uᵏ)` of `B × Δ*`.
- `Kummer.logCover B`: the set `B × {Re w < 0}`, the universal covering space of `B × Δ*`.
- `Kummer.expMap B`: the universal covering `(b, w) ↦ (b, exp w)`.
- `Kummer.fundamentalGroupEquiv`: the fundamental group of `B × Δ*` is `ℤ`.

## Main results

- `IsCoveringMapOn.prodMap_id`: the product of a covering map with an identity is a covering map.
- `Kummer.isCoveringMap_cover`: the Kummer map is a covering map with finite fibres.
- `Kummer.isAddQuotientCoveringMap_expMap`: `B × Δ*` is the quotient of `B × {Re w < 0}` by the
  translations `w ↦ w + 2πij`.
- `IsCoveringMap.exists_kummer`: the path component of a point in a covering of `B × Δ*` with
  finite fibres is the image of an open embedding of a Kummer covering.
- `IsCoveringMap.exists_homeomorph_kummer`: a path connected covering of `B × Δ*` with finite
  fibres is isomorphic to a Kummer covering.
- `IsCoveringMap.exists_homeomorph_sigma_kummer`: a covering of `B × Δ*` with finite fibres is
  isomorphic to a finite disjoint union of Kummer coverings.
-/

open Set Topology Complex

section ProdMap

variable {A E X I : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace I] {f : E → X}

/-- If `x` is evenly covered by `f`, then `(a, x)` is evenly covered by `id × f`. -/
theorem IsEvenlyCovered.prodMap_id {x : X} (h : IsEvenlyCovered f x I) (a : A) :
    IsEvenlyCovered (Prod.map (id : A → A) f) (a, x) I := by
  obtain ⟨hI, U, hxU, hU, hfU, H, hH⟩ := h
  let e₁ : ↥(Prod.map (id : A → A) f ⁻¹' ((univ : Set A) ×ˢ U)) ≃ₜ A × ↥(f ⁻¹' U) :=
    { toFun z := (z.1.1, ⟨z.1.2, z.2.2⟩)
      invFun z := ⟨(z.1, z.2.1), trivial, z.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e₂ : A × ↥U ≃ₜ ↥((univ : Set A) ×ˢ U) :=
    { toFun z := ⟨(z.1, z.2.1), trivial, z.2.2⟩
      invFun z := (z.1.1, ⟨z.1.2, z.2.2⟩)
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨hI, univ ×ˢ U, ⟨trivial, hxU⟩, isOpen_univ.prod hU, isOpen_univ.prod hfU,
    e₁.trans (((Homeomorph.refl A).prodCongr H).trans
      ((Homeomorph.prodAssoc A U I).symm.trans (e₂.prodCongr (Homeomorph.refl I)))),
    fun z ↦ ?_⟩
  change ((z.1.1, (H ⟨z.1.2, z.2.2⟩).1.1) : A × X) = (z.1.1, f z.1.2)
  rw [hH]

/-- The product of a covering map on `s` with an identity map is a covering map on `univ ×ˢ s`. -/
theorem IsCoveringMapOn.prodMap_id {s : Set X} (hf : IsCoveringMapOn f s) :
    IsCoveringMapOn (Prod.map (id : A → A) f) (univ ×ˢ s) := by
  rintro ⟨a, x⟩ ⟨-, hx⟩
  exact ((hf x hx).prodMap_id a).to_isEvenlyCovered_preimage

end ProdMap

namespace Kummer

noncomputable section

variable {E : Type*} (B : Set E)

/-- The punctured open unit disc in `ℂ`. -/
def puncturedDisc : Set ℂ := {u | u ≠ 0 ∧ ‖u‖ < 1}

lemma isOpen_puncturedDisc : IsOpen puncturedDisc :=
  isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)

/-- The product `B × Δ*` of `B` with the punctured unit disc, as a subset of `E × ℂ`. -/
def base : Set (E × ℂ) := B ×ˢ puncturedDisc

variable {B} in
lemma mem_base {x : E × ℂ} : x ∈ base B ↔ x.1 ∈ B ∧ x.2 ≠ 0 ∧ ‖x.2‖ < 1 :=
  Iff.rfl

lemma isOpen_base [TopologicalSpace E] {B : Set E} (hB : IsOpen B) : IsOpen (base B) :=
  hB.prod isOpen_puncturedDisc

lemma preimage_prodMap_pow_base (k : ℕ+) :
    Prod.map (id : E → E) (fun u : ℂ ↦ u ^ (k : ℕ)) ⁻¹' base B = base B := by
  ext ⟨b, u⟩
  simp only [mem_preimage, Prod.map_apply, id_eq, mem_base, norm_pow, ne_eq,
    pow_eq_zero_iff (PNat.ne_zero k), pow_lt_one_iff_of_nonneg (norm_nonneg u) (PNat.ne_zero k)]

/-- The **Kummer covering** `(b, u) ↦ (b, uᵏ)` of `B × Δ*`. -/
def cover (k : ℕ+) (y : base B) : base B :=
  ⟨(y.1.1, y.1.2 ^ (k : ℕ)), y.2.1, pow_ne_zero _ y.2.2.1, by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) y.2.2.2 k.ne_zero⟩

@[simp]
lemma cover_apply (k : ℕ+) (y : base B) : (cover B k y : E × ℂ) = (y.1.1, y.1.2 ^ (k : ℕ)) :=
  rfl

/-- The Kummer map is a covering map. -/
theorem isCoveringMap_cover [TopologicalSpace E] (k : ℕ+) : IsCoveringMap (cover B k) := by
  have h : IsCoveringMapOn (Prod.map (id : E → E) fun u : ℂ ↦ u ^ (k : ℕ)) (base B) :=
    (isCoveringMapOn_npow (𝕜 := ℂ) (k : ℕ) (by simp)).prodMap_id.mono
      fun x hx ↦ ⟨trivial, hx.2.1⟩
  convert h.isCoveringMap_restrictPreimage.comp_homeomorph
    (Homeomorph.setCongr (preimage_prodMap_pow_base B k).symm) using 1
  funext y
  rfl

/-- The fibres of the Kummer map are finite. -/
theorem finite_preimage_cover (k : ℕ+) (y : base B) : (cover B k ⁻¹' {y}).Finite := by
  classical
  refine Finite.of_finite_image (f := fun z : base B ↦ z.1.2) ?_ ?_
  · refine (Polynomial.nthRoots (k : ℕ) y.1.2).toFinset.finite_toSet.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots k.pos]
    exact congrArg (fun y : base B ↦ y.1.2) hz
  · intro z hz z' hz' h
    have h₁ := congrArg (fun y : base B ↦ y.1.1) (hz.trans hz'.symm)
    exact Subtype.ext (Prod.ext h₁ h)

/-- The subset `B × {Re w < 0}` of `E × ℂ`, the universal covering space of `B × Δ*`. -/
def logCover : Set (E × ℂ) := B ×ˢ {w | w.re < 0}

lemma isOpen_logCover [TopologicalSpace E] {B : Set E} (hB : IsOpen B) : IsOpen (logCover B) :=
  hB.prod (isOpen_lt Complex.continuous_re continuous_const)

lemma convex_logCover [AddCommGroup E] [Module ℝ E] {B : Set E} (hB : Convex ℝ B) :
    Convex ℝ (logCover B) :=
  hB.prod (convex_halfSpace_re_lt 0)

lemma preimage_prodMap_exp_base :
    Prod.map (id : E → E) Complex.exp ⁻¹' base B = logCover B := by
  ext ⟨b, w⟩
  simp [mem_base, logCover, Complex.norm_exp, Complex.exp_ne_zero]

/-- The universal covering `(b, w) ↦ (b, exp w)` of `B × Δ*`. -/
def expMap (x : logCover B) : base B :=
  ⟨(x.1.1, Complex.exp x.1.2), x.2.1, Complex.exp_ne_zero _, by
    rw [Complex.norm_exp]
    exact Real.exp_lt_one_iff.2 x.2.2⟩

@[simp]
lemma expMap_apply (x : logCover B) :
    (expMap B x : E × ℂ) = (x.1.1, Complex.exp x.1.2) :=
  rfl

/-- The map `(b, w) ↦ (b, exp w)` is a covering map. -/
theorem isCoveringMap_expMap [TopologicalSpace E] : IsCoveringMap (expMap B) := by
  have h : IsCoveringMapOn (Prod.map (id : E → E) Complex.exp) (base B) :=
    Complex.isCoveringMapOn_exp.prodMap_id.mono fun x hx ↦ ⟨trivial, hx.2.1⟩
  convert h.isCoveringMap_restrictPreimage.comp_homeomorph
    (Homeomorph.setCongr (preimage_prodMap_exp_base B).symm) using 1
  funext y
  rfl

/-- A point of `B × {Re w < 0}` over a point of `B × Δ*`, given by the principal logarithm. -/
def logLift (y : base B) : logCover B :=
  ⟨(y.1.1, Complex.log y.1.2), y.2.1, by
    rw [mem_ofPred_eq, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.2 y.2.2.1) y.2.2.2⟩

@[simp]
lemma expMap_logLift (y : base B) : expMap B (logLift B y) = y :=
  Subtype.ext (Prod.ext rfl (Complex.exp_log y.2.2.1))

lemma surjective_expMap : Function.Surjective (expMap B) :=
  fun y ↦ ⟨logLift B y, expMap_logLift B y⟩

/-- The translation `(b, w) ↦ (b, w + 2πij)` of `B × {Re w < 0}`. -/
def shift (j : ℤ) (x : logCover B) : logCover B :=
  ⟨(x.1.1, x.1.2 + j * (2 * Real.pi * Complex.I)), x.2.1, by simpa using x.2.2⟩

@[simp]
lemma shift_apply (j : ℤ) (x : logCover B) :
    (shift B j x : E × ℂ) = (x.1.1, x.1.2 + j * (2 * Real.pi * Complex.I)) :=
  rfl

lemma shift_zero (x : logCover B) : shift B 0 x = x :=
  Subtype.ext (Prod.ext rfl (by simp))

lemma shift_add (i j : ℤ) (x : logCover B) : shift B (i + j) x = shift B i (shift B j x) :=
  Subtype.ext (Prod.ext rfl (by simp; ring))

@[fun_prop]
lemma continuous_shift [TopologicalSpace E] (j : ℤ) : Continuous (shift B j) := by
  unfold shift
  fun_prop

@[simp]
lemma expMap_shift (j : ℤ) (x : logCover B) : expMap B (shift B j x) = expMap B x :=
  Subtype.ext (Prod.ext rfl (by simp [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]))

variable {B} in
lemma exists_eq_shift {x x' : logCover B} (h : expMap B x = expMap B x') :
    ∃ j : ℤ, x = shift B j x' := by
  have h₁ := congrArg (fun y : base B ↦ y.1.1) h
  have h₂ := congrArg (fun y : base B ↦ y.1.2) h
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 h₂
  exact ⟨j, Subtype.ext (Prod.ext h₁ hj)⟩

instance : AddAction ℤ (logCover B) where
  vadd := shift B
  zero_vadd := shift_zero B
  add_vadd := shift_add B

lemma vadd_def (j : ℤ) (x : logCover B) : j +ᵥ x = shift B j x :=
  rfl

/-- **`B × Δ*` is the quotient of `B × {Re w < 0}` by the translations by `2πiℤ`.** -/
theorem isAddQuotientCoveringMap_expMap [TopologicalSpace E] :
    IsAddQuotientCoveringMap (expMap B) ℤ where
  toIsQuotientMap := (isCoveringMap_expMap B).isQuotientMap (surjective_expMap B)
  continuous_const_vadd j := continuous_shift B j
  apply_eq_iff_mem_orbit {x x'} := by
    rw [AddAction.mem_orbit_iff]
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨j, rfl⟩ := exists_eq_shift h
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact expMap_shift B j x'
  disjoint x := by
    refine ⟨{z | ‖z.1.2 - x.1.2‖ < 1}, (isOpen_lt (by fun_prop) continuous_const).mem_nhds
      (by simp), fun j ⟨z, ⟨z', hz', hz⟩, hz''⟩ ↦ ?_⟩
    change shift B j z' = z at hz
    subst hz
    simp only [mem_ofPred_eq, shift_apply] at hz' hz''
    have h : ‖(j : ℂ) * (2 * Real.pi * Complex.I)‖ < 2 := by
      calc _ = ‖(z'.1.2 + j * (2 * Real.pi * Complex.I) - x.1.2) - (z'.1.2 - x.1.2)‖ := by
              ring_nf
        _ ≤ ‖z'.1.2 + j * (2 * Real.pi * Complex.I) - x.1.2‖ + ‖z'.1.2 - x.1.2‖ :=
              norm_sub_le _ _
        _ < 1 + 1 := add_lt_add hz'' hz'
        _ = 2 := by norm_num
    by_contra hj
    have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hj
    have h2 : ‖(j : ℂ) * (2 * Real.pi * Complex.I)‖ = |(j : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [h2] at h
    nlinarith [Real.two_le_pi]

variable {B}

lemma nonempty_logCover (y : base B) : (logCover B).Nonempty :=
  ⟨_, (logLift B y).2⟩

/-- **The fundamental group of `B × Δ*` is `ℤ`**, for `B` convex. -/
def fundamentalGroupEquiv [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (hB : Convex ℝ B) (y : base B) :
    FundamentalGroup (base B) y ≃* Multiplicative ℤ :=
  haveI : ContractibleSpace (logCover B) :=
    (convex_logCover hB).contractibleSpace (nonempty_logCover y)
  ((isAddQuotientCoveringMap_expMap B).fundamentalGroupEquiv
    (⟨logLift B y, expMap_logLift B y⟩ : expMap B ⁻¹' {y})).trans
    MulOpposite.opMulEquiv.symm

/-- The dilation `(b, w) ↦ (b, k w)` of `B × {Re w < 0}`. -/
def scale (k : ℕ+) (x : logCover B) : logCover B :=
  ⟨(x.1.1, (k : ℂ) * x.1.2), x.2.1, by
    have := x.2.2
    simp only [mem_ofPred_eq] at this ⊢
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast k.pos) this⟩

/-- The contraction `(b, w) ↦ (b, w / k)` of `B × {Re w < 0}`. -/
def unscale (k : ℕ+) (x : logCover B) : logCover B :=
  ⟨(x.1.1, x.1.2 / (k : ℂ)), x.2.1, by
    have := x.2.2
    simp only [mem_ofPred_eq] at this ⊢
    rw [Complex.div_natCast_re]
    exact div_neg_of_neg_of_pos this (by exact_mod_cast k.pos)⟩

lemma scale_unscale (k : ℕ+) (x : logCover B) : scale k (unscale k x) = x :=
  Subtype.ext (Prod.ext rfl (mul_div_cancel₀ _ (by exact_mod_cast k.ne_zero)))

lemma scale_injective (k : ℕ+) : Function.Injective (scale (B := B) k) := by
  intro x x' h
  have h₁ := congrArg (fun y : logCover B ↦ y.1.1) h
  have h₂ := congrArg (fun y : logCover B ↦ y.1.2) h
  exact Subtype.ext (Prod.ext h₁ (mul_left_cancel₀ (by exact_mod_cast k.ne_zero) h₂))

@[fun_prop]
lemma continuous_scale [TopologicalSpace E] (k : ℕ+) : Continuous (scale (B := B) k) := by
  unfold scale
  fun_prop

lemma scale_shift (k : ℕ+) (j : ℤ) (x : logCover B) :
    scale k (shift B j x) = shift B (k * j) (scale k x) :=
  Subtype.ext (Prod.ext rfl (by simp [scale]; ring))

lemma expMap_scale (k : ℕ+) (x : logCover B) :
    expMap B (scale k x) = cover B k (expMap B x) :=
  Subtype.ext (Prod.ext rfl (by simp [scale, Complex.exp_nat_mul]))

lemma surjective_cover (k : ℕ+) : Function.Surjective (cover B k) := by
  intro y
  obtain ⟨x, rfl⟩ := surjective_expMap B y
  exact ⟨expMap B (unscale k x), by rw [← expMap_scale, scale_unscale]⟩

end

end Kummer

open Kummer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}
  {X : Type*} [TopologicalSpace X] {p : X → base B}

/-- **The path components of a covering of `B × Δ*` are Kummer coverings.** Let `p` be a
covering map of `B × Δ*` with finite fibres, `B` convex and open. The path component of any
`e₀` is the image of an open embedding `Φ` of `B × Δ*` with `p ∘ Φ` a Kummer map. -/
theorem IsCoveringMap.exists_kummer (hB : Convex ℝ B) (hBo : IsOpen B) (hp : IsCoveringMap p)
    (hfin : ∀ y, (p ⁻¹' {y}).Finite) (e₀ : X) :
    ∃ (k : ℕ+) (Φ : base B → X), Continuous Φ ∧ IsOpenMap Φ ∧ Function.Injective Φ ∧
      range Φ = pathComponent e₀ ∧ ∀ y, p (Φ y) = cover B k y := by
  set x₀ := logLift B (p e₀)
  haveI : ContractibleSpace (logCover B) :=
    (convex_logCover hB).contractibleSpace (nonempty_logCover (p e₀))
  haveI : LocallyPathConnectedSpace (logCover B) := (isOpen_logCover hBo).locallyPathConnectedSpace
  obtain ⟨ψ, ⟨hψ₀, hψ⟩, -⟩ := hp.existsUnique_continuousMap_lifts
    ⟨expMap B, (isCoveringMap_expMap B).continuous⟩ x₀ e₀ (expMap_logLift B _).symm
  have hψ' (x : logCover B) : p (ψ x) = expMap B x := congrFun hψ x
  -- Invariance under a translation at one point implies invariance everywhere.
  have L1 (j : ℤ) (x : logCover B) (h : ψ (shift B j x) = ψ x) (x' : logCover B) :
      ψ (shift B j x') = ψ x' := by
    have := hp.eq_of_comp_eq (g₁ := ψ ∘ shift B j) (g₂ := ψ) (by fun_prop) ψ.continuous
      (funext fun z ↦ by simp [hψ']) x h
    exact congrFun this x'
  let Γ : AddSubgroup ℤ :=
    { carrier := {j | ∀ x, ψ (shift B j x) = ψ x}
      add_mem' := fun {a b} ha hb x ↦ by
        simp only [mem_ofPred_eq] at ha hb ⊢
        rw [shift_add, ha, hb]
      zero_mem' := fun x ↦ by simp only [shift_zero]
      neg_mem' := fun {a} ha x ↦ by
        simp only [mem_ofPred_eq] at ha ⊢
        rw [← ha (shift B (-a) x), ← shift_add, add_neg_cancel, shift_zero] }
  have hΓ (j : ℤ) : j ∈ Γ ↔ ∀ x, ψ (shift B j x) = ψ x := Iff.rfl
  -- The subgroup `Γ` is non-zero since the fibre over `p e₀` is finite.
  haveI := (hfin (p e₀)).to_subtype
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun j : ℤ ↦ (⟨ψ (shift B j x₀), by simp [hψ', x₀]⟩ : p ⁻¹' {p e₀}))
  have hmem : i - j ∈ Γ := L1 (i - j) (shift B j x₀) (by
    rw [← shift_add, sub_add_cancel]
    exact congrArg Subtype.val hfij)
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic Γ
  rw [← AddSubgroup.zmultiples_eq_closure] at ha
  have hΓa (j : ℤ) : j ∈ Γ ↔ a ∣ j := by rw [ha, Int.mem_zmultiples_iff]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hij (sub_eq_zero.1 (zero_dvd_iff.1 ((hΓa _).1 hmem)))
  let k : ℕ+ := ⟨a.natAbs, Int.natAbs_pos.2 ha0⟩
  have hΓk (j : ℤ) : j ∈ Γ ↔ (k : ℤ) ∣ j := by
    rw [hΓa]
    exact Int.natAbs_dvd.symm
  -- The map `(b, u) ↦ ψ(b, k log u)`.
  let Φ : base B → X := fun y ↦ ψ (scale k (logLift B y))
  have L2 (x : logCover B) : Φ (expMap B x) = ψ (scale k x) := by
    obtain ⟨j, hj⟩ := exists_eq_shift (expMap_logLift B (expMap B x))
    simp only [Φ]
    rw [hj, scale_shift]
    exact ((hΓk _).2 (dvd_mul_right _ _)) _
  have hcont : Continuous Φ := by
    rw [((isCoveringMap_expMap B).isQuotientMap (surjective_expMap B)).continuous_iff]
    have : Φ ∘ expMap B = ψ ∘ scale k := funext L2
    rw [this]
    fun_prop
  have hpΦ (y : base B) : p (Φ y) = cover B k y := by
    simp only [Φ, hψ', expMap_scale, expMap_logLift]
  refine ⟨k, Φ, hcont, ?_, ?_, ?_, hpΦ⟩
  · refine (IsLocalHomeomorph.of_comp (g := p) ?_ hp.isLocalHomeomorph hcont).isOpenMap
    have : p ∘ Φ = cover B k := funext hpΦ
    rw [this]
    exact (isCoveringMap_cover B k).isLocalHomeomorph
  · intro y y' h
    obtain ⟨x, rfl⟩ := surjective_expMap B y
    obtain ⟨x', rfl⟩ := surjective_expMap B y'
    rw [L2, L2] at h
    have h' : expMap B (scale k x) = expMap B (scale k x') := by rw [← hψ', h, hψ']
    obtain ⟨j, hj⟩ := exists_eq_shift h'
    rw [hj] at h
    obtain ⟨m, rfl⟩ := (hΓk j).1 (L1 j _ h)
    rw [← scale_shift] at hj
    rw [scale_injective k hj, expMap_shift]
  · ext e
    constructor
    · rintro ⟨y, rfl⟩
      have h := (PathConnectedSpace.joined x₀ (scale k (logLift B y))).somePath.map ψ.continuous
      rw [hψ₀] at h
      exact ⟨h⟩
    · intro he
      obtain ⟨γ⟩ := (mem_pathComponent_iff.1 he)
      obtain ⟨Γ', hΓ', hΓ'0⟩ := (isCoveringMap_expMap B).exists_path_lifts
        ⟨fun t ↦ p (γ t), hp.continuous.comp γ.continuous⟩ x₀ (by simp [x₀])
      have := hp.eq_of_comp_eq (g₁ := ψ ∘ Γ') (g₂ := γ) (by fun_prop) γ.continuous
        (funext fun t ↦ by simpa [hψ'] using congrFun hΓ' t) 0 (by simp [hΓ'0, hψ₀])
      refine ⟨expMap B (unscale k (Γ' 1)), ?_⟩
      rw [L2, scale_unscale]
      simpa using congrFun this 1

/-- **A covering of `B × Δ*` with finite fibres is a finite disjoint union of Kummer
coverings**, indexed by its path components. -/
theorem IsCoveringMap.exists_homeomorph_sigma_kummer (hB : Convex ℝ B) (hBo : IsOpen B)
    (hp : IsCoveringMap p) (hfin : ∀ y, (p ⁻¹' {y}).Finite) :
    Finite (ZerothHomotopy X) ∧ ∃ (k : ZerothHomotopy X → ℕ+)
      (Φ : (Σ _ : ZerothHomotopy X, base B) ≃ₜ X), ∀ c y, p (Φ ⟨c, y⟩) = cover B (k c) y := by
  choose rep hrep using ZerothHomotopy.mk_surjective (X := X)
  choose k Φ hcont hopen hinj hrange hpΦ using fun c ↦ hp.exists_kummer hB hBo hfin (rep c)
  have hmem (c : ZerothHomotopy X) (y : base B) : Φ c y ∈ pathComponent (rep c) :=
    hrange c ▸ mem_range_self y
  have hsep (c c' : ZerothHomotopy X) (y y' : base B) (h : Φ c y = Φ c' y') : c = c' := by
    have h₁ := hmem c y
    have h₂ := hmem c' y'
    rw [h] at h₁
    rw [← hrep c, ← hrep c']
    exact Quotient.sound ((mem_pathComponent_iff.1 h₁).trans (mem_pathComponent_iff.1 h₂).symm)
  refine ⟨?_, k, ?_⟩
  · by_cases hX : Nonempty X
    · obtain ⟨e⟩ := hX
      haveI := (hfin (p e)).to_subtype
      choose s hs using fun c ↦ surjective_cover (k c) (p e)
      refine Finite.of_injective (fun c ↦ (⟨Φ c (s c), by simp [hpΦ, hs]⟩ : p ⁻¹' {p e}))
        fun c c' h ↦ hsep c c' _ _ (congrArg Subtype.val h)
    · haveI : IsEmpty X := not_nonempty_iff.1 hX
      haveI : IsEmpty (ZerothHomotopy X) := ⟨fun c ↦ ZerothHomotopy.rec (motive := fun _ ↦ False)
        (fun e ↦ isEmptyElim e) c⟩
      infer_instance
  · let Ψ : (Σ _ : ZerothHomotopy X, base B) → X := fun z ↦ Φ z.1 z.2
    have hinj' : Function.Injective Ψ := by
      rintro ⟨c, y⟩ ⟨c', y'⟩ h
      obtain rfl := hsep c c' y y' h
      obtain rfl := hinj c h
      rfl
    have hsurj : Function.Surjective Ψ := by
      intro e
      have he : e ∈ pathComponent (rep (ZerothHomotopy.mk e)) :=
        mem_pathComponent_iff.2 (Quotient.exact (hrep (ZerothHomotopy.mk e)))
      rw [← hrange] at he
      obtain ⟨y, hy⟩ := he
      exact ⟨⟨_, y⟩, hy⟩
    exact ⟨(Equiv.ofBijective Ψ ⟨hinj', hsurj⟩).toHomeomorphOfContinuousOpen
      (continuous_sigma hcont) (isOpenMap_sigma.2 hopen), fun c y ↦ hpΦ c y⟩
