/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytic.Laurent.L1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Toeplitz operators on Laurent series and the cohomology of `E(k)` on `ℙ¹`

Let `g`, `u` be Laurent series with values in `V →L[ℂ] V`, inverse to each other, representing
the transition function of a vector bundle `E` on `ℙ¹` with respect to the cover by the discs
`{‖w‖ < σ}` and `{‖w‖ > σ⁻¹}`, and its inverse. On `ℓ¹` Laurent series (`Laurent.L1`) the Čech
differential of `E(k)` is

  `Φ k (a, b) = a - wᵏ g b`,

where `a` has no terms of negative degree and `b` none of positive degree. We construct:

* for `k` with `‖g‖ ‖π_{> k} u‖ < 1`, a right inverse of `Φ k` (`Laurent.L1.rinv`): this is the
  vanishing of `H¹(ℙ¹, E(k))`;
* for `m` with `‖g‖ ‖π_{≤ m} u‖ < 1`, a left inverse of `Φ m` on pairs `(a, b)` of the above
  form (`Laurent.L1.linvA`, `Laurent.L1.linvB`): this is the vanishing of `H⁰(ℙ¹, E(m))`;
* from both, for `D = k - m`, an idempotent endomorphism `Laurent.L1.jetIdem` of `V^D` whose image
  is identified with `H⁰(ℙ¹, E(k))` by the map sending a section to the first `D` Taylor
  coefficients of `a` (`Laurent.L1.recon_ofJet_toJet`, `Laurent.L1.phi_recon`).

All operators are explicit expressions in `g`, `u` and inverses `Ring.inverse (1 - T)` of
operators `T` of norm less than `1`, so they depend holomorphically on holomorphic families
`g`, `u`.

## Main definitions

- `Laurent.L1.mulL V σ`: multiplication by `V →L[ℂ] V`-valued Laurent series.
- `Laurent.L1.phi σ g k`: the map `(a, b) ↦ a - wᵏ g b`.
- `Laurent.L1.rinv`, `Laurent.L1.linvA`, `Laurent.L1.linvB`, `Laurent.L1.recon`,
  `Laurent.L1.jetIdem`.

## Main results

- `Laurent.L1.norm_proj_Ioi_mulL_proj_Iio_le`, `Laurent.L1.norm_proj_Iic_mulL_proj_Ici_le`: the
  tail estimates behind the Neumann series.
- `Laurent.L1.phi_rinv`: `rinv` is a right inverse of `phi`.
- `Laurent.L1.linv_phi`: `(linvA, linvB)` is a left inverse of `phi`.
- `Laurent.L1.recon_ofJet_toJet`, `Laurent.L1.phi_recon_ofJet`, `Laurent.L1.jetIdem_toJet`,
  `Laurent.L1.jetIdem_comp_self`: the kernel of `phi σ g k` is identified with the image of the
  idempotent `jetIdem`.
- `Laurent.L1.differentiableOn_rinv`, `Laurent.L1.differentiableOn_recon`,
  `Laurent.L1.differentiableOn_jetIdem`: holomorphic dependence on `g` and `u`.
-/

open Set Filter Metric Complex
open scoped Topology

namespace Laurent

namespace L1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {σ : ℝ}
  [hσ : Fact (1 ≤ σ)]

/-! ### Algebra of shifts and projections -/

section Algebra

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

lemma shift_shift (m n : ℤ) (x : L1 W) : shift σ m (shift σ n x) = shift σ (m + n) x :=
  ext_coeff (zero_lt_one.trans_le hσ.out) fun j ↦ by simp [sub_sub]

@[simp]
lemma shift_zero_apply (x : L1 W) : shift σ 0 x = x :=
  ext_coeff (zero_lt_one.trans_le hσ.out) fun j ↦ by simp

lemma shift_neg_shift (m : ℤ) (x : L1 W) : shift σ (-m) (shift σ m x) = x := by
  rw [shift_shift, neg_add_cancel, shift_zero_apply]

lemma shift_shift_neg (m : ℤ) (x : L1 W) : shift σ m (shift σ (-m) x) = x := by
  rw [shift_shift, add_neg_cancel, shift_zero_apply]

lemma proj_shift (S : Set ℤ) (m : ℤ) (x : L1 W) :
    proj W S (shift σ m x) = shift σ m (proj W ((· + m) ⁻¹' S) x) :=
  ext_coeff (zero_lt_one.trans_le hσ.out) fun j ↦ by
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj]

omit hσ in
lemma proj_proj (S T : Set ℤ) (x : L1 W) : proj W S (proj W T x) = proj W (S ∩ T) x :=
  lp.ext <| funext fun j ↦ by
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [proj_apply, hS, hT]

omit hσ in
lemma proj_add_proj_compl (S : Set ℤ) (x : L1 W) : proj W S x + proj W Sᶜ x = x :=
  lp.ext <| funext fun j ↦ by
    by_cases hS : j ∈ S <;> simp [proj_apply, hS]

omit hσ in
lemma proj_univ (x : L1 W) : proj W univ x = x :=
  lp.ext <| funext fun j ↦ by simp [proj_apply]

omit hσ in
lemma proj_of_subset {S T : Set ℤ} (h : T ⊆ S) {x : L1 W} (hx : proj W T x = x) :
    proj W S x = x := by
  rw [← hx, proj_proj, inter_eq_right.2 h]

omit hσ in
lemma proj_eq_self_iff {S : Set ℤ} {x : L1 W} :
    proj W S x = x ↔ ∀ j ∉ S, x j = 0 := by
  refine ⟨fun h j hj ↦ ?_, fun h ↦ lp.ext <| funext fun j ↦ ?_⟩
  · rw [← h, proj_apply, indicator_of_notMem hj]
  · by_cases hj : j ∈ S
    · simp [proj_apply, hj]
    · simp [proj_apply, hj, h j hj]

omit hσ in
lemma coeff_eq_zero_of_proj_eq_self {S : Set ℤ} {x : L1 W} (hx : proj W S x = x) {j : ℤ}
    (hj : j ∉ S) : coeff σ x j = 0 := by
  rw [coeff, proj_eq_self_iff.1 hx j hj, smul_zero]

end Algebra

/-! ### Multiplication by operator-valued Laurent series -/

section Mul

variable (σ V) in
/-- Multiplication of `V`-valued Laurent series by `V →L[ℂ] V`-valued Laurent series. -/
noncomputable def mulL : L1 (V →L[ℂ] V) →L[ℂ] L1 V →L[ℂ] L1 V :=
  conv σ (ContinuousLinearMap.id ℂ (V →L[ℂ] V))

lemma coeff_mulL (g : L1 (V →L[ℂ] V)) (x : L1 V) (m : ℤ) :
    coeff σ (mulL V σ g x) m = ∑' i, coeff σ g i (coeff σ x (m - i)) :=
  coeff_conv _ g x m

lemma norm_mulL_le (g : L1 (V →L[ℂ] V)) : ‖mulL V σ g‖ ≤ ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
  refine (norm_conv_apply_apply_le _ g x).trans ?_
  have := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := V →L[ℂ] V)
  gcongr
  calc ‖ContinuousLinearMap.id ℂ (V →L[ℂ] V)‖ * ‖g‖ ≤ 1 * ‖g‖ := by gcongr
    _ = ‖g‖ := one_mul _

lemma mulL_shift (g : L1 (V →L[ℂ] V)) (m : ℤ) (x : L1 V) :
    mulL V σ g (shift σ m x) = shift σ m (mulL V σ g x) :=
  ext_coeff (zero_lt_one.trans_le hσ.out) fun j ↦ by
    simp only [coeff_mulL, coeff_shift]
    exact tsum_congr fun i ↦ by rw [sub_right_comm]

/-- The product of a series of degree at most `p` with one of degree at most `q` has degree at
most `p + q`. -/
lemma proj_mulL_eq_zero_of_le {g : L1 (V →L[ℂ] V)} {x : L1 V} {p q n : ℤ}
    (hg : proj _ (Iic p) g = g) (hx : proj V (Iic q) x = x) (hn : p + q ≤ n) :
    proj V (Ioi n) (mulL V σ g x) = 0 :=
  ext_coeff (zero_lt_one.trans_le hσ.out) fun m ↦ by
    rw [coeff_proj, coeff_zero]
    by_cases hm : m ∈ Ioi n
    · rw [indicator_of_mem hm]
      exact coeff_conv_eq_zero_of_gt _
        (fun i hi ↦ coeff_eq_zero_of_proj_eq_self hg (by simpa using hi))
        (fun j hj ↦ coeff_eq_zero_of_proj_eq_self hx (by simpa using hj))
        (lt_of_le_of_lt hn hm)
    · exact indicator_of_notMem hm _

/-- The product of a series of order at least `p` with one of order at least `q` has order at
least `p + q`. -/
lemma proj_mulL_eq_zero_of_ge {g : L1 (V →L[ℂ] V)} {x : L1 V} {p q n : ℤ}
    (hg : proj _ (Ici p) g = g) (hx : proj V (Ici q) x = x) (hn : n < p + q) :
    proj V (Iic n) (mulL V σ g x) = 0 :=
  ext_coeff (zero_lt_one.trans_le hσ.out) fun m ↦ by
    rw [coeff_proj, coeff_zero]
    by_cases hm : m ∈ Iic n
    · rw [indicator_of_mem hm]
      exact coeff_conv_eq_zero_of_lt _
        (fun i hi ↦ coeff_eq_zero_of_proj_eq_self hg (by simpa using hi))
        (fun j hj ↦ coeff_eq_zero_of_proj_eq_self hx (by simpa using hj))
        (lt_of_le_of_lt hm hn)
    · exact indicator_of_notMem hm _

/-- **Tail estimate**: `‖π_{> k} (g · π_{< 0} x)‖ ≤ ‖π_{> k} g‖ ‖x‖`. -/
lemma norm_proj_Ioi_mulL_proj_Iio_le (g : L1 (V →L[ℂ] V)) (k : ℤ) (x : L1 V) :
    ‖proj V (Ioi k) (mulL V σ g (proj V (Iio 0) x))‖ ≤ ‖proj _ (Ioi k) g‖ * ‖x‖ := by
  have hsplit := proj_add_proj_compl (Iic k) g
  rw [compl_Iic] at hsplit
  have h0 : proj V (Ioi k) (mulL V σ (proj _ (Iic k) g) (proj V (Iio 0) x)) = 0 :=
    proj_mulL_eq_zero_of_le (p := k) (q := -1) (by rw [proj_proj, inter_self])
      (by rw [proj_proj, show Iic (-1 : ℤ) ∩ Iio 0 = Iio 0 by
        ext j; simp only [mem_inter_iff, mem_Iic, mem_Iio]; omega]) (by omega)
  conv_lhs => rw [← hsplit, map_add, add_apply, map_add, h0, zero_add]
  calc ‖proj V (Ioi k) (mulL V σ (proj _ (Ioi k) g) (proj V (Iio 0) x))‖
      ≤ ‖mulL V σ (proj _ (Ioi k) g) (proj V (Iio 0) x)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (norm_proj_le _))
    _ ≤ ‖proj _ (Ioi k) g‖ * ‖proj V (Iio 0) x‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_mulL_le _)
    _ ≤ ‖proj _ (Ioi k) g‖ * ‖x‖ := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (norm_proj_le _))

/-- **Tail estimate**: `‖π_{≤ m} (g · π_{≥ 0} x)‖ ≤ ‖π_{≤ m} g‖ ‖x‖`. -/
lemma norm_proj_Iic_mulL_proj_Ici_le (g : L1 (V →L[ℂ] V)) (m : ℤ) (x : L1 V) :
    ‖proj V (Iic m) (mulL V σ g (proj V (Ici 0) x))‖ ≤ ‖proj _ (Iic m) g‖ * ‖x‖ := by
  have hsplit := proj_add_proj_compl (Iic m) g
  rw [compl_Iic] at hsplit
  have h0 : proj V (Iic m) (mulL V σ (proj _ (Ioi m) g) (proj V (Ici 0) x)) = 0 :=
    proj_mulL_eq_zero_of_ge (p := m + 1) (q := 0)
      (by rw [proj_proj, show Ici (m + 1) ∩ Ioi m = Ioi m by
        ext j; simp only [mem_inter_iff, mem_Ici, mem_Ioi]; omega])
      (by rw [proj_proj, inter_self])
      (by omega)
  conv_lhs => rw [← hsplit, map_add, add_apply, map_add, h0, add_zero]
  calc ‖proj V (Iic m) (mulL V σ (proj _ (Iic m) g) (proj V (Ici 0) x))‖
      ≤ ‖mulL V σ (proj _ (Iic m) g) (proj V (Ici 0) x)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (norm_proj_le _))
    _ ≤ ‖proj _ (Iic m) g‖ * ‖proj V (Ici 0) x‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_mulL_le _)
    _ ≤ ‖proj _ (Iic m) g‖ * ‖x‖ := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (norm_proj_le _))

end Mul

/-! ### The Čech differential and its one-sided inverses -/

section Operators

variable (σ) (g u : L1 (V →L[ℂ] V))

/-- The Čech differential `(a, b) ↦ a - wᵏ g b` of `E(k)`. -/
noncomputable def phi (k : ℤ) : L1 V × L1 V →L[ℂ] L1 V :=
  ContinuousLinearMap.fst ℂ (L1 V) (L1 V) -
    (shift σ k ∘L mulL V σ g) ∘L ContinuousLinearMap.snd ℂ (L1 V) (L1 V)

lemma phi_apply (k : ℤ) (x : L1 V × L1 V) : phi σ g k x = x.1 - shift σ k (mulL V σ g x.2) :=
  rfl

/-- The error term `g π_{> k} (u π_{< 0} ·)` of the first approximation `rinv₀` to a right inverse
of `phi σ g k`. -/
noncomputable def errR (k : ℤ) : L1 V →L[ℂ] L1 V :=
  mulL V σ g ∘L proj V (Ioi k) ∘L mulL V σ u ∘L proj V (Iio 0)

/-- The first approximation `h ↦ (π_{≥ 0} h, -π_{≤ 0} (w⁻ᵏ u π_{< 0} h))` to a right inverse of
`phi σ g k`. -/
noncomputable def rinv₀ (k : ℤ) : L1 V →L[ℂ] L1 V × L1 V :=
  (proj V (Ici 0)).prod (-(proj V (Iic 0) ∘L shift σ (-k) ∘L mulL V σ u ∘L proj V (Iio 0)))

/-- A right inverse of `phi σ g k`, if `1 - errR σ g u k` is invertible
(`Laurent.L1.phi_rinv`). -/
noncomputable def rinv (k : ℤ) : L1 V →L[ℂ] L1 V × L1 V :=
  rinv₀ σ u k ∘L Ring.inverse (1 - errR σ g u k)

/-- The error term `π_{≥ 0} g π_{≤ m} u π_{≥ 0}` of the left inverse of `phi σ g m`. -/
noncomputable def errL (m : ℤ) : L1 V →L[ℂ] L1 V :=
  proj V (Ici 0) ∘L mulL V σ g ∘L proj V (Iic m) ∘L mulL V σ u ∘L proj V (Ici 0)

/-- The first component of a left inverse of `phi σ g m` (`Laurent.L1.linv_phi`). -/
noncomputable def linvA (m : ℤ) : L1 V →L[ℂ] L1 V :=
  Ring.inverse (1 - errL σ g u m) ∘L proj V (Ici 0) ∘L
    (1 - mulL V σ g ∘L proj V (Iic m) ∘L mulL V σ u)

/-- The second component of a left inverse of `phi σ g m` (`Laurent.L1.linv_phi`). -/
noncomputable def linvB (m : ℤ) : L1 V →L[ℂ] L1 V :=
  shift σ (-m) ∘L proj V (Iic m) ∘L mulL V σ u ∘L (linvA σ g u m - 1)

variable {σ g u}

lemma shift_proj_shift_neg {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (S : Set ℤ)
    (m : ℤ) (x : L1 W) :
    shift σ m (proj W S (shift σ (-m) x)) = proj W ((· + -m) ⁻¹' S) x := by
  rw [proj_shift, shift_shift_neg]

lemma phi_rinv₀ (hgu : ∀ x, mulL V σ g (mulL V σ u x) = x) (k : ℤ) (x : L1 V) :
    phi σ g k (rinv₀ σ u k x) = x - errR σ g u k x := by
  have hS : (· + -k) ⁻¹' Iic (0 : ℤ) = Iic k := by
    ext j
    simp only [mem_preimage, mem_Iic]
    omega
  set z := mulL V σ u (proj V (Iio 0) x) with hz
  have h1 : shift σ k (mulL V σ g (proj V (Iic 0) (shift σ (-k) z))) =
      mulL V σ g (proj V (Iic k) z) := by
    rw [← mulL_shift, shift_proj_shift_neg, hS]
  have h2 := proj_add_proj_compl (Iic k) z
  rw [compl_Iic] at h2
  have h3 := proj_add_proj_compl (Ici 0) x
  rw [compl_Ici] at h3
  have h4 : mulL V σ g (proj V (Iic k) z) = proj V (Iio 0) x - mulL V σ g (proj V (Ioi k) z) := by
    rw [eq_sub_of_add_eq h2, map_sub, hz, hgu]
  have e1 : rinv₀ σ u k x = (proj V (Ici 0) x, -proj V (Iic 0) (shift σ (-k) z)) := rfl
  have e2 : errR σ g u k x = mulL V σ g (proj V (Ioi k) z) := rfl
  rw [e1, e2, phi_apply, map_neg, map_neg, h1, h4, sub_neg_eq_add, ← add_sub_assoc, h3]

lemma phi_rinv (hgu : ∀ x, mulL V σ g (mulL V σ u x) = x) {k : ℤ}
    (hk : IsUnit (1 - errR σ g u k)) (x : L1 V) : phi σ g k (rinv σ g u k x) = x := by
  rw [rinv, ContinuousLinearMap.comp_apply, phi_rinv₀ hgu]
  change ((1 - errR σ g u k) * Ring.inverse (1 - errR σ g u k)) x = x
  rw [Ring.mul_inverse_cancel _ hk]
  rfl

lemma rinv_fst_mem (k : ℤ) (x : L1 V) :
    proj V (Ici 0) (rinv σ g u k x).1 = (rinv σ g u k x).1 := by
  simp [rinv, rinv₀, proj_proj]

lemma rinv_snd_mem (k : ℤ) (x : L1 V) :
    proj V (Iic 0) (rinv σ g u k x).2 = (rinv σ g u k x).2 := by
  simp [rinv, rinv₀, proj_proj]

lemma proj_Iic_shift_of_proj {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℤ}
    {b : L1 W} (hb : proj W (Iic 0) b = b) : proj W (Iic m) (shift σ m b) = shift σ m b := by
  rw [proj_shift]
  congr 1
  refine proj_of_subset (fun j hj ↦ ?_) hb
  simp only [mem_Iic, mem_preimage] at hj ⊢
  omega

lemma linv_phi (hug : ∀ x, mulL V σ u (mulL V σ g x) = x) {m : ℤ}
    (hm : IsUnit (1 - errL σ g u m)) {a b : L1 V} (ha : proj V (Ici 0) a = a)
    (hb : proj V (Iic 0) b = b) :
    linvA σ g u m (phi σ g m (a, b)) = a ∧ linvB σ g u m (phi σ g m (a, b)) = b := by
  have hy : mulL V σ u (phi σ g m (a, b)) = mulL V σ u a - shift σ m b := by
    rw [phi_apply, map_sub, mulL_shift, hug]
  have hP : proj V (Iic m) (mulL V σ u (phi σ g m (a, b))) =
      proj V (Iic m) (mulL V σ u a) - shift σ m b := by
    rw [hy, map_sub, proj_Iic_shift_of_proj hb]
  have hA : proj V (Ici 0) ((1 - mulL V σ g ∘L proj V (Iic m) ∘L mulL V σ u) (phi σ g m (a, b))) =
      (1 - errL σ g u m) a := by
    have e1 : (1 - mulL V σ g ∘L proj V (Iic m) ∘L mulL V σ u) (phi σ g m (a, b)) =
        phi σ g m (a, b) - mulL V σ g (proj V (Iic m) (mulL V σ u (phi σ g m (a, b)))) := rfl
    have e2 : (1 - errL σ g u m) a =
        a - proj V (Ici 0) (mulL V σ g (proj V (Iic m) (mulL V σ u (proj V (Ici 0) a)))) := rfl
    rw [e1, e2, hP]
    simp only [map_sub, ha, mulL_shift, phi_apply]
    abel
  have hlinA : linvA σ g u m (phi σ g m (a, b)) = a := by
    change Ring.inverse (1 - errL σ g u m)
      (proj V (Ici 0) ((1 - mulL V σ g ∘L proj V (Iic m) ∘L mulL V σ u) (phi σ g m (a, b)))) = a
    rw [hA]
    change (Ring.inverse (1 - errL σ g u m) * (1 - errL σ g u m)) a = a
    rw [Ring.inverse_mul_cancel _ hm]
    rfl
  refine ⟨hlinA, ?_⟩
  change shift σ (-m) (proj V (Iic m) (mulL V σ u
    (linvA σ g u m (phi σ g m (a, b)) - phi σ g m (a, b)))) = b
  rw [hlinA, map_sub, hy, sub_sub_cancel, proj_Iic_shift_of_proj hb, shift_neg_shift]

end Operators
/-! ### Reconstruction of sections from their jets -/

section Recon

variable (σ) (g u : L1 (V →L[ℂ] V))

/-- A left inverse of `phi σ g k` on pairs `(a, b)` such that `a` has order at least `k - m`
(`Laurent.L1.lhigh_phi`). -/
noncomputable def lhigh (k m : ℤ) : L1 V →L[ℂ] L1 V × L1 V :=
  (shift σ (k - m) ∘L linvA σ g u m ∘L shift σ (m - k)).prod (linvB σ g u m ∘L shift σ (m - k))

/-- A right inverse of `phi σ g k` which restricts to `lhigh σ g u k m` on the image of pairs
`(a, b)` such that `a` has order at least `k - m`. -/
noncomputable def sol (k m : ℤ) : L1 V →L[ℂ] L1 V × L1 V :=
  lhigh σ g u k m + rinv σ g u k ∘L (1 - phi σ g k ∘L lhigh σ g u k m)

/-- The map `p ↦ (p, 0) - sol p`, a projection onto the kernel of `phi σ g k` which recovers
every element `(a, b)` of the kernel from the truncation of `a` below degree `k - m`
(`Laurent.L1.recon_proj`). -/
noncomputable def recon (k m : ℤ) : L1 V →L[ℂ] L1 V × L1 V :=
  ContinuousLinearMap.inl ℂ (L1 V) (L1 V) - sol σ g u k m

variable {σ g u}

lemma proj_shift_of_proj {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {S T : Set ℤ}
    {m : ℤ} (hST : ∀ j ∈ S, j + m ∈ T) {x : L1 W} (hx : proj W S x = x) :
    proj W T (shift σ m x) = shift σ m x := by
  rw [proj_shift]
  congr 1
  exact proj_of_subset hST hx

lemma phi_inl (k : ℤ) (x : L1 V) : phi σ g k (x, 0) = x := by
  simp [phi_apply]

lemma lhigh_phi (hug : ∀ x, mulL V σ u (mulL V σ g x) = x) {k m : ℤ}
    (hm : IsUnit (1 - errL σ g u m)) {a b : L1 V} (ha : proj V (Ici (k - m)) a = a)
    (hb : proj V (Iic 0) b = b) : lhigh σ g u k m (phi σ g k (a, b)) = (a, b) := by
  have ha' : proj V (Ici 0) (shift σ (m - k) a) = shift σ (m - k) a :=
    proj_shift_of_proj (fun j hj ↦ by simp only [mem_Ici] at hj ⊢; omega) ha
  have hphi : shift σ (m - k) (phi σ g k (a, b)) = phi σ g m (shift σ (m - k) a, b) := by
    rw [phi_apply, phi_apply, map_sub, shift_shift, sub_add_cancel]
  obtain ⟨h1, h2⟩ := linv_phi hug hm ha' hb
  change (shift σ (k - m) (linvA σ g u m (shift σ (m - k) (phi σ g k (a, b)))),
    linvB σ g u m (shift σ (m - k) (phi σ g k (a, b)))) = (a, b)
  rw [hphi, h1, h2, shift_shift, show k - m + (m - k) = 0 by ring, shift_zero_apply]

lemma phi_sol (hgu : ∀ x, mulL V σ g (mulL V σ u x) = x) {k : ℤ}
    (hk : IsUnit (1 - errR σ g u k)) (m : ℤ) (x : L1 V) : phi σ g k (sol σ g u k m x) = x := by
  change phi σ g k (lhigh σ g u k m x +
    rinv σ g u k (x - phi σ g k (lhigh σ g u k m x))) = x
  rw [map_add, phi_rinv hgu hk, add_sub_cancel]

lemma phi_recon (hgu : ∀ x, mulL V σ g (mulL V σ u x) = x) {k : ℤ}
    (hk : IsUnit (1 - errR σ g u k)) (m : ℤ) (x : L1 V) : phi σ g k (recon σ g u k m x) = 0 := by
  change phi σ g k ((x, 0) - sol σ g u k m x) = 0
  rw [map_sub, phi_inl, phi_sol hgu hk, sub_self]

/-- An element `(a, b)` of the kernel of `phi σ g k` is recovered by `recon` from the terms of `a`
of degree less than `k - m`. -/
lemma recon_proj (hug : ∀ x, mulL V σ u (mulL V σ g x) = x) {k m : ℤ}
    (hm : IsUnit (1 - errL σ g u m)) {a b : L1 V} (hb : proj V (Iic 0) b = b)
    (hab : phi σ g k (a, b) = 0) : recon σ g u k m (proj V (Iio (k - m)) a) = (a, b) := by
  set p := proj V (Iio (k - m)) a
  have hsplit : p + proj V (Ici (k - m)) a = a := by
    rw [← compl_Iio]
    exact proj_add_proj_compl _ a
  set xh : L1 V × L1 V := (proj V (Ici (k - m)) a, b)
  have hxh : phi σ g k xh = -p := by
    have h : phi σ g k (a, b) = phi σ g k (p, 0) + phi σ g k xh := by
      rw [← map_add]
      congr 1
      exact Prod.ext hsplit.symm (zero_add b).symm
    rw [hab, phi_inl] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hl : lhigh σ g u k m (phi σ g k xh) = xh :=
    lhigh_phi hug hm (by rw [proj_proj, inter_self]) hb
  have hsol : sol σ g u k m (phi σ g k xh) = xh := by
    change lhigh σ g u k m (phi σ g k xh) +
      rinv σ g u k (phi σ g k xh - phi σ g k (lhigh σ g u k m (phi σ g k xh))) = xh
    rw [hl, sub_self, map_zero, add_zero]
  have hsol' : sol σ g u k m p = -xh := by
    rw [← neg_neg p, map_neg, ← hxh, hsol]
  change (p, 0) - sol σ g u k m p = (a, b)
  rw [hsol', sub_neg_eq_add]
  exact Prod.ext hsplit (zero_add b)

lemma linvA_mem {m : ℤ} (hm : IsUnit (1 - errL σ g u m)) (y : L1 V) :
    proj V (Ici 0) (linvA σ g u m y) = linvA σ g u m y := by
  set w := proj V (Ici 0) ((1 - mulL V σ g ∘L proj V (Iic m) ∘L mulL V σ u) y)
  have hw : proj V (Ici 0) w = w := by rw [proj_proj, inter_self]
  set v := linvA σ g u m y
  have hv : (1 - errL σ g u m) v = w := by
    change ((1 - errL σ g u m) * Ring.inverse (1 - errL σ g u m)) w = w
    rw [Ring.mul_inverse_cancel _ hm]
    rfl
  have hv' : v = w + errL σ g u m v := by
    rw [← hv]
    simp
  have hK : proj V (Ici 0) (errL σ g u m v) = errL σ g u m v := by
    simp [errL, proj_proj]
  rw [hv', map_add, hw, hK]

lemma recon_fst_mem {k m : ℤ} (hm : IsUnit (1 - errL σ g u m)) (hkm : m ≤ k) {p : L1 V}
    (hp : proj V (Ici 0) p = p) : proj V (Ici 0) (recon σ g u k m p).1 = (recon σ g u k m p).1 := by
  change proj V (Ici 0) (p - (shift σ (k - m) (linvA σ g u m (shift σ (m - k) p)) +
    (rinv σ g u k (p - phi σ g k (lhigh σ g u k m p))).1)) =
    p - (shift σ (k - m) (linvA σ g u m (shift σ (m - k) p)) +
    (rinv σ g u k (p - phi σ g k (lhigh σ g u k m p))).1)
  rw [map_sub, map_add, hp, rinv_fst_mem,
    proj_shift_of_proj (S := Ici 0) (fun j hj ↦ by simp only [mem_Ici] at hj ⊢; omega)
      (linvA_mem hm _)]

lemma recon_snd_mem {k m : ℤ} (p : L1 V) :
    proj V (Iic 0) (recon σ g u k m p).2 = (recon σ g u k m p).2 := by
  change proj V (Iic 0) (0 - (shift σ (-m) (proj V (Iic m) (mulL V σ u
    ((linvA σ g u m - 1) (shift σ (m - k) p)))) +
    (rinv σ g u k (p - phi σ g k (lhigh σ g u k m p))).2)) =
    0 - (shift σ (-m) (proj V (Iic m) (mulL V σ u
    ((linvA σ g u m - 1) (shift σ (m - k) p)))) +
    (rinv σ g u k (p - phi σ g k (lhigh σ g u k m p))).2)
  rw [map_sub, map_add, map_zero, rinv_snd_mem,
    proj_shift_of_proj (S := Iic m) (fun j hj ↦ by simp only [mem_Iic] at hj ⊢; omega)
      (by rw [proj_proj, inter_self])]

end Recon
/-! ### Jets and the idempotent -/

section Jet

variable (σ V) in
/-- The first `D` coefficients of a Laurent series. -/
noncomputable def toJet (D : ℕ) : L1 V →L[ℂ] (Fin D → V) :=
  ContinuousLinearMap.pi fun i ↦ coeffCLM σ (i : ℤ)

variable (σ V) in
/-- The Laurent polynomial `∑_{i < D} cᵢ wⁱ`. -/
noncomputable def ofJet (D : ℕ) : (Fin D → V) →L[ℂ] L1 V :=
  ∑ i : Fin D, (lp.singleContinuousLinearMap ℂ (fun _ : ℤ ↦ V) 1 (i : ℤ)).comp
    ((wt σ i : ℂ) • ContinuousLinearMap.proj i)

omit [CompleteSpace V] hσ in
@[simp]
lemma toJet_apply (D : ℕ) (a : L1 V) (i : Fin D) : toJet V σ D a i = coeff σ a i := rfl

omit [CompleteSpace V] hσ in
lemma ofJet_apply (D : ℕ) (c : Fin D → V) (j : ℤ) :
    ofJet V σ D c j = ∑ i : Fin D, if j = i then (wt σ i : ℂ) • c i else 0 := by
  simp only [ofJet, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, lp.singleContinuousLinearMap_apply,
    smul_apply, ContinuousLinearMap.proj_apply]
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lp.coeFn_single, Pi.single_apply]

omit [CompleteSpace V] hσ in
lemma ofJet_apply_natCast (D : ℕ) (c : Fin D → V) (i : Fin D) :
    ofJet V σ D c (i : ℤ) = (wt σ i : ℂ) • c i := by
  rw [ofJet_apply, Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    rw [ite_eq_right]
    exact fun h ↦ hi' (Fin.ext (by exact_mod_cast h.symm))
  · simp

omit [CompleteSpace V] hσ in
lemma ofJet_apply_of_notMem (D : ℕ) (c : Fin D → V) {j : ℤ} (hj : j ∉ Ico (0 : ℤ) D) :
    ofJet V σ D c j = 0 := by
  rw [ofJet_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [ite_eq_right]
  rintro rfl
  exact hj ⟨by positivity, by exact_mod_cast i.2⟩

omit [CompleteSpace V] in
lemma ofJet_toJet (D : ℕ) (a : L1 V) : ofJet V σ D (toJet V σ D a) = proj V (Ico 0 D) a := by
  refine lp.ext <| funext fun j ↦ ?_
  rw [proj_apply]
  by_cases hj : j ∈ Ico (0 : ℤ) D
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj.1
    have hn : n < D := by exact_mod_cast hj.2
    rw [indicator_of_mem hj]
    have := ofJet_apply_natCast (σ := σ) D (toJet V σ D a) ⟨n, hn⟩
    simp only [Fin.val_mk] at this
    rw [this, toJet_apply, ← apply_eq_wt_smul_coeff (zero_lt_one.trans_le hσ.out)]
  · rw [ofJet_apply_of_notMem D _ hj, indicator_of_notMem hj]

omit [CompleteSpace V] hσ in
lemma proj_ofJet (D : ℕ) (c : Fin D → V) : proj V (Ici 0) (ofJet V σ D c) = ofJet V σ D c :=
  proj_eq_self_iff.2 fun _ hj ↦ ofJet_apply_of_notMem D c fun h ↦ hj h.1

variable (σ) (g u : L1 (V →L[ℂ] V))

/-- The endomorphism `c ↦ (the first `D` coefficients of `(recon σ g u k (k - D) c).1`)` of `V^D`.
It is idempotent and its image is identified with the kernel of `phi σ g k`
(`Laurent.L1.jetIdem_comp_self`, `Laurent.L1.jetIdem_toJet`). -/
noncomputable def jetIdem (k : ℤ) (D : ℕ) : (Fin D → V) →L[ℂ] (Fin D → V) :=
  toJet V σ D ∘L ContinuousLinearMap.fst ℂ (L1 V) (L1 V) ∘L recon σ g u k (k - D) ∘L ofJet V σ D

variable {σ g u}

/-- A pair `(a, b)` in the kernel of `phi σ g k` is determined by the first `D` coefficients of
`a`. -/
lemma recon_ofJet_toJet (hug : ∀ x, mulL V σ u (mulL V σ g x) = x) {k : ℤ} {D : ℕ}
    (hm : IsUnit (1 - errL σ g u (k - D))) {a b : L1 V} (ha : proj V (Ici 0) a = a)
    (hb : proj V (Iic 0) b = b) (hab : phi σ g k (a, b) = 0) :
    recon σ g u k (k - D) (ofJet V σ D (toJet V σ D a)) = (a, b) := by
  have h := recon_proj hug hm hb hab
  rw [sub_sub_cancel] at h
  have e : proj V (Ico 0 D) a = proj V (Iio D) a := by
    rw [← ha, proj_proj, proj_proj, show Ico (0 : ℤ) D ∩ Ici 0 = Iio (D : ℤ) ∩ Ici 0 by
      ext j; simp only [mem_Ico, mem_inter_iff, mem_Iio, mem_Ici]; omega]
  rw [ofJet_toJet, e, h]

lemma jetIdem_toJet (hug : ∀ x, mulL V σ u (mulL V σ g x) = x) {k : ℤ} {D : ℕ}
    (hm : IsUnit (1 - errL σ g u (k - D))) {a b : L1 V} (ha : proj V (Ici 0) a = a)
    (hb : proj V (Iic 0) b = b) (hab : phi σ g k (a, b) = 0) :
    jetIdem σ g u k D (toJet V σ D a) = toJet V σ D a := by
  change toJet V σ D (recon σ g u k (k - D) (ofJet V σ D (toJet V σ D a))).1 = _
  rw [recon_ofJet_toJet hug hm ha hb hab]

lemma phi_recon_ofJet (hgu : ∀ x, mulL V σ g (mulL V σ u x) = x) {k : ℤ}
    (hk : IsUnit (1 - errR σ g u k)) (D : ℕ) (c : Fin D → V) :
    phi σ g k (recon σ g u k (k - D) (ofJet V σ D c)) = 0 :=
  phi_recon hgu hk _ _

lemma jetIdem_comp_self (hgu : ∀ x, mulL V σ g (mulL V σ u x) = x)
    (hug : ∀ x, mulL V σ u (mulL V σ g x) = x) {k : ℤ} {D : ℕ}
    (hk : IsUnit (1 - errR σ g u k)) (hm : IsUnit (1 - errL σ g u (k - D))) :
    jetIdem σ g u k D ∘L jetIdem σ g u k D = jetIdem σ g u k D := by
  ext1 c
  set x := recon σ g u k (k - D) (ofJet V σ D c)
  have hx1 : proj V (Ici 0) x.1 = x.1 :=
    recon_fst_mem hm (by omega) (proj_ofJet D c)
  have hx2 : proj V (Iic 0) x.2 = x.2 := recon_snd_mem _
  have hx : phi σ g k (x.1, x.2) = 0 := phi_recon_ofJet hgu hk D c
  change toJet V σ D (recon σ g u k (k - D) (ofJet V σ D (toJet V σ D x.1))).1 = toJet V σ D x.1
  rw [recon_ofJet_toJet hug hm hx1 hx2 hx]

end Jet
/-! ### Norm bounds -/

section Bounds

variable {g u : L1 (V →L[ℂ] V)}

lemma norm_errR_le (k : ℤ) : ‖errR σ g u k‖ ≤ ‖g‖ * ‖proj _ (Ioi k) u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  change ‖mulL V σ g (proj V (Ioi k) (mulL V σ u (proj V (Iio 0) x)))‖ ≤ _
  calc _ ≤ ‖g‖ * ‖proj V (Ioi k) (mulL V σ u (proj V (Iio 0) x))‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_mulL_le _)
    _ ≤ ‖g‖ * (‖proj _ (Ioi k) u‖ * ‖x‖) := by
        gcongr
        exact norm_proj_Ioi_mulL_proj_Iio_le u k x
    _ = _ := by ring

lemma norm_errL_le (m : ℤ) : ‖errL σ g u m‖ ≤ ‖g‖ * ‖proj _ (Iic m) u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  change ‖proj V (Ici 0) (mulL V σ g (proj V (Iic m) (mulL V σ u (proj V (Ici 0) x))))‖ ≤ _
  calc _ ≤ ‖mulL V σ g (proj V (Iic m) (mulL V σ u (proj V (Ici 0) x)))‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (norm_proj_le _))
    _ ≤ ‖g‖ * ‖proj V (Iic m) (mulL V σ u (proj V (Ici 0) x))‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_mulL_le _)
    _ ≤ ‖g‖ * (‖proj _ (Iic m) u‖ * ‖x‖) := by
        gcongr
        exact norm_proj_Iic_mulL_proj_Ici_le u m x
    _ = _ := by ring

end Bounds

/-! ### Holomorphic dependence on `g` and `u` -/

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
  {g u : E → L1 (V →L[ℂ] V)}

lemma differentiableOn_clm_prod {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {A : E → X →L[ℂ] Y} {B : E → X →L[ℂ] Z} (hA : DifferentiableOn ℂ A s)
    (hB : DifferentiableOn ℂ B s) : DifferentiableOn ℂ (fun z ↦ (A z).prod (B z)) s := by
  have := (ContinuousLinearMap.prodL ℂ : ((X →L[ℂ] Y) × (X →L[ℂ] Z)) ≃L[ℂ] (X →L[ℂ] Y × Z))
    |>.differentiable.comp_differentiableOn (hA.prodMk hB)
  simpa [Function.comp_def] using this

variable (hg : DifferentiableOn ℂ g s) (hu : DifferentiableOn ℂ u s)
include hg hu

lemma differentiableOn_rinv {k : ℤ} (hk : ∀ z ∈ s, IsUnit (1 - errR σ (g z) (u z) k)) :
    DifferentiableOn ℂ (fun z ↦ rinv σ (g z) (u z) k) s := by
  have hE : DifferentiableOn ℂ (fun z ↦ errR σ (g z) (u z) k) s := by
    unfold errR
    fun_prop
  have hI := ((differentiableOn_const 1).sub hE).inverse hk
  have h₀ : DifferentiableOn ℂ (fun z ↦ rinv₀ σ (u z) k) s := by
    unfold rinv₀
    exact differentiableOn_clm_prod (differentiableOn_const _) (by fun_prop)
  exact h₀.clm_comp hI

lemma differentiableOn_linvA {m : ℤ} (hm : ∀ z ∈ s, IsUnit (1 - errL σ (g z) (u z) m)) :
    DifferentiableOn ℂ (fun z ↦ linvA σ (g z) (u z) m) s := by
  have hE : DifferentiableOn ℂ (fun z ↦ errL σ (g z) (u z) m) s := by
    unfold errL
    fun_prop
  have hI := ((differentiableOn_const 1).sub hE).inverse hm
  unfold linvA
  exact hI.clm_comp (by fun_prop)

lemma differentiableOn_linvB {m : ℤ} (hm : ∀ z ∈ s, IsUnit (1 - errL σ (g z) (u z) m)) :
    DifferentiableOn ℂ (fun z ↦ linvB σ (g z) (u z) m) s := by
  have hA := differentiableOn_linvA hg hu hm
  unfold linvB
  fun_prop

lemma differentiableOn_recon {k : ℤ} {D : ℕ} (hk : ∀ z ∈ s, IsUnit (1 - errR σ (g z) (u z) k))
    (hm : ∀ z ∈ s, IsUnit (1 - errL σ (g z) (u z) (k - D))) :
    DifferentiableOn ℂ (fun z ↦ recon σ (g z) (u z) k (k - D)) s := by
  have hA := differentiableOn_linvA hg hu hm
  have hB := differentiableOn_linvB hg hu hm
  have hR := differentiableOn_rinv hg hu hk
  have hL : DifferentiableOn ℂ (fun z ↦ lhigh σ (g z) (u z) k (k - D)) s := by
    unfold lhigh
    exact differentiableOn_clm_prod (by fun_prop) (by fun_prop)
  have hphi : DifferentiableOn ℂ (fun z ↦ phi σ (g z) k) s := by
    unfold phi
    fun_prop
  unfold recon sol
  fun_prop

lemma differentiableOn_jetIdem {k : ℤ} {D : ℕ} (hk : ∀ z ∈ s, IsUnit (1 - errR σ (g z) (u z) k))
    (hm : ∀ z ∈ s, IsUnit (1 - errL σ (g z) (u z) (k - D))) :
    DifferentiableOn ℂ (fun z ↦ jetIdem σ (g z) (u z) k D) s := by
  have hrec := differentiableOn_recon hg hu hk hm
  unfold jetIdem
  fun_prop

end Holomorphic

end L1

end Laurent
