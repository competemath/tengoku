import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.MixtureIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace OddCycleBound.DenseRegion

def momentConv (s : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | r + 1, j => ∑ k ∈ Finset.range (j + 1), s k * momentConv s r (j - k)

@[simp] lemma momentConv_zero_zero (s : ℕ → ℝ) : momentConv s 0 0 = 1 := rfl

@[simp] lemma momentConv_zero_succ (s : ℕ → ℝ) (j : ℕ) :
    momentConv s 0 (j + 1) = 0 := by
  simp [momentConv]

lemma momentConv_succ (s : ℕ → ℝ) (r j : ℕ) :
    momentConv s (r + 1) j =
      ∑ k ∈ Finset.range (j + 1), s k * momentConv s r (j - k) := rfl

lemma momentConv_congr_of_le {s t : ℕ → ℝ} : ∀ (r j : ℕ),
    (∀ k ≤ j, s k = t k) → momentConv s r j = momentConv t r j
  | 0, j, _ => by cases j <;> rfl
  | r + 1, j, h => by
      rw [momentConv_succ, momentConv_succ]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := by
        rw [Finset.mem_range] at hk
        omega
      rw [h k hk_le, momentConv_congr_of_le r (j - k)
        (fun ell hell => h ell (by omega))]

noncomputable def momentShiftTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m - 2 * r + 1),
    ((m / r : ℝ) *
      ((Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          (1 - q) ^ (m - 2 * r - j) * (-1 : ℝ) ^ j
        + (Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) *
          q ^ (m - 2 * r - j))) * momentConv s r j

noncomputable def momentPathTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m - 2 * r + 1),
    (if j < m - 2 * r then
        (Nat.choose (m - 2 * r - 1 - j + r) r : ℝ) * q ^ (m - 2 * r - 1 - j)
      else 0) * momentConv s r j

noncomputable def momentPhiTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  momentShiftTerm m r q s - momentPathTerm m r q s

noncomputable def momentPhi (m : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range ((m - 1) / 2), momentPhiTerm m (k + 1) q s

theorem momentPhi_congr_of_le {m : ℕ} (q : ℝ) {s t : ℕ → ℝ}
    (h : ∀ j ≤ m, s j = t j) :
    momentPhi m q s = momentPhi m q t := by
  unfold momentPhi momentPhiTerm momentShiftTerm momentPathTerm
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1 <;> refine Finset.sum_congr rfl fun j hj => ?_
  all_goals
    rw [momentConv_congr_of_le _ _ fun ell hell => h ell (by
      have hjlt : j < m - 2 * (k + 1) + 1 := Finset.mem_range.mp hj
      omega)]

noncomputable def momentKernelTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m - 2 * r + 1), kerB m r q j * momentConv s r j

noncomputable def momentKernelExpansion (m : ℕ) (q : ℝ) (s : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range ((m - 1) / 2), momentKernelTerm m (k + 1) q s

lemma momentPhiTerm_eq_momentKernelTerm (m r : ℕ) (q : ℝ) (s : ℕ → ℝ) :
    momentPhiTerm m r q s = momentKernelTerm m r q s := by
  unfold momentPhiTerm momentShiftTerm momentPathTerm momentKernelTerm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold kerB
  ring

theorem momentPhi_eq_momentKernelExpansion (m : ℕ) (q : ℝ) (s : ℕ → ℝ) :
    momentPhi m q s = momentKernelExpansion m q s := by
  unfold momentPhi momentKernelExpansion
  refine Finset.sum_congr rfl fun k _ => ?_
  exact momentPhiTerm_eq_momentKernelTerm m (k + 1) q s

variable {ι : Type*} [Fintype ι]

noncomputable def atomicIntegral (w lam : ι → ℝ) : ℕ → (List ℝ → ℝ) → ℝ
  | 0, F => F []
  | r + 1, F => ∑ i, w i * atomicIntegral w lam r (fun L => F (lam i :: L))

noncomputable def atomicMoment (w lam : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ i, w i * lam i ^ j

@[simp] lemma atomicIntegral_zero (w lam : ι → ℝ) (r : ℕ) :
    atomicIntegral w lam r (fun _ => 0) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [atomicIntegral, ih]

lemma atomicIntegral_add (w lam : ι → ℝ) (r : ℕ) (F G : List ℝ → ℝ) :
    atomicIntegral w lam r (fun L => F L + G L) =
      atomicIntegral w lam r F + atomicIntegral w lam r G := by
  induction r generalizing F G with
  | zero => rfl
  | succ r ih =>
      simp only [atomicIntegral]
      simp_rw [ih, mul_add, Finset.sum_add_distrib]

lemma atomicIntegral_const_mul (w lam : ι → ℝ) (r : ℕ) (c : ℝ) (F : List ℝ → ℝ) :
    atomicIntegral w lam r (fun L => c * F L) = c * atomicIntegral w lam r F := by
  induction r generalizing c F with
  | zero => rfl
  | succ r ih =>
      simp only [atomicIntegral]
      simp_rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring

lemma atomicIntegral_finset_sum {κ : Type*} (w lam : ι → ℝ) (r : ℕ)
    (t : Finset κ) (F : κ → List ℝ → ℝ) :
    atomicIntegral w lam r (fun L => ∑ k ∈ t, F k L) =
      ∑ k ∈ t, atomicIntegral w lam r (F k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [atomicIntegral_zero]
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      rw [atomicIntegral_add, ih]

lemma atomicIntegral_hsym (w lam : ι → ℝ) : ∀ (r j : ℕ),
    atomicIntegral w lam r (fun L => hsym L j) = momentConv (atomicMoment w lam) r j
  | 0, j => by
      simp [atomicIntegral, momentConv, hsym_nil]
  | r + 1, j => by
      rw [momentConv_succ]
      simp only [atomicIntegral]
      have hinner : ∀ i : ι,
          atomicIntegral w lam r (fun L => hsym (lam i :: L) j) =
            ∑ k ∈ Finset.range (j + 1),
              lam i ^ k * momentConv (atomicMoment w lam) r (j - k) := by
        intro i
        simp_rw [hsym_cons]
        rw [atomicIntegral_finset_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [atomicIntegral_const_mul, atomicIntegral_hsym w lam r (j - k)]
      simp_rw [hinner, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold atomicMoment
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring

noncomputable def atomicKernelTerm (m r : ℕ) (q : ℝ) (w lam : ι → ℝ) : ℝ :=
  atomicIntegral w lam r (multiKernel m r q)

theorem atomicKernelTerm_eq_momentKernelTerm {m r : ℕ} (hr : r ≠ 0)
    (hn : 1 ≤ m - 2 * r) (q : ℝ) (w lam : ι → ℝ) :
    atomicKernelTerm m r q w lam = momentKernelTerm m r q (atomicMoment w lam) := by
  unfold atomicKernelTerm momentKernelTerm
  have hexpand : multiKernel m r q = fun L =>
      ∑ j ∈ Finset.range (m - 2 * r + 1), kerB m r q j * hsym L j := by
    funext L
    exact multiKernel_expand hr hn q L
  rw [hexpand, atomicIntegral_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [atomicIntegral_const_mul, atomicIntegral_hsym]

lemma atomicIntegral_nonneg_of (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (P : ℝ → Prop) : ∀ (r : ℕ) (F : List ℝ → ℝ),
      (∀ L, L.length = r → (∀ x ∈ L, P x) → 0 ≤ F L) →
      (∀ i, P (lam i)) → 0 ≤ atomicIntegral w lam r F
  | 0, F, hF, _ => by
      exact hF [] rfl (by simp)
  | r + 1, F, hF, hP => by
      simp only [atomicIntegral]
      refine Finset.sum_nonneg fun i _ => mul_nonneg (hw i) ?_
      refine atomicIntegral_nonneg_of w lam hw P r (fun L => F (lam i :: L)) ?_ hP
      intro L hlen hL
      apply hF (lam i :: L)
      · simp [hlen]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hP i
        · exact hL x hx

/-- Lemma 3.3 for an atomic measure: the `r`-th excursion term is nonnegative as soon as the
excursion polynomial `P_{m,r}` is nonnegative at all atoms.-/
theorem momentKernelTerm_nonneg_of_atomic' {m r : ℕ} (hr : r ≠ 0)
    (hn : 1 ≤ m - 2 * r) (q : ℝ) (w lam : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hP : ∀ L : List ℝ, L.length = r → (∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) →
      0 ≤ multiKernel m r q L) :
    0 ≤ momentKernelTerm m r q (atomicMoment w lam) := by
  rw [← atomicKernelTerm_eq_momentKernelTerm hr hn]
  unfold atomicKernelTerm
  exact atomicIntegral_nonneg_of w lam hw
    (fun x => x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) r (multiKernel m r q) hP hlam

theorem momentKernelTerm_nonneg_of_atomic {m r : ℕ} (hr : r ≠ 0)
    (hn : 1 ≤ m - 2 * r) (q : ℝ) (w lam : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hdiag : ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
      0 ≤ diagKernel m r q ell) :
    0 ≤ momentKernelTerm m r q (atomicMoment w lam) :=
  momentKernelTerm_nonneg_of_atomic' hr hn q w lam hw hlam fun L hlen hL =>
    multiKernel_nonneg hr hn q L hlen hdiag hL

theorem momentPhi_nonneg_of_atomic' {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (q : ℝ) (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hP : ∀ r, 1 ≤ r → 2 * r < m → ∀ L : List ℝ, L.length = r →
      (∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) → 0 ≤ multiKernel m r q L) :
    0 ≤ momentPhi m q (atomicMoment w lam) := by
  rw [momentPhi_eq_momentKernelExpansion]
  unfold momentKernelExpansion
  refine Finset.sum_nonneg fun k hk => ?_
  have hklt : k < (m - 1) / 2 := Finset.mem_range.mp hk
  have hr1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hrm : 2 * (k + 1) < m := by
    rcases hm with ⟨t, ht⟩
    omega
  have hn : 1 ≤ m - 2 * (k + 1) := by omega
  exact momentKernelTerm_nonneg_of_atomic' (r := k + 1) (by omega) hn q w lam hw hlam
    (hP (k + 1) hr1 hrm)

theorem momentPhi_nonneg_of_atomic {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (q : ℝ) (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hlam : ∀ i, lam i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2))
    (hdiag : ∀ r, 1 ≤ r → 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), 0 ≤ diagKernel m r q ell) :
    0 ≤ momentPhi m q (atomicMoment w lam) :=
  momentPhi_nonneg_of_atomic' hm hm3 q w lam hw hlam fun r hr hrm L hlen hL =>
    multiKernel_nonneg (by omega) (by omega) q L hlen (hdiag r hr hrm) hL

end OddCycleBound.DenseRegion
