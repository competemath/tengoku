import Tengoku.OpenaiMath.OAI.Analysis.RecursivePotentials.TreeGeometry

namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

instance : Infinite JoinedNode := by
  apply Infinite.of_injective (fun n : ℕ => (some ⟨⟨n + 1, by omega⟩, ⟨[], by simp⟩⟩ : JoinedNode))
  intro n m h
  have he := congrArg (fun x : JoinedNode => x.map (fun y => y.1.val)) h
  simpa using he

theorem XSigma_averaged_modulus {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t ^ 3 / 128 ≤ averagedModulus XSigma t :=
  TreeSpace.averaged_modulus_cubic sequenceTree ht ht1

theorem XJoined_averaged_modulus {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t ^ 3 / 128 ≤ averagedModulus XJoined t :=
  TreeSpace.averaged_modulus_cubic joinedTree ht ht1

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma inclusion_apply (v : ZeroTreeVector T) : inclusion T v = toTree T v := rfl

@[simp] lemma inclusion_projection (H : Finset ι) (hH : T.Initial H) (v : ZeroTreeVector T) :
    inclusion T (projection T H hH v) = TreeVector.projection T H hH (inclusion T v) := rfl

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma inclusion_coe (v : ZeroTreeVector T) :
    inclusion T (v : ZeroTreeSpace T) = (ZeroTreeVector.inclusion T v : TreeSpace T) :=
  ContinuousLinearMap.completion_apply_coe _ v

@[simp] lemma projection_coe (H : Finset ι) (hH : T.Initial H) (v : ZeroTreeVector T) :
    projection T H hH (v : ZeroTreeSpace T) =
      (ZeroTreeVector.projection T H hH v : ZeroTreeSpace T) :=
  ContinuousLinearMap.completion_apply_coe _ v

end ZeroTreeSpace

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def headCoordinates (H : Finset ι) : ZeroTreeSpace T →L[ℝ] (H → ℝ) :=
  (TreeSpace.headCoordinates T H).comp (inclusion T)

end ZeroTreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma depth_le_of_mem_ancestors (s : ι) {c : ι} (hc : c ∈ T.ancestors s) :
    T.depth c ≤ T.depth s := by
  rw [ancestors] at hc
  split_ifs at hc with hs
  · have he := Finset.mem_singleton.mp hc
    subst c
    exact le_rfl
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact le_rfl
    · exact (depth_le_of_mem_ancestors (T.parent s) hc).trans (T.parent_depth s hs).le
termination_by T.depth s

decreasing_by exact T.parent_depth s hs

lemma parent_ancestors_injective (s : ι) {a b : ι} (ha : a ∈ T.ancestors s)
    (hb : b ∈ T.ancestors s) (ha0 : a ≠ T.root) (hb0 : b ≠ T.root)
    (he : T.parent a = T.parent b) : a = b := by
  rw [ancestors] at ha hb
  split_ifs at ha hb with hs
  · exact (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm
  · rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · rfl
      · have h₁ := T.depth_le_of_mem_ancestors (T.parent a) hb
        have h₂ := T.parent_depth b hb0
        rw [he] at h₁
        omega
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · have h₁ := T.depth_le_of_mem_ancestors (T.parent b) ha
        have h₂ := T.parent_depth a ha0
        rw [← he] at h₁
        omega
      · exact parent_ancestors_injective (T.parent s) ha hb ha0 hb0 he
termination_by T.depth s

decreasing_by exact T.parent_depth s hs

noncomputable def path (s : ι) : ι →₀ ℝ := extend (T.ancestors s) (fun _ => 1)

lemma path_apply (s c : ι) : T.path s c = if c ∈ T.ancestors s then 1 else 0 := by
  by_cases hc : c ∈ T.ancestors s
  · rw [path, extend_mem _ _ hc, ite_eq_left hc]
  · rw [path, extend_not_mem _ _ hc, ite_eq_right hc]

lemma path_nonneg (s c : ι) : 0 ≤ T.path s c := by
  rw [path_apply]
  split_ifs <;> norm_num

lemma path_root (s : ι) : T.path s T.root = 1 := by
  rw [path_apply, ite_eq_left (T.root_mem_ancestors s)]

lemma path_upper (s : ι) : T.GlobalUpper (T.path s) := by
  intro a S hS
  by_cases ha : a ∈ T.ancestors s
  · have hcard : (S.filter (fun c => c ∈ T.ancestors s)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro c hc d hd
      obtain ⟨hcS, hcA⟩ := Finset.mem_filter.mp hc
      obtain ⟨hdS, hdA⟩ := Finset.mem_filter.mp hd
      exact T.parent_ancestors_injective s hcA hdA (hS c hcS).1 (hS d hdS).1
        ((hS c hcS).2.trans (hS d hdS).2.symm)
    calc
      ∑ c ∈ S, T.path s c ^ 2 = ∑ c ∈ S.filter (fun c => c ∈ T.ancestors s), (1 : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro c hc
        rw [path_apply]
        split_ifs <;> norm_num
      _ = ((S.filter (fun c => c ∈ T.ancestors s)).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
      _ = T.path s a ^ 2 := by rw [path_apply, ite_eq_left ha]; norm_num
  · have hz : ∑ c ∈ S, T.path s c ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      have hcA : c ∉ T.ancestors s := by
        intro h
        have hpar := T.ancestors_parent_closed s h
        rw [(hS c hc).2] at hpar
        exact ha hpar
      rw [path_apply, ite_eq_right hcA]
      norm_num
    rw [hz]
    exact sq_nonneg _

lemma GlobalUpper.zero {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) :
    T.GlobalUpper (0 : ι → ℝ) := by
  intro s S hS
  simp

theorem path_fields (s c : ι) : T.P (T.path s) c = T.path s c ∧ T.Q (T.path s) c = 0 := by
  have h := T.potentials_minimal (T.path s) (T.path s) 0 (T.path_nonneg s)
    (fun _ => le_rfl) (fun _ => sub_zero _) (T.path_upper s) (GlobalUpper.zero T) c
  have hq : T.Q (T.path s) c = 0 := le_antisymm h.2 (T.Q_nonneg _ _)
  have hd := T.P_sub_Q (T.path s) c
  rw [hq, sub_zero] at hd
  exact ⟨hd, hq⟩

lemma normSum_path (s : ι) : T.normSum (T.path s) = 1 := by
  unfold normSum
  rw [(T.path_fields s T.root).1, (T.path_fields s T.root).2, T.path_root, add_zero]

lemma path_step (c : ι) (hc : c ≠ T.root) :
    T.path c = T.path (T.parent c) + Finsupp.single c 1 := by
  have hnot : c ∉ T.ancestors (T.parent c) := by
    intro h
    have h₁ := T.depth_le_of_mem_ancestors (T.parent c) h
    have h₂ := T.parent_depth c hc
    omega
  ext s
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rw [path_apply, path_apply, ancestors, dite_eq_right hc]
  by_cases hs : s = c
  · subst s
    simp [hnot]
  · have hs' : c ≠ s := Ne.symm hs
    simp [hs, hs']

lemma child_not_mem_ancestors {s c : ι} (hc : c ≠ T.root) (hp : T.parent c = s) :
    c ∉ T.ancestors s := by
  intro h
  have h₁ := T.depth_le_of_mem_ancestors s h
  have h₂ := T.parent_depth c hc
  rw [hp] at h₂
  omega

lemma child_function_zero_on_ancestors (s : ι) (b : ι → ℝ)
    (hb : ∀ c, b c ≠ 0 → c ≠ T.root ∧ T.parent c = s)
    {a : ι} (ha : a ∈ T.ancestors s) : b a = 0 := by
  by_contra hh
  exact T.child_not_mem_ancestors (hb a hh).1 (hb a hh).2 ha

lemma attached_upper (s : ι) (b : ι → ℝ) (hb0 : ∀ c, 0 ≤ b c)
    (hb : ∀ c, b c ≠ 0 → c ≠ T.root ∧ T.parent c = s)
    {R : ℝ} (hR : 0 ≤ R) (hsq : ∀ S : Finset ι, ∑ c ∈ S, b c ^ 2 ≤ R ^ 2) :
    T.GlobalUpper (fun c => R * T.path s c + b c) := by
  intro a S hS
  dsimp only
  by_cases ha : a = s
  · subst a
    have hzero := T.child_function_zero_on_ancestors s b hb (T.mem_ancestors_self s)
    have hsum : ∑ c ∈ S, (R * T.path s c + b c) ^ 2 = ∑ c ∈ S, b c ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [path_apply, ite_eq_right (T.child_not_mem_ancestors (hS c hc).1 (hS c hc).2)]
      ring
    have hself : T.path s s = 1 := by rw [path_apply, ite_eq_left (T.mem_ancestors_self s)]
    rw [hsum, hself, hzero, mul_one, add_zero]
    exact hsq S
  · have hsum : ∑ c ∈ S, (R * T.path s c + b c) ^ 2 = ∑ c ∈ S, (R * T.path s c) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      have hz : b c = 0 := by
        by_contra hh
        exact ha ((hS c hc).2.symm.trans (hb c hh).2)
      rw [hz, add_zero]
    rw [hsum]
    have hp := ((T.path_upper s).smul T R) a S hS
    simp only [Pi.smul_apply, smul_eq_mul] at hp
    have hnon : 0 ≤ R * T.path s a := mul_nonneg hR (T.path_nonneg s a)
    nlinarith [hb0 a, sq_nonneg (b a)]

lemma sum_sq_le_support (v : ι →₀ ℝ) (S : Finset ι) :
    ∑ c ∈ S, v c ^ 2 ≤ ∑ c ∈ v.support, v c ^ 2 := by
  have he : ∑ c ∈ S ∪ v.support, v c ^ 2 = ∑ c ∈ v.support, v c ^ 2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro c hc hn
    rw [Finsupp.notMem_support_iff.mp hn]
    norm_num
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun c hc hn => sq_nonneg _)

lemma positivePart_sq_le (a : ℝ) : max a 0 ^ 2 ≤ a ^ 2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
  · rw [max_eq_right (le_of_not_ge ha)]
    simpa using sq_nonneg a

theorem normSum_siblings_le (s : ι) (v : ι →₀ ℝ)
    (hv : ∀ c ∈ v.support, c ≠ T.root ∧ T.parent c = s) :
    T.normSum v ≤ 2 * Real.sqrt (∑ c ∈ v.support, v c ^ 2) := by
  let R := Real.sqrt (∑ c ∈ v.support, v c ^ 2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = ∑ c ∈ v.support, v c ^ 2 := Real.sq_sqrt
    (Finset.sum_nonneg (fun c hc => sq_nonneg _))
  let p : ι → ℝ := fun c => R * T.path s c + max (v c) 0
  let q : ι → ℝ := fun c => R * T.path s c + max (-v c) 0
  have hp : T.GlobalUpper p := by
    refine T.attached_upper s (fun c => max (v c) 0) (fun c => le_max_right _ _) ?_ hR ?_
    · intro c hc
      apply hv c (Finsupp.mem_support_iff.mpr ?_)
      intro he
      simp [he] at hc
    · intro S
      calc
        ∑ c ∈ S, max (v c) 0 ^ 2 ≤ ∑ c ∈ S, v c ^ 2 :=
          Finset.sum_le_sum (fun c hc => positivePart_sq_le _)
        _ ≤ R ^ 2 := by rw [hR2]; exact sum_sq_le_support v S
  have hq : T.GlobalUpper q := by
    refine T.attached_upper s (fun c => max (-v c) 0) (fun c => le_max_right _ _) ?_ hR ?_
    · intro c hc
      apply hv c (Finsupp.mem_support_iff.mpr ?_)
      intro he
      simp [he] at hc
    · intro S
      calc
        ∑ c ∈ S, max (-v c) 0 ^ 2 ≤ ∑ c ∈ S, v c ^ 2 := by
          apply Finset.sum_le_sum
          intro c hc
          simpa only [neg_sq] using positivePart_sq_le (-v c)
        _ ≤ R ^ 2 := by rw [hR2]; exact sum_sq_le_support v S
  have hdiff : ∀ c, p c - q c = v c := by
    intro c
    dsimp [p, q]
    by_cases hc : 0 ≤ v c
    · rw [max_eq_left hc, max_eq_right (neg_nonpos.mpr hc)]
      ring
    · have hcn := le_of_not_ge hc
      rw [max_eq_right hcn, max_eq_left (neg_nonneg.mpr hcn)]
      ring
  have hle := T.potentials_minimal v p q
    (fun c => add_nonneg (mul_nonneg hR (T.path_nonneg s c)) (le_max_right _ _))
    (fun c => add_nonneg (mul_nonneg hR (T.path_nonneg s c)) (le_max_right _ _))
    hdiff hp hq T.root
  have hv0 : v T.root = 0 := by
    by_contra h
    exact (hv T.root (Finsupp.mem_support_iff.mpr h)).1 rfl
  have hp0 : p T.root = R := by simp [p, T.path_root, hv0]
  have hq0 : q T.root = R := by simp [q, T.path_root, hv0]
  rw [hp0, hq0] at hle
  unfold normSum
  linarith

lemma twice_coordinate_le_normSum (v : ι →₀ ℝ) (hv : v T.root = 0) (s : ι) :
    2 * |v s| ≤ T.normSum v := by
  have hd := T.P_sub_Q v T.root
  rw [hv] at hd
  have hp := (T.P_upper v).le_root T (T.P_nonneg v) s
  have hq := (T.Q_upper v).le_root T (T.Q_nonneg v) s
  have hc := T.P_sub_Q v s
  have hp0 := T.P_nonneg v s
  have hq0 := T.Q_nonneg v s
  unfold normSum
  rcases le_total 0 (v s) with hs | hs
  · rw [abs_of_nonneg hs]
    linarith
  · rw [abs_of_nonpos hs]
    linarith

lemma normSum_single (c : ι) (hc : c ≠ T.root) :
    T.normSum (Finsupp.single c 1) = 2 := by
  have hl := T.twice_coordinate_le_normSum (Finsupp.single c 1) (by simp [hc]) c
  simp only [Finsupp.single_eq_same, abs_one, mul_one] at hl
  have hu := T.normSum_siblings_le (T.parent c) (Finsupp.single c 1) (by
    intro s hs
    have he : s = c := by simpa using hs
    subst s
    exact ⟨hc, rfl⟩)
  have hsum : ∑ s ∈ (Finsupp.single c (1 : ℝ)).support, (Finsupp.single c (1 : ℝ) s) ^ 2 = 1 := by
    simp
  rw [hsum, Real.sqrt_one, mul_one] at hu
  exact le_antisymm hu hl

noncomputable def cutPath (s : ι) : ι →₀ ℝ := T.path s - Finsupp.single T.root 1

lemma cutPath_root (s : ι) : T.cutPath s T.root = 0 := by
  simp [cutPath, T.path_root]

lemma normSum_cutPath (s : ι) (hs : s ≠ T.root) : T.normSum (T.cutPath s) = 2 := by
  have hv : T.cutPath s s = 1 := by
    simp [cutPath, path_apply, T.mem_ancestors_self, Ne.symm hs]
  have hl := T.twice_coordinate_le_normSum (T.cutPath s) (T.cutPath_root s) s
  rw [hv, abs_one, mul_one] at hl
  let b : ι → ℝ := (Finsupp.single T.root 1 : ι →₀ ℝ)
  have hb : T.GlobalUpper b := by
    intro a S hS
    have he : ∑ c ∈ S, b c ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      simp only [b, Finsupp.single_apply, ite_eq_right (Ne.symm (hS c hc).1), zero_pow (by omega : 2 ≠ 0)]
    rw [he]
    exact sq_nonneg _
  have hu := T.potentials_minimal (T.cutPath s) (T.path s) b (T.path_nonneg s)
    (fun c => by dsimp [b]; simp only [Finsupp.single_apply]; split_ifs <;> norm_num)
    (fun c => rfl) (T.path_upper s) hb T.root
  have hb0 : b T.root = 1 := by simp [b]
  rw [T.path_root, hb0] at hu
  unfold normSum
  exact le_antisymm (by linarith [hu.1, hu.2]) hl

lemma cutPath_step (c : ι) (hc : c ≠ T.root) :
    T.cutPath c - T.cutPath (T.parent c) = Finsupp.single c 1 := by
  unfold cutPath
  rw [T.path_step c hc]
  abel

end FiniteRootedTree

end RecursivePotentials

end

end OAI
