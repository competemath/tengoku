import Tengoku
import Tengoku.FixedPointTheoremsLean4.FixedPointTheorems.cubical_sperner

open Classical

/-
shows the fixed-point theorem for the unit cube
by applying the cubical sperner's lemma
-/

variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by {
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    }
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    }
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by {
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  }
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    suffices h3 : k1 ∈ s by {
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    }
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  }
  {
    intro h2
    have h3 : k1 ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    }
    exact Finset.min_le_of_eq h3 hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  {
    intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  }
  {
    intro h2
    apply (h1.2 k).2
    exact Or.inr h2
  }
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_ofPred_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    {
      intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    }
    {
      intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    }
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}
