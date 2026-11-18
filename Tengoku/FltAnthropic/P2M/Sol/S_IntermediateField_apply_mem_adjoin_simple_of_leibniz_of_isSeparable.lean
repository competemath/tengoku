import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_apply_mem_adjoin_simple_of_leibniz_of_isSeparable.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_apply_mem_adjoin_simple_of_leibniz_of_isSeparable
set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace DerivStable

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section Calculus
variable (D : L → L) (hadd : ∀ a b : L, D (a + b) = D a + D b) (hmul : ∀ a b : L, D (a * b) = a * D b + b * D a)
include hadd hmul

def addHom : L →+ L := AddMonoidHom.mk' D hadd

omit hmul in
/--
@isnad1 id=eq.1h3v.s7.016eafc3f807 from=translated src=- shape=1fd55361 vocab=73a442d6
-/
theorem addHom_apply (x : L) : addHom D hadd x = D x := rfl

omit hmul in
/--
@isnad1 id=eq.1h2v.s6.7b2273a29e0a from=translated src=- shape=514771b9 vocab=fe483021
-/
theorem map_zero' : D 0 = 0 := (addHom D hadd).map_zero

omit hadd in
/--
@isnad1 id=eq.1h2v.s7.bbcc8cce409e from=translated src=- shape=f56247c2 vocab=8f4da391
-/
theorem map_one' : D 1 = 0 := by
  have h := hmul 1 1
  rw [one_mul, one_mul] at h
  linear_combination -h

omit hadd in
/--
@isnad1 id=eq.1h4v.s7.af5a96a3e66e from=translated src=- shape=8f521945 vocab=66608009
-/
theorem map_pow' (a : L) (n : ℕ) : D (a ^ (n + 1)) = ((n + 1 : ℕ) : L) * a ^ n * D a := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, hmul, ih]
    push_cast
    ring

/--
@isnad1 id=eq.2h4v.s8.ac09c47c376c from=translated src=- shape=60352313 vocab=135f908b
-/
theorem map_pow'' (a : L) (n : ℕ) : D (a ^ n) = (n : L) * a ^ (n - 1) * D a := by
  cases n with
  | zero => rw [pow_zero, map_one' D hmul]; simp
  | succ k => rw [map_pow' D hmul, Nat.add_sub_cancel]

/--
@isnad1 id=eq.3h3v.s8.0d965979efdc from=translated src=- shape=6d55dd3d vocab=0b2bd111
-/
theorem map_inv' (a : L) (ha : a ≠ 0) : D a⁻¹ = -(a⁻¹ ^ 2) * D a := by
  have h := hmul a a⁻¹
  rw [mul_inv_cancel₀ ha, map_one' D hmul] at h
  have h' : a * D a⁻¹ = -(a⁻¹ * D a) := eq_neg_of_add_eq_zero_left h.symm
  calc D a⁻¹ = a⁻¹ * (a * D a⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    _ = a⁻¹ * -(a⁻¹ * D a) := by rw [h']
    _ = -(a⁻¹ ^ 2) * D a := by ring

/--
@isnad1 id=eq.2h5v.s8.43c23082bab7 from=translated src=- shape=ef30801e vocab=92778461
-/
theorem apply_sum_mul_pow (c : ℕ → L) (x : L) (n : ℕ) :
    D (∑ i ∈ Finset.range n, c i * x ^ i) =
      ∑ i ∈ Finset.range n, x ^ i * D (c i) + (∑ i ∈ Finset.range n, c i * i * x ^ (i - 1)) * D x := by
  rw [← addHom_apply D hadd, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [addHom_apply, hmul, map_pow'' D hadd hmul]
  ring

/--
@isnad1 id=mem.4h5v.s9.eab801806a30 from=translated src=- shape=fc19fa5f vocab=78852ff4
-/
theorem apply_gen_mem (F : IntermediateField K L) (hF : ∀ x : L, x ∈ F → D x ∈ F)
    (α : L) (hα : IsSeparable F α) : D α ∈ IntermediateField.adjoin F ({α} : Set L) := by
  set E := IntermediateField.adjoin F ({α} : Set L) with hE
  have hαE : α ∈ E := IntermediateField.subset_adjoin F _ (Set.mem_singleton α)
  set m : Polynomial F := minpoly F α with hm
  set d : ℕ := m.natDegree with hd
  set c : ℕ → L := fun i => algebraMap F L (m.coeff i) with hc
  have hcF : ∀ i, c i ∈ F := fun i => (m.coeff i).2
  have heval : ∑ i ∈ Finset.range (d + 1), c i * α ^ i = 0 := by
    have h0 : aeval α m = 0 := minpoly.aeval F α
    rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range' (p := m.map (algebraMap F L))
      (lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self d))] at h0
    simpa only [coeff_map] using h0
  have hsep : aeval α (derivative m) ≠ 0 :=
    Polynomial.Separable.aeval_derivative_ne_zero hα (minpoly.aeval F α)
  have hder : aeval α (derivative m) = ∑ i ∈ Finset.range (d + 1), c i * i * α ^ (i - 1) := by
    rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range' (n := d + 1) (p := (derivative m).map (algebraMap F L))
      (lt_of_le_of_lt natDegree_map_le (lt_of_le_of_lt (natDegree_derivative_le m) (by omega)))]
    rw [Finset.sum_range_succ' (fun i => c i * i * α ^ (i - 1))]
    simp only [coeff_map, coeff_derivative, Nat.cast_zero, mul_zero, zero_mul, add_zero, hc, map_mul,
      Nat.add_sub_cancel]
    have hlast : m.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Finset.sum_range_succ]
    simp [hlast]
  have hD := congrArg D heval
  rw [apply_sum_mul_pow D hadd hmul, map_zero' D hadd, ← hder] at hD
  have hDα : D α = -(∑ i ∈ Finset.range (d + 1), α ^ i * D (c i)) / aeval α (derivative m) := by
    rw [eq_div_iff hsep]
    linear_combination hD
  rw [hDα]
  refine div_mem (neg_mem (sum_mem fun i _ => mul_mem (pow_mem hαE i) ?_)) ?_
  · exact IntermediateField.algebraMap_mem E ⟨D (c i), hF _ (hcF i)⟩
  · rw [hder]
    exact sum_mem fun i _ => mul_mem (mul_mem (IntermediateField.algebraMap_mem E ⟨c i, hcF i⟩)
      (by exact_mod_cast natCast_mem E i)) (pow_mem hαE _)

/--
@isnad1 id=mem.5h6v.s9.ad432692daa6 from=translated src=- shape=6e3b274f vocab=78852ff4
-/
theorem main (F : IntermediateField K L) (hF : ∀ x : L, x ∈ F → D x ∈ F)
    (α : L) (hα : IsSeparable F α) (x : L) (hx : x ∈ IntermediateField.adjoin F ({α} : Set L)) :
    D x ∈ IntermediateField.adjoin F ({α} : Set L) := by
  set E := IntermediateField.adjoin F ({α} : Set L) with hE
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact apply_gen_mem D hadd hmul F hF _ hα
  | algebraMap x =>
    exact IntermediateField.algebraMap_mem E ⟨D (algebraMap F L x), hF _ x.2⟩
  | add x y hx hy ihx ihy =>
    rw [hadd]; exact add_mem ihx ihy
  | inv x hx ihx =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [inv_zero, map_zero' D hadd]; exact zero_mem E
    · rw [map_inv' D hadd hmul x hx0]
      exact mul_mem (neg_mem (pow_mem (inv_mem hx) 2)) ihx
  | mul x y hx hy ihx ihy =>
    rw [hmul]
    exact add_mem (mul_mem hx ihy) (mul_mem hy ihx)

end Calculus

end DerivStable

/--
@isnad1 id=mem.5h6v.s9.ad432692daa6 from=translated src=- shape=6e3b274f vocab=78852ff4
-/
theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : L → L) (hadd : ∀ a b : L, D (a + b) = D a + D b) (hmul : ∀ a b : L, D (a * b) = a * D b + b * D a)
    (F : IntermediateField K L) (hF : ∀ x : L, x ∈ F → D x ∈ F)
    (α : L) (hα : IsSeparable F α) (x : L) (hx : x ∈ IntermediateField.adjoin F ({α} : Set L)) :
    D x ∈ IntermediateField.adjoin F ({α} : Set L) :=
  DerivStable.main D hadd hmul F hF α hα x hx
