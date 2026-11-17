import Tengoku.PaperCLean.PaperC.Arithmetic.CertificateCount
import Tengoku.PaperCLean.PaperC.Arithmetic.StartResidue
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # CRT counts for allocations of all rough prime factors

Empty target blocks incur no factor three. The block bound is charged by
its number of assigned primes, so the total factor is 3^omega(r).
-/
namespace PaperC.Prel8.RoughKernelCRT
open Finset PaperC.CRT
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {ι : Type*}

def solutions (n : ℕ) (S : Finset ι) (modulus offset : ι → ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun x ↦ ∀ i ∈ S, modulus i ∣ x + offset i)

/-- Membership without exposing the implementation of finite universal decidability.-/
theorem mem_solutions (n : ℕ) (S : Finset ι) (modulus offset : ι → ℕ) (x : ℕ) :
    x ∈ solutions n S modulus offset ↔ x ∈ Icc 1 n ∧ ∀ i ∈ S, modulus i ∣ x + offset i := by
  classical
  exact mem_filter

/-- Exact elementary CRT count, including the empty certificate.-/
theorem solutions_count (n : ℕ) (S : Finset ι) (modulus offset : ι → ℕ)
    (hp : ∀ i, (modulus i).Prime) (hinj : Function.Injective modulus) :
    ((solutions n S modulus offset).card : ℝ) ≤ (n:ℝ)/(∏ i ∈ S, (modulus i:ℝ))+1 := by
  classical
  have hc : S.toList.Pairwise (fun i j ↦ Nat.Coprime (modulus i) (modulus j)) :=
    S.nodup_toList.imp (fun {i j} hij ↦ (Nat.coprime_primes (hp i) (hp j)).2 (fun h ↦ hij (hinj h)))
  have h := card_Ico_satisfies_cast_le_div_add_one
    (fun i ↦ additiveStartResidue (modulus i) (offset i)) modulus S.toList hc
    (fun i _ ↦ (hp i).pos) 1 (n+1) (by omega)
  have hs : {x ∈ Ico 1 (n+1) | ∀ i ∈ S.toList, x ≡ additiveStartResidue (modulus i) (offset i) [MOD modulus i]} =
      solutions n S modulus offset := by
    ext x
    simp only [solutions, mem_filter, mem_Ico, mem_Icc, mem_toList]
    rw [Nat.lt_succ_iff]
    apply and_congr_right
    intro _
    exact forall_congr' (fun i ↦ imp_congr_right (fun _ ↦ modEq_additiveStartResidue_iff_dvd_add _ _ _ (hp i).pos))
  rw [hs,prod_map_toList] at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  simpa using hr

/-- Under r<=2n, a nonempty block costs at most 3/r; an empty block costs exactly one.
Charging one factor three per prime gives a uniform statement for both cases.-/
theorem solutions_count_le (n : ℕ) (S : Finset ι) (modulus offset : ι → ℕ)
    (hp : ∀ i, (modulus i).Prime) (hinj : Function.Injective modulus)
    (hr : (∏ i ∈ S, modulus i) ≤ 2*n) :
    ((solutions n S modulus offset).card : ℝ) ≤
      (n:ℝ) * (3:ℝ)^S.card / (∏ i ∈ S, (modulus i:ℝ)) := by
  classical
  by_cases hs : S = ∅
  · subst S
    simp [solutions]
  have h := solutions_count n S modulus offset hp hinj
  have hpos : 0 < ∏ i ∈ S, (modulus i:ℝ) := prod_pos (fun i _ ↦ by exact_mod_cast (hp i).pos)
  have hr' : (∏ i ∈ S, (modulus i:ℝ)) ≤ 2*(n:ℝ) := by exact_mod_cast hr
  have hc : 3 ≤ (3:ℝ)^S.card := by
    have : 1 ≤ S.card := (card_pos.mpr (nonempty_iff_ne_empty.mpr hs))
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤3) this)
  apply h.trans
  apply (le_div_iff₀ hpos).mpr
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)]

variable [Fintype ι]

def assignedGrid (n h Q : ℕ) (modulus : ι → ℕ) (a : ι → Fin h × Fin (Q+1)) : Finset (Fin h → ℕ) :=
  Fintype.piFinset (fun b ↦ solutions n (univ.filter (fun i ↦ (a i).1 = b)) modulus (fun i ↦ (a i).2.val))

/-- Every prime is hosted at some vertex of one of h independent target blocks.-/
def hostedGrid (n h Q : ℕ) (modulus : ι → ℕ) : Finset (Fin h → ℕ) :=
  (Fintype.piFinset (fun _ : Fin h ↦ Icc 1 n)).filter
    (fun J ↦ ∀ i, ∃ b : Fin h, ∃ a : Fin (Q+1), modulus i ∣ J b + a.val)

/-- The union over all block-and-offset assignments covers the hosting event.-/
theorem hosted_subset (n h Q : ℕ) (modulus : ι → ℕ) :
    hostedGrid n h Q modulus ⊆ (univ : Finset (ι → Fin h × Fin (Q+1))).biUnion
      (assignedGrid n h Q modulus) := by
  classical
  intro J hJ
  obtain ⟨hg,hh⟩ := mem_filter.mp hJ
  choose b a ha using hh
  refine mem_biUnion.mpr ⟨(fun i ↦ (b i,a i)),mem_univ _,?_⟩
  apply Fintype.mem_piFinset.mpr
  intro t
  change J t ∈ solutions n (univ.filter (fun i ↦ b i = t)) modulus (fun i ↦ (a i).val)
  apply (mem_solutions n _ modulus _ (J t)).mpr
  refine ⟨Fintype.mem_piFinset.mp hg t,?_⟩
  intro i hi
  have he : b i = t := (mem_filter.mp hi).2
  simpa only [← he] using ha i

end
end PaperC.Prel8.RoughKernelCRT
