import Tengoku.Seed.Algebra.Field.Subfield.Basic
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms closure_eq_span` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_coefficients` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixed_iff_mem_base` (it only prints; the queue checks the axioms of every declaration). -/

/-! A square root reversed by an actual field automorphism has a two-term
adjoin normal form. Its fixed elements in that adjoin are precisely the base. -/

noncomputable section
namespace AlbertLean.Generic.SignRootAdjoin

variable {K : Type*} [Field K]
variable (H : Subfield K) (s : K ≃+* K) (hfix : ∀ z ∈ H, s z = z)
variable (t : K) (hsq : t ^ 2 ∈ H) (hneg : s t = -t)

include hfix in
private theorem map_coe (a : H) : s (a : K) = a := hfix _ a.property

def span : Subfield K where
  carrier := {z | ∃ a b : H, z = (a : K) + (b : K) * t}
  zero_mem' := ⟨0,0,by simp⟩
  one_mem' := ⟨1,0,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    exact ⟨a+c,b+d,by push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨a,b,rfl⟩
    exact ⟨-a,-b,by push_cast; ring⟩
  mul_mem' := by
    rintro x y ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    refine ⟨a*c+b*d*⟨t^2,hsq⟩,a*d+b*c,?_⟩
    push_cast
    ring
  inv_mem' := by
    rintro x ⟨a,b,rfl⟩
    let n : H := a^2 - b^2 * ⟨t^2,hsq⟩
    by_cases hx : (a : K) + (b : K) * t = 0
    · exact ⟨0,0,by simp [hx]⟩
    · have hn : (n : K) ≠ 0 := by
        have hs : (a : K) - (b : K) * t ≠ 0 := by
          have hh := (map_ne_zero s).mpr hx
          simpa only [map_add, map_mul, map_coe H s hfix, hneg, mul_neg,
            ← sub_eq_add_neg] using hh
        have hp : ((a : K) + (b : K) * t) * ((a : K) - (b : K) * t) = (n : K) := by
          dsimp [n]
          push_cast
          ring
        rw [← hp]
        exact mul_ne_zero hx hs
      refine ⟨a/n,-b/n,?_⟩
      have hp : ((a : K) + (b : K) * t) * ((a : K) - (b : K) * t) = (n : K) := by
        dsimp [n]
        push_cast
        ring
      have hi : ((a : K) + (b : K) * t)⁻¹ =
          ((a : K) - (b : K) * t) / (n : K) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_div_assoc, hp, div_self hn]
      rw [hi]
      push_cast
      ring

theorem closure_eq_span :
    Subfield.closure ((H : Set K) ∪ {t}) = span H s hfix t hsq hneg := by
  apply le_antisymm
  · apply Subfield.closure_le.2
    rintro z (hz | rfl)
    · exact ⟨⟨z,hz⟩,0,by simp⟩
    · exact ⟨0,1,by simp⟩
  · rintro z ⟨a,b,rfl⟩
    apply Subfield.add_mem
    · exact Subfield.subset_closure (Or.inl a.property)
    · exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inl b.property))
        (Subfield.subset_closure (Or.inr rfl))

include s hfix hsq hneg in
theorem exists_coefficients {z : K} (hz : z ∈ Subfield.closure ((H : Set K) ∪ {t})) :
    ∃ a b : H, z = (a : K) + (b : K) * t := by
  rw [closure_eq_span H s hfix t hsq hneg] at hz
  exact hz

include hfix hsq hneg in
theorem fixed_iff_mem_base [CharZero K] (ht : t ≠ 0) {z : K}
    (hz : z ∈ Subfield.closure ((H : Set K) ∪ {t})) : s z = z ↔ z ∈ H := by
  constructor
  · intro hsz
    obtain ⟨a,b,he⟩ := exists_coefficients H s hfix t hsq hneg hz
    have hs := congrArg s he
    simp only [map_add, map_mul, map_coe H s hfix, hneg, hsz] at hs
    have hb : (b : K) = 0 := by
      have hh : (2 : K) * ((b : K) * t) = 0 := by linear_combination hs - he
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))).resolve_right ht
    rw [he,hb,zero_mul,add_zero]
    exact a.property
  · exact hfix z

end AlbertLean.Generic.SignRootAdjoin
