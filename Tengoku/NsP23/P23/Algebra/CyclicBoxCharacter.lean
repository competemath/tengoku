import Tengoku.Seed.Analysis.SpecialFunctions.Complex.CircleAddChar
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Algebra
noncomputable section
open scoped BigOperators
variable {q : ℕ} [NeZero q]

abbrev cyclicCharacter : AddChar (ZMod q) ℂ := ZMod.stdAddChar

theorem nonzero_two_torsion_eq_half (h : ZMod q) (hne : h ≠ 0)
    (h2 : h + h = 0) : 2 ∣ q ∧ h = ((q / 2 : ℕ) : ZMod q) := by
  have hv : 0 < h.val := by
    by_contra hn
    have hz : h.val = 0 := by omega
    apply hne
    simpa [hz] using (ZMod.natCast_zmod_val h).symm
  have hlt := ZMod.val_lt h
  have hc : ((2 * h.val : ℕ) : ZMod q) = 0 := by
    simpa [Nat.cast_mul, ZMod.natCast_zmod_val, two_mul] using h2
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hc
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hk1 : k = 1 := by nlinarith
  have he : q = 2 * h.val := by simpa [hk1] using hk.symm
  constructor
  · exact ⟨h.val, he⟩
  · have hh : q / 2 = h.val := by omega
    rw [hh, ZMod.natCast_zmod_val]

theorem cyclicCharacter_two_torsion (h : ZMod q) (hne : h≠0) (h2 : h+h=0) :
    cyclicCharacter h = -1 := by
  have he : cyclicCharacter h * cyclicCharacter h = 1 := by
    rw [←AddChar.map_add_eq_mul,h2,AddChar.map_zero_eq_one]
  have hn : cyclicCharacter h ≠ 1 := by
    intro hh
    apply hne
    apply ZMod.injective_stdAddChar
    simpa using hh
  have hh : (cyclicCharacter h - 1) * (cyclicCharacter h + 1)=0 := by
    calc _ = cyclicCharacter h * cyclicCharacter h - 1 := by ring
         _ = 0 := by rw [he]; ring
  rcases mul_eq_zero.mp hh with hh | hh
  · exact False.elim (hn (sub_eq_zero.mp hh))
  · exact eq_neg_of_add_eq_zero_left hh

def cyclicGeometricSum (n : ℕ) (w : ZMod q) : ℂ :=
  ∑ j ∈ Finset.range n, cyclicCharacter (j • w)

theorem geometric_sum_zero_nsmul (n : ℕ) (w : ZMod q)
    (hz : cyclicGeometricSum n w=0) : n • w=0 := by
  have hs : ∑ j ∈ Finset.range n, cyclicCharacter w ^ j=0 := by
    simpa only [cyclicGeometricSum,AddChar.map_nsmul_eq_pow] using hz
  have he := geom_sum_mul (cyclicCharacter w) n
  rw [hs,zero_mul] at he
  have hp : cyclicCharacter w ^ n=1 := by linear_combination -he
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_nsmul_eq_pow,AddChar.map_zero_eq_one] using hp

theorem cyclicGeometricSum_zero (n : ℕ) :
    cyclicGeometricSum (q:=q) n 0=(n:ℂ) := by simp [cyclicGeometricSum]

theorem cyclicCharacter_translation_sum_zero (S : Finset (ZMod q)) (h : ZMod q)
    (hne : h≠0) (h2 : h+h=0) (hS : S.image (fun x=>x+h)=S) :
    ∑ x∈S, cyclicCharacter x=0 := by
  classical
  have he : (∑ x∈S,cyclicCharacter x) = (∑ x∈S,cyclicCharacter x)*cyclicCharacter h := by
    calc
      _ = ∑ x∈S.image (fun x=>x+h),cyclicCharacter x := by rw [hS]
      _ = ∑ x∈S,cyclicCharacter (x+h) := Finset.sum_image (by
        intro x _ y _ hh; exact add_right_cancel hh)
      _ = _ := by simp_rw [AddChar.map_add_eq_mul]; rw [Finset.sum_mul]
  rw [cyclicCharacter_two_torsion h hne h2] at he
  linear_combination (1/2:ℂ)*he

def cyclicBoxSum (A B C : ℕ) (X Y Z : ZMod q) : ℂ :=
  ∑ x∈Finset.range A, ∑ y∈Finset.range B, ∑ z∈Finset.range C,
    cyclicCharacter (x • X+y • Y+z • Z)

theorem cyclicCharacter_box_product (A B C : ℕ) (X Y Z : ZMod q) :
    cyclicBoxSum A B C X Y Z=
      cyclicGeometricSum A X*cyclicGeometricSum B Y*cyclicGeometricSum C Z := by
  unfold cyclicBoxSum cyclicGeometricSum
  simp_rw [AddChar.map_add_eq_mul]
  symm
  rw [Finset.sum_mul_sum (Finset.range A) (Finset.range B)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]

end
end P23.Algebra
