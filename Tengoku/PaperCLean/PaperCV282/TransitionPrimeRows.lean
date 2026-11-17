import Tengoku.PaperCLean.PaperC.Arithmetic.ParityVector
import Tengoku.Seed.Algebra.Order.Floor.Div
import Tengoku.Seed.NumberTheory.PrimeCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Actual identity rows in the microscopic transition range

For every prime p above Y, choose the first multiple of p at least a.
If 1 <= a <= B and B <= Y^2, its cofactor is at most Y. This gives
literal Kronecker-delta prime-parity coordinates, not an assumed rank.
-/
namespace PaperC.V282.TransitionPrimeRows

open scoped BigOperators

noncomputable section

def transitionRow (a p : ℕ) : ℕ := p*(a ⌈/⌉ p)

/--
@isnad1 id=le.1h2v.s4.dc4a3be46d31 from=translated src=- shape=de9c066d vocab=c8888814
-/
theorem transitionRow_lower {a p : ℕ} (hp : 0<p) : a≤transitionRow a p := by
  exact (ceilDiv_le_iff_le_mul hp).mp (le_refl (a ⌈/⌉ p))

/--
@isnad1 id=lt.1h2v.s4.b891419fc565 from=translated src=- shape=f6542145 vocab=03fd8d72
-/
theorem transitionRow_lt {a p : ℕ} (hp : 0<p) : transitionRow a p<a+p := by
  unfold transitionRow
  rw [Nat.ceilDiv_eq_add_pred_div]
  have h := Nat.mul_div_le (a+p-1) p
  omega

/--
@isnad1 id=eq.2h2v.s4.7820f769b4d6 from=translated src=- shape=55c94330 vocab=c8888814
-/
theorem transitionRow_eq_prime {a p : ℕ} (ha : 0<a) (hap : a≤p) : transitionRow a p=p := by
  have hp : 0<p := ha.trans_le hap
  have hc : a ⌈/⌉ p≤1 := (ceilDiv_le_iff_le_mul hp).mpr (by simpa using hap)
  have hl := transitionRow_lower (a := a) hp
  have hcpos : 0<a ⌈/⌉ p := by
    by_contra hn
    have hz : a ⌈/⌉ p=0 := by omega
    simp [transitionRow,hz] at hl
    omega
  have hc1 : a ⌈/⌉ p=1 := by omega
  simp [transitionRow,hc1]

/-- Both the small-prime multiples and the large-prime vertices lie in the actual window.
@isnad1 id=and.4h3v.s6.f2ec3c80d4c0 from=translated src=- shape=664bd6fd vocab=48eb4e6b
-/
theorem transitionRow_mem_interval {a B p : ℕ} (ha : 0<a) (haB : a≤B)
    (hp : 0<p) (hpTop : p≤a+B-1) :
    a≤transitionRow a p ∧ transitionRow a p≤a+B-1 := by
  refine ⟨transitionRow_lower hp,?_⟩
  by_cases hpB : p≤B
  · have h := transitionRow_lt (a := a) hp
    omega
  · rw [transitionRow_eq_prime ha (by omega)]
    exact hpTop

/-- The cofactor contains no prime species above Y.
@isnad1 id=le.4h4v.s6.79f8146c6521 from=translated src=- shape=8fb02116 vocab=e9ff314f
-/
theorem transition_cofactor_le {a B Y p : ℕ} (haB : a≤B) (hBY : B≤Y^2)
    (hp : 0<p) (hYp : Y<p) : a ⌈/⌉ p≤Y := by
  apply (ceilDiv_le_iff_le_mul hp).mpr
  calc
    a ≤ B := haB
    _ ≤ Y*Y := by simpa [pow_two] using hBY
    _ ≤ p*Y := Nat.mul_le_mul_right Y hYp.le

/--
@isnad1 id=lt.2h2v.s5.9a64e5d0f0bb from=translated src=- shape=cbdac857 vocab=986108e6
-/
theorem transition_cofactor_pos {a p : ℕ} (ha : 0<a) (hp : 0<p) : 0<a ⌈/⌉ p := by
  have h := transitionRow_lower (a := a) hp
  unfold transitionRow at h
  by_contra hn
  have hz : a ⌈/⌉ p=0 := by omega
  simp [hz] at h
  omega

/-- The selected valuation rows have an exact identity minor on all primes above Y.
@isnad1 id=eq.7h5v.s7.04d8d610c17c from=translated src=- shape=15f57535 vocab=6197c16d
-/
theorem transitionRow_parity {a B Y p q : ℕ} (ha : 0<a) (haB : a≤B)
    (hBY : B≤Y^2) (hp : p.Prime) (hq : q.Prime) (hYp : Y<p) (hYq : Y<q) :
    parityVec (transitionRow a p) q = if q=p then 1 else 0 := by
  have hc := transition_cofactor_le haB hBY hp.pos hYp
  have hcpos := transition_cofactor_pos ha hp.pos
  have hnot : ¬q∣a ⌈/⌉ p := by
    intro hdiv
    have hle := Nat.le_of_dvd hcpos hdiv
    omega
  rw [transitionRow,parityVec_mul hp.ne_zero (by omega : a ⌈/⌉ p≠0)]
  simp only [parityVec,Finsupp.add_apply,Finsupp.mapRange_apply,Nat.factorization_eq_zero_of_not_dvd hnot,
    Nat.cast_zero,add_zero,hp.factorization]
  by_cases hqp : q=p
  · subst q; simp
  · simp [Finsupp.single_eq_of_ne hqp,hqp]

/-- The selected rows cannot collide, since their parity coordinates distinguish them.
@isnad1 id=injon.3h3v.s5.25757099e3c9 from=translated src=- shape=2cc8732b vocab=7196541e
-/
theorem transitionRow_injective_on_primes {a B Y : ℕ} (ha : 0<a) (haB : a≤B)
    (hBY : B≤Y^2) :
    Set.InjOn (transitionRow a) {p : ℕ | p.Prime ∧ Y<p} := by
  intro p hp q hq heq
  by_contra hpq
  have hpp := transitionRow_parity ha haB hBY hp.1 hp.1 hp.2 hp.2
  have hqp := transitionRow_parity ha haB hBY hq.1 hp.1 hq.2 hp.2
  rw [heq] at hpp
  rw [ite_eq_right hpq] at hqp
  exact (one_ne_zero : (1 : F₂)≠0) (by simpa using hpp.symm.trans hqp)

end
end PaperC.V282.TransitionPrimeRows
