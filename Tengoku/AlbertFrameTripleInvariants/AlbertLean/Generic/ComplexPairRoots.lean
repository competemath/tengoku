import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ComplexDephasedPair
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms roots_eq_or_eq_dual` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms dephased_eq_of_overlap_of_d_eq` (it only prints; the queue checks the axioms of every declaration). -/

/-! Source-only extraction of the scalar root and fixed-root uniqueness
arguments. Does not import the old nine rational-overlap proof. -/
noncomputable section
namespace AlbertLean.Generic.ComplexPairRoots
open C1Coordinates ComplexPairPolynomial ComplexDephasedPair
variable {K : Type*} [Field K]

def A2 (p q r : K) : K := (1-p-q)*(1-p-r)
def A0 (p q r s : K) : K := p*(p+q+r+s-1)
def dualRoot (p q r s d : K) : K := A0 p q r s / (A2 p q r * d)
def td (a b c d : K) : K := (a-1)*(a*d-b*c)/((b-a)*(c-a))

theorem roots_eq_or_eq_dual (p q r s x y : K)
    (hA2 : A2 p q r ≠ 0) (hx : x ≠ 0)
    (hQx : pairQuadratic p q r s x = 0)
    (hQy : pairQuadratic p q r s y = 0) :
    y = x ∨ y = dualRoot p q r s x := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  · right
    have hfactor : (y-x) * (A2 p q r * (y+x) +
        (p*(1-p-q-r)+(1-p)*(p+q+r+s-1)-q*r)) = 0 := by
      simp only [pairQuadratic, A2] at hQx hQy ⊢
      linear_combination hQy - hQx
    have hlinear : A2 p q r * (y+x) +
        (p*(1-p-q-r)+(1-p)*(p+q+r+s-1)-q*r) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hyx)
    have hproduct : A2 p q r * x * y = A0 p q r s := by
      simp only [pairQuadratic, A2, A0] at hQx hlinear ⊢
      linear_combination x * hlinear - hQx
    unfold dualRoot
    apply (eq_div_iff (mul_ne_zero hA2 hx)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hproduct

theorem dephased_eq_of_overlap_of_d_eq
    (a b c d a' b' c' d' : K)
    (hΔ : delta a b c d ≠ 0) (hΔ' : delta a' b' c' d' ≠ 0)
    (hnu : nu (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) (overlap a b c d 1 1) d ≠ 0)
    (hnu' : nu (overlap a' b' c' d' 0 0) (overlap a' b' c' d' 0 1)
      (overlap a' b' c' d' 1 0) (overlap a' b' c' d' 1 1) d' ≠ 0)
    (hover : ∀ i j, overlap a' b' c' d' i j = overlap a b c d i j)
    (hd : d' = d) : dephased a' b' c' d' = dephased a b c d := by
  obtain ⟨ha, hb, hc⟩ := reconstruct_entries a b c d hΔ hnu
  obtain ⟨ha', hb', hc'⟩ := reconstruct_entries a' b' c' d' hΔ' hnu'
  simp only [hover] at ha' hb' hc'
  simp only [hd] at ha' hb' hc'
  have hea : a' = a := ha'.trans ha.symm
  have heb : b' = b := hb'.trans hb.symm
  have hec : c' = c := hc'.trans hc.symm
  simp only [hea, heb, hec, hd]

end AlbertLean.Generic.ComplexPairRoots
