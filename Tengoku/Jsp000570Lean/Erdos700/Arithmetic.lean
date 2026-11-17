import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact polynomial identities and the three exclusions involving the base P.
These are components of the proposed four-prime criterion, not a formalization
of the entire criterion. In particular, the hypotheses about normalized digits
still have to be connected to the Lucas bounds in the main proof.
-/

namespace Erdos700.FourPrime.Arithmetic

/--
@isnad1 id=eq.0h5v.s8.ed5bf72300b0 from=translated src=- shape=4bdf1263 vocab=fb2191f5
-/
theorem change_base (q d u v h : ℤ) :
    (q-d) * (u*(q-d)^2 + v*(q-d) + (h*q-u*d^2+v*d)) =
    q * (u*q^2 + (v-3*u*d+h)*q + (2*u*d^2-d*v-d*h)) := by ring

/--
@isnad1 id=eq.0h4v.s7.35b669e21342 from=translated src=- shape=adfbe8df vocab=85af4b90
-/
theorem expansion_p (x a b c : ℤ) :
    (x+a)*(x+b)*(x+c) =
    x^3 + (a+b+c)*x^2 + (a*b+a*c+b*c)*x + a*b*c := by ring

/--
@isnad1 id=eq.0h4v.s8.750585c91629 from=translated src=- shape=0bf7ffc5 vocab=fb2191f5
-/
theorem expansion_a (x a b c : ℤ) :
    (x-a)*(x+b-a)*(x+c-a) =
    x^3 + (b+c-3*a)*x^2 + (b*c-2*a*(b+c)+3*a^2-1)*x +
      (x-a*(b-a)*(c-a)) := by ring

/--
@isnad1 id=eq.0h4v.s8.0592fd11602c from=translated src=- shape=e6f1d1e2 vocab=fb2191f5
-/
theorem expansion_b (x a b c : ℤ) :
    (x-b)*(x+a-b)*(x+c-b) =
    x^3 + (a+c-3*b-1)*x^2 + (x-((2*b-a)*c+2*a*b-3*b^2))*x +
      b*(b-a)*(c-b) := by ring

/--
@isnad1 id=eq.0h4v.s8.8541e0d42350 from=translated src=- shape=e1b3ae5f vocab=fb2191f5
-/
theorem expansion_c (x a b c : ℤ) :
    (x-c)*(x+a-c)*(x+b-c) =
    (x-(3*c-a-b))*x^2 + (3*c^2-2*c*(a+b)+a*b-1)*x +
      (x-c*(c-a)*(c-b)) := by ring

/--
@isnad1 id=lt.3h5v.s7.d4de8d6402bd from=translated src=- shape=fc3eeec2 vocab=e94596d0
-/
theorem pairAP_bound (a b c u v : ℤ) (ha : 0 < a)
    (hu : u ≤ b+c-3*a) (hv : v ≤ b*c-2*a*(b+c)+3*a^2-1) :
    a^2*u+a*v < a*(b-a)*(c-a)-a := by
  have h₁ := mul_le_mul_of_nonneg_left hu (sq_nonneg a)
  have h₂ := mul_le_mul_of_nonneg_left hv ha.le
  have h₃ : 0 < a^3 := pow_pos ha 3
  nlinarith only [h₁, h₂, h₃]

/--
@isnad1 id=false.5h7v.s8.d9074dcc321c from=translated src=- shape=1eb25f5e vocab=e94596d0
-/
theorem pairAP_residue_impossible (p a b c u v w : ℤ) (ha : 0 < a)
    (hu : u ≤ b+c-3*a) (hv : v ≤ b*c-2*a*(b+c)+3*a^2-1)
    (hw : w = p-(a^2*u+a*v)) (hwmax : w ≤ p+a-a*(b-a)*(c-a)) : False := by
  have h := pairAP_bound a b c u v ha hu hv
  linarith

/-- Complete residue exclusion for the bases `(P+a,P)`: the only source
digit vector whose quotient is divisible by P is the zero vector.
@isnad1 id=and.8h7v.s8.0deab07eb9ee from=translated src=- shape=d2ff9d89 vocab=239ca0fb
-/
theorem pairAP_zero_digits (p a b c u v w : ℤ) (ha : 0 < a)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hu : u ≤ b+c-3*a) (hv : v ≤ b*c-2*a*(b+c)+3*a^2-1)
    (hw : w ≤ p+a-a*(b-a)*(c-a))
    (hdiv : p ∣ u*(p+a)^2+v*(p+a)+w) : u = 0 ∧ v = 0 ∧ w = 0 := by
  have hbnd := pairAP_bound a b c u v ha hu hv
  have hau := mul_nonneg (sq_nonneg a) hu0
  have hav := mul_nonneg ha.le hv0
  have hsmall : a^2*u+a*v+w < p := by linarith
  have hdiv' : p ∣ a^2*u+a*v+w := by
    have hid : u*(p+a)^2+v*(p+a)+w - p*(u*(p+2*a)+v) = a^2*u+a*v+w := by ring
    rw [← hid]
    exact dvd_sub hdiv (dvd_mul_right p (u*(p+2*a)+v))
  have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (by linarith : 0 ≤ a^2*u+a*v+w)
    hsmall hdiv'
  have hzu : a^2*u = 0 := le_antisymm (by linarith) hau
  have hzv : a*v = 0 := le_antisymm (by linarith) hav
  exact ⟨(mul_eq_zero.mp hzu).resolve_left (ne_of_gt (sq_pos_of_pos ha)),
    (mul_eq_zero.mp hzv).resolve_left ha.ne', by linarith⟩

/--
@isnad1 id=false.4h5v.s7.8305994108eb from=translated src=- shape=3ec9c45f vocab=e94596d0
-/
theorem pairPB_impossible (a b c u t : ℤ) (hb : 0 < b)
    (hu : u ≤ a+c-3*b)
    (hlow : b*u-t ≤ (b-a)*(c-b))
    (hmiddle : (2*b-a)*c+2*a*b-3*b^2 ≤ 2*b*u-t) : False := by
  have h := mul_le_mul_of_nonneg_left hu hb.le
  have hs := sq_pos_of_pos hb
  nlinarith only [h, hlow, hmiddle, hs]

/--
@isnad1 id=eq.0h3v.s6.6909dbba5bcd from=translated src=- shape=a53b29a7 vocab=64706f8b
-/
theorem pairPC_gap (a b c : ℤ) :
    c*(c-a)*(c-b)-a*b*c = c^2*(c-a-b) := by ring

/--
@isnad1 id=false.5h6v.s7.89872d56ea98 from=translated src=- shape=f9ee84e9 vocab=3b732f86
-/
theorem pairPC_negative_low_impossible (a b c q u t : ℤ)
    (hc : 0 < c) (hsep : a+b < c) (hu : 0 ≤ u) (ht : t ≤ a*b)
    (hlow : q+c*(c*u-t) ≤ q-c*(c-a)*(c-b)) : False := by
  have hcu : 0 ≤ c*u := mul_nonneg hc.le hu
  have ht' := mul_le_mul_of_nonneg_left ht hc.le
  have hcu' : 0 ≤ c*(c*u) := mul_nonneg hc.le hcu
  have hgap : 0 < c^2*(c-a-b) := mul_pos (sq_pos_of_pos hc) (by linarith)
  nlinarith only [ht', hcu', hgap, hlow]

/--
@isnad1 id=lt.3h3v.s6.4f3df1c66d68 from=translated src=- shape=40679f5d vocab=b4d30996
-/
theorem pairPC_middle_negative (c u t : ℤ) (hc : 0 < c) (hu : 0 < u)
    (hK : 0 ≤ c*(c*u-t)) : t-2*c*u < 0 := by
  have hin := (mul_nonneg_iff_of_pos_left hc).mp hK
  have hp := mul_pos hc hu
  nlinarith

/--
@isnad1 id=eq.3h2v.s6.a56e591eb5bf from=translated src=- shape=467445c7 vocab=b4d30996
-/
theorem pairPC_zero_case (c t : ℤ) (hc : 0 < c) (ht : 0 ≤ t)
    (hK : 0 ≤ c*(c*0-t)) : t = 0 := by
  have hin := (mul_nonneg_iff_of_pos_left hc).mp hK
  nlinarith

end Erdos700.FourPrime.Arithmetic
