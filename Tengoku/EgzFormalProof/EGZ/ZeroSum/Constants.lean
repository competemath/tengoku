import Tengoku.EgzFormalProof.EGZ.ZeroSum.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace EGZ

/-- The Erdős--Ginzburg--Ziv constant `𝔰(𝔽_p^d)`: the least exact sequence
length with the EGZ property.  `exists_egzProperty` supplies the witness used by
`Nat.find`, so the definition does not depend on the default behavior of an
infimum of an empty set.-/
noncomputable def egzConstant (p d : ℕ) : ℕ :=
  @Nat.find (EGZProperty p d) (Classical.decPred _) (exists_egzProperty p d)

/-- The least EGZ length itself has the EGZ property.
@isnad1 id=egzprope.0h2v.s3.e9d57d0b3770 from=translated src=- shape=c08a1264 vocab=81b7ec2e
-/
theorem egzConstant_spec (p d : ℕ) : EGZProperty p d (egzConstant p d) := by
  classical
  exact Nat.find_spec (exists_egzProperty p d)

/-- Minimality of the EGZ constant.
@isnad1 id=le.1h3v.s4.cf0531b1113f from=translated src=- shape=184d58ed vocab=19a797ff
-/
theorem egzConstant_min {p d n : ℕ} (h : EGZProperty p d n) :
    egzConstant p d ≤ n := by
  classical
  exact Nat.find_min' (exists_egzProperty p d) h

/-- The crude pigeonhole construction gives an explicit finite upper bound.
@isnad1 id=le.0h2v.s5.b65aa0efcc98 from=translated src=- shape=47d2e7ca vocab=615b0342
-/
theorem egzConstant_le_pigeonhole_bound (p d : ℕ) :
    egzConstant p d ≤ (p - 1) * p ^ d + 1 :=
  egzConstant_min (EGZProperty.pigeonhole_bound p d)

/-- Every exact length at least the EGZ constant has the EGZ property.
@isnad1 id=egzprope.1h3v.s4.92504cb2ee14 from=translated src=- shape=89bb98ea vocab=19a797ff
-/
theorem egzProperty_of_egzConstant_le {p d n : ℕ} (h : egzConstant p d ≤ n) :
    EGZProperty p d n :=
  EGZProperty.mono h (egzConstant_spec p d)

/-- A failed exact length lies strictly below the EGZ constant.
@isnad1 id=lt.1h3v.s4.6bd37f1a6c2d from=translated src=- shape=0ee3a867 vocab=1e896461
-/
theorem lt_egzConstant_of_not_egzProperty {p d n : ℕ}
    (h : ¬ EGZProperty p d n) : n < egzConstant p d := by
  exact Nat.lt_of_not_ge fun hn ↦ h (egzProperty_of_egzConstant_le hn)

/-- The extremal `p`-hollow number `𝔴(𝔽_p^d)`.

The paper only uses this at primes.  We search through the natural ambient
bound `p ^ d`; for prime `p`, injectivity of hollow families proves that this
cutoff loses nothing.  This bounded definition is total even at the degenerate
moduli `0` and `1`, where hollow lengths need not be bounded.-/
noncomputable def hollowConstant (p d : ℕ) : ℕ :=
  @Nat.findGreatest (AdmitsPHollowLength p d) (Classical.decPred _) (p ^ d)

/-- The bounded-search definition is always at most the ambient cutoff.
@isnad1 id=le.0h2v.s4.55b492147bdc from=translated src=- shape=895a5e7f vocab=fbca081b
-/
theorem hollowConstant_le_pow (p d : ℕ) : hollowConstant p d ≤ p ^ d := by
  classical
  exact Nat.findGreatest_le _

/-- At a prime, the extremal hollow length is attained.
@isnad1 id=admitsph.1h2v.s3.b72012972a51 from=translated src=- shape=5126d034 vocab=97d7a922
-/
theorem hollowConstant_spec {p d : ℕ} (hp : Nat.Prime p) :
    AdmitsPHollowLength p d (hollowConstant p d) := by
  classical
  unfold hollowConstant
  exact Nat.findGreatest_spec (P := AdmitsPHollowLength p d) (n := p ^ d)
    (Nat.zero_le _) (admitsPHollowLength_zero hp.pos)

/-- At a prime, every admitted hollow length is at most the hollow constant.
@isnad1 id=le.2h3v.s4.2a8f16af3d9a from=translated src=- shape=691f13af vocab=abec1759
-/
theorem hollowConstant_max {p d s : ℕ} (hp : Nat.Prime p)
    (h : AdmitsPHollowLength p d s) : s ≤ hollowConstant p d := by
  classical
  unfold hollowConstant
  exact Nat.le_findGreatest (P := AdmitsPHollowLength p d) (h.le_pow hp) h

/-- Any positive-modulus hollow family gives the elementary EGZ lower bound.
@isnad1 id=le.2h3v.s5.6d768d0e4761 from=translated src=- shape=8823bd90 vocab=145a69db
-/
theorem hollowLength_mul_add_one_le_egzConstant {p d s : ℕ} (hp : 0 < p)
    (h : AdmitsPHollowLength p d s) :
    s * (p - 1) + 1 ≤ egzConstant p d := by
  have hlt : s * (p - 1) < egzConstant p d :=
    lt_egzConstant_of_not_egzProperty
      (not_egzProperty_of_admitsPHollowLength hp h)
  omega

/-- The standard lower comparison between the two constants.
@isnad1 id=le.1h2v.s5.a7a4c69e6852 from=translated src=- shape=5ca340a4 vocab=e23dadaa
-/
theorem hollowConstant_mul_add_one_le_egzConstant {p d : ℕ} (hp : Nat.Prime p) :
    hollowConstant p d * (p - 1) + 1 ≤ egzConstant p d :=
  hollowLength_mul_add_one_le_egzConstant hp.pos (hollowConstant_spec hp)

end EGZ
