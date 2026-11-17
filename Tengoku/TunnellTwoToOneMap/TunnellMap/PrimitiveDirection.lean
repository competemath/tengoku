import Tengoku.TunnellTwoToOneMap.TunnellMap.AffineLattice
import Tengoku.TunnellTwoToOneMap.TunnellMap.Antipodal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primitive integer directions

An integer triple is encoded as the polynomial `x + y X + z X²`.  Mathlib's
standard polynomial content and primitive part then give the gcd-normalized
integer generator of its rational line.  The remaining sign normalization is
the paper's convention that the first nonzero coordinate is positive.
-/

namespace TunnellMap

open Polynomial

noncomputable def triplePolynomial (v : Triple) : ℤ[X] :=
  C v.x + C v.y * X + C v.z * X ^ 2

def polynomialTriple (f : ℤ[X]) : Triple :=
  ⟨f.coeff 0, f.coeff 1, f.coeff 2⟩

/--
@isnad1 id=eq.0h1v.s4.4f7c0fd79389 from=translated src=- shape=22c521f0 vocab=5c53cf69
-/
@[simp] theorem polynomialTriple_neg (f : ℤ[X]) :
    polynomialTriple (-f) = negTriple (polynomialTriple f) := by
  ext <;> simp [polynomialTriple, negTriple]

/--
@isnad1 id=eq.0h1v.s4.a1d7f832aff9 from=translated src=- shape=b5df01d7 vocab=10d37d61
-/
@[simp] theorem triplePolynomial_coeff_zero (v : Triple) :
    (triplePolynomial v).coeff 0 = v.x := by
  simp [triplePolynomial]

/--
@isnad1 id=eq.0h1v.s4.511b5a229e79 from=translated src=- shape=b5df01d7 vocab=6df71bd5
-/
@[simp] theorem triplePolynomial_coeff_one (v : Triple) :
    (triplePolynomial v).coeff 1 = v.y := by
  simp only [triplePolynomial, coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  norm_num

/--
@isnad1 id=eq.0h1v.s4.bbc7cab8bf7a from=translated src=- shape=b5df01d7 vocab=19ffc9a7
-/
@[simp] theorem triplePolynomial_coeff_two (v : Triple) :
    (triplePolynomial v).coeff 2 = v.z := by
  simp only [triplePolynomial, coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  norm_num

/--
@isnad1 id=eq.0h1v.s3.d5ae8e07be8f from=translated src=- shape=47dcad53 vocab=2c1dc763
-/
@[simp] theorem polynomialTriple_triplePolynomial (v : Triple) :
    polynomialTriple (triplePolynomial v) = v := by
  ext <;> simp [polynomialTriple]

/--
@isnad1 id=injectiv.0h0v.s2.7be127554ef5 from=translated src=- shape=4b736592 vocab=2c3a5e3e
-/
theorem triplePolynomial_injective : Function.Injective triplePolynomial := by
  intro v w h
  simpa using congrArg polynomialTriple h

/--
@isnad1 id=eq.0h1v.s4.67a0ad16cc70 from=translated src=- shape=e1ba4b03 vocab=863bdb0a
-/
@[simp] theorem triplePolynomial_negTriple (v : Triple) :
    triplePolynomial (negTriple v) = -triplePolynomial v := by
  simp [triplePolynomial, negTriple]
  ring

/--
@isnad1 id=eq.0h2v.s6.02fe46434d62 from=translated src=- shape=cfd61c6c vocab=5e3ad2ce
-/
@[simp] theorem triplePolynomial_vsmul (a : ℤ) (v : Triple) :
    triplePolynomial (vsmul a v) = C a * triplePolynomial v := by
  simp [triplePolynomial, vsmul]
  ring

/--
@isnad1 id=ne.1h1v.s5.c73e72e27ea8 from=translated src=- shape=a36ad929 vocab=f6fc5b1b
-/
theorem triplePolynomial_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    triplePolynomial v ≠ 0 := by
  intro h
  apply hv
  apply Triple.ext
  · have := congrArg (fun f : ℤ[X] => f.coeff 0) h
    simpa using this
  · have := congrArg (fun f : ℤ[X] => f.coeff 1) h
    simpa using this
  · have := congrArg (fun f : ℤ[X] => f.coeff 2) h
    simpa using this

/--
@isnad1 id=le.0h1v.s3.d06186bd4bf1 from=translated src=- shape=8e1bdd70 vocab=f63aa626
-/
theorem triplePolynomial_natDegree_le_two (v : Triple) :
    (triplePolynomial v).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp only [triplePolynomial, coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  simp [hn0, hn1, hn2]

noncomputable def tripleContent (v : Triple) : ℤ :=
  (triplePolynomial v).content

noncomputable def primitivePartTriple (v : Triple) : Triple :=
  polynomialTriple (triplePolynomial v).primPart

/-- Converting the primitive polynomial back to a triple loses no
coefficients, because the original polynomial has degree at most two.
@isnad1 id=eq.0h1v.s4.e1bec7221212 from=translated src=- shape=267a0781 vocab=a2d19753
-/
theorem triplePolynomial_primitivePartTriple (v : Triple) :
    triplePolynomial (primitivePartTriple v) = (triplePolynomial v).primPart := by
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [primitivePartTriple, polynomialTriple]
  · have hnLarge : 2 < n := Nat.lt_of_not_ge hn
    have hleftDeg : (triplePolynomial (primitivePartTriple v)).natDegree ≤ 2 :=
      triplePolynomial_natDegree_le_two _
    have hrightDeg : (triplePolynomial v).primPart.natDegree ≤ 2 := by
      rw [Polynomial.natDegree_primPart]
      exact triplePolynomial_natDegree_le_two _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hleftDeg hnLarge)]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hrightDeg hnLarge)]

/--
@isnad1 id=eq.0h1v.s5.19d7124a69a1 from=translated src=- shape=b1dfe555 vocab=018e631b
-/
theorem polynomial_content_neg (f : ℤ[X]) : (-f).content = f.content := by
  rw [show -f = C (-1 : ℤ) * f by simp, Polynomial.content_C_mul]
  rw [← Int.abs_eq_normalize]
  norm_num

/--
@isnad1 id=eq.0h1v.s3.7a053a1b2455 from=translated src=- shape=8d4cac31 vocab=31faff23
-/
@[simp] theorem tripleContent_negTriple (v : Triple) :
    tripleContent (negTriple v) = tripleContent v := by
  simp [tripleContent, polynomial_content_neg]

/--
@isnad1 id=eq.1h1v.s6.5f3380adfa01 from=translated src=- shape=00072ec6 vocab=aeb85a44
-/
theorem polynomial_primPart_neg {f : ℤ[X]} (hf : f ≠ 0) :
    (-f).primPart = -f.primPart := by
  have hc : f.content ≠ 0 := by
    intro h
    exact hf (Polynomial.content_eq_zero_iff.mp h)
  have hbase := Polynomial.eq_C_content_mul_primPart f
  have hneg := Polynomial.eq_C_content_mul_primPart (-f)
  rw [polynomial_content_neg] at hneg
  apply mul_left_cancel₀ (show C f.content ≠ (0 : ℤ[X]) by simpa using hc)
  calc
    C f.content * (-f).primPart = -f := hneg.symm
    _ = -(C f.content * f.primPart) := by rw [← hbase]
    _ = C f.content * (-f.primPart) := by simp

/--
@isnad1 id=eq.1h1v.s6.e92788633f99 from=translated src=- shape=916fd95f vocab=c35b18ff
-/
theorem polynomial_primPart_two_mul {f : ℤ[X]} (hf : f ≠ 0) :
    (C (2 : ℤ) * f).primPart = f.primPart := by
  have hc : f.content ≠ 0 := by
    intro h
    exact hf (Polynomial.content_eq_zero_iff.mp h)
  have hcontent : (C (2 : ℤ) * f).content = 2 * f.content := by
    rw [Polynomial.content_C_mul, ← Int.abs_eq_normalize]
    norm_num
  have hbase := Polynomial.eq_C_content_mul_primPart f
  have hscaled := Polynomial.eq_C_content_mul_primPart (C (2 : ℤ) * f)
  rw [hcontent] at hscaled
  apply mul_left_cancel₀ (show C (2 * f.content) ≠ (0 : ℤ[X]) by
    simp [hc])
  calc
    C (2 * f.content) * (C (2 : ℤ) * f).primPart = C (2 : ℤ) * f :=
      hscaled.symm
    _ = C (2 : ℤ) * (C f.content * f.primPart) := by rw [← hbase]
    _ = C (2 * f.content) * f.primPart := by simp [mul_assoc]

/--
@isnad1 id=eq.1h1v.s4.9c3dcbe6bd46 from=translated src=- shape=aecb388d vocab=4f64ba33
-/
@[simp] theorem primitivePartTriple_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple (negTriple v) = negTriple (primitivePartTriple v) := by
  unfold primitivePartTriple
  rw [triplePolynomial_negTriple,
    polynomial_primPart_neg (triplePolynomial_ne_zero hv), polynomialTriple_neg]

/--
@isnad1 id=eq.1h1v.s5.f6fe1e938587 from=translated src=- shape=e397c93d vocab=0ab5bddd
-/
@[simp] theorem primitivePartTriple_two_vsmul {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple (vsmul 2 v) = primitivePartTriple v := by
  unfold primitivePartTriple
  rw [triplePolynomial_vsmul,
    polynomial_primPart_two_mul (triplePolynomial_ne_zero hv)]

/--
@isnad1 id=ne.1h1v.s4.cad793c68f45 from=translated src=- shape=cce858f6 vocab=7fe32c18
-/
theorem tripleContent_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    tripleContent v ≠ 0 := by
  intro hc
  apply triplePolynomial_ne_zero hv
  exact Polynomial.content_eq_zero_iff.mp hc

/--
@isnad1 id=eq.0h1v.s3.7ef4a04c2f03 from=translated src=- shape=f6b6ad72 vocab=358c962e
-/
@[simp] theorem tripleContent_primitivePartTriple (v : Triple) :
    tripleContent (primitivePartTriple v) = 1 := by
  unfold tripleContent
  rw [triplePolynomial_primitivePartTriple]
  exact Polynomial.content_primPart _

/-- The coordinate form of `Polynomial.eq_C_content_mul_primPart`.
@isnad1 id=eq.0h1v.s3.63afe4bc47e9 from=translated src=- shape=fd592461 vocab=8ff0478e
-/
theorem content_mul_primitivePartTriple (v : Triple) :
    v = vsmul (tripleContent v) (primitivePartTriple v) := by
  apply Triple.ext
  · have h := congrArg (fun f : ℤ[X] => f.coeff 0)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h
  · have h := congrArg (fun f : ℤ[X] => f.coeff 1)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h
  · have h := congrArg (fun f : ℤ[X] => f.coeff 2)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h

/--
@isnad1 id=ne.1h1v.s5.cb8b5f1e57f7 from=translated src=- shape=dfb49cbf vocab=d725999a
-/
theorem primitivePartTriple_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple v ≠ ⟨0, 0, 0⟩ := by
  intro hd
  have h := content_mul_primitivePartTriple v
  rw [hd] at h
  apply hv
  simpa [vsmul] using h

def FirstNonzeroPositive (v : Triple) : Prop :=
  0 < v.x ∨ (v.x = 0 ∧ 0 < v.y) ∨ (v.x = 0 ∧ v.y = 0 ∧ 0 < v.z)

instance firstNonzeroPositiveDecidable (v : Triple) : Decidable (FirstNonzeroPositive v) :=
  by
    unfold FirstNonzeroPositive
    infer_instance

/--
@isnad1 id=or.1h1v.s4.f6370d4475cc from=translated src=- shape=fe20eb5e vocab=15f2eec1
-/
theorem firstNonzeroPositive_or_neg {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    FirstNonzeroPositive v ∨ FirstNonzeroPositive (negTriple v) := by
  rcases lt_trichotomy v.x 0 with hx | hx | hx
  · right
    left
    simpa [negTriple]
  · rcases lt_trichotomy v.y 0 with hy | hy | hy
    · right
      right
      left
      simpa [negTriple, hx]
    · have hz : v.z ≠ 0 := by
        intro hz
        apply hv
        ext <;> simp_all
      rcases lt_or_gt_of_ne hz with hz | hz
      · right
        right
        right
        simpa [negTriple, hx, hy]
      · left
        right
        right
        exact ⟨hx, hy, hz⟩
    · left
      right
      left
      exact ⟨hx, hy⟩
  · left
    exact Or.inl hx

/--
@isnad1 id=not.0h1v.s3.f7a91dc894f0 from=translated src=- shape=3d1bfd91 vocab=d0513518
-/
theorem firstNonzeroPositive_not_both (v : Triple) :
    ¬ (FirstNonzeroPositive v ∧ FirstNonzeroPositive (negTriple v)) := by
  rintro ⟨hv, hn⟩
  rcases hv with hx | hy | hz <;> rcases hn with hx' | hy' | hz' <;>
    simp [negTriple] at * <;> omega

def orientDirection (v : Triple) : Triple :=
  if FirstNonzeroPositive v then v else negTriple v

/--
@isnad1 id=eq.0h1v.s3.22ea99a9ae52 from=translated src=- shape=8d4cac31 vocab=e19ae4e2
-/
@[simp] theorem tripleContent_orientDirection (v : Triple) :
    tripleContent (orientDirection v) = tripleContent v := by
  by_cases h : FirstNonzeroPositive v <;> simp [orientDirection, h]

/--
@isnad1 id=firstnon.1h1v.s4.ea9b7d7aee5c from=translated src=- shape=3ef40b71 vocab=61077aa5
-/
theorem orientDirection_firstNonzeroPositive {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    FirstNonzeroPositive (orientDirection v) := by
  by_cases h : FirstNonzeroPositive v
  · simp [orientDirection, h]
  · have hn := (firstNonzeroPositive_or_neg hv).resolve_left h
    simpa [orientDirection, h] using hn

/--
@isnad1 id=eq.1h1v.s4.23e083ebd62c from=translated src=- shape=262b6642 vocab=13d25d98
-/
theorem orientDirection_neg {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    orientDirection (negTriple v) = orientDirection v := by
  have hnb : ¬ (FirstNonzeroPositive v ∧ FirstNonzeroPositive (negTriple v)) :=
    firstNonzeroPositive_not_both v
  rcases firstNonzeroPositive_or_neg hv with h | h
  · have hn : ¬ FirstNonzeroPositive (negTriple v) := fun hn => hnb ⟨h, hn⟩
    simp [orientDirection, h, hn]
  · have hvn : ¬ FirstNonzeroPositive v := fun hvp => hnb ⟨hvp, h⟩
    simp [orientDirection, h, hvn]

noncomputable def primitiveDirection (v : Triple) : Triple :=
  orientDirection (primitivePartTriple v)

noncomputable def directionScale (v : Triple) : ℤ :=
  if FirstNonzeroPositive (primitivePartTriple v) then
    tripleContent v
  else
    -tripleContent v

/--
@isnad1 id=eq.0h1v.s3.cf340e8f142b from=translated src=- shape=f6b6ad72 vocab=cde0878e
-/
@[simp] theorem tripleContent_primitiveDirection (v : Triple) :
    tripleContent (primitiveDirection v) = 1 := by
  simp [primitiveDirection]

/--
@isnad1 id=eq.1h1v.s4.46bb9ffcf3d3 from=translated src=- shape=9d6c7c5e vocab=358c962e
-/
theorem primitivePartTriple_eq_self_of_content_one {v : Triple}
    (hv : tripleContent v = 1) : primitivePartTriple v = v := by
  have hp : (triplePolynomial v).IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_content_eq_one]
    exact hv
  unfold primitivePartTriple
  rw [hp.primPart_eq, polynomialTriple_triplePolynomial]

/--
@isnad1 id=eq.2h1v.s4.d5058ea5eb01 from=translated src=- shape=abfbc4b1 vocab=19b6c26b
-/
theorem primitiveDirection_eq_self_of_content_one_of_oriented {v : Triple}
    (hcontent : tripleContent v = 1) (horiented : FirstNonzeroPositive v) :
    primitiveDirection v = v := by
  rw [primitiveDirection, primitivePartTriple_eq_self_of_content_one hcontent]
  simp [orientDirection, horiented]

/--
@isnad1 id=eq.1h1v.s4.1b560d91ab3c from=translated src=- shape=262b6642 vocab=20664742
-/
@[simp] theorem primitiveDirection_idem {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (primitiveDirection v) = primitiveDirection v := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_primitiveDirection v
  · exact orientDirection_firstNonzeroPositive (primitivePartTriple_ne_zero hv)

/--
@isnad1 id=eq.1h1v.s4.f1e24dcd8436 from=translated src=- shape=262b6642 vocab=efed4f0f
-/
@[simp] theorem primitiveDirection_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (negTriple v) = primitiveDirection v := by
  rw [primitiveDirection, primitivePartTriple_negTriple hv]
  exact orientDirection_neg (primitivePartTriple_ne_zero hv)

/--
@isnad1 id=eq.1h1v.s5.460d355936c4 from=translated src=- shape=e397c93d vocab=a3c78202
-/
@[simp] theorem primitiveDirection_two_vsmul {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (vsmul 2 v) = primitiveDirection v := by
  simp [primitiveDirection, primitivePartTriple_two_vsmul hv]

/-- Every integer vector is an integral multiple of the paper-oriented
primitive part selected from its line.
@isnad1 id=eq.0h1v.s3.d6acaaf0ab7b from=translated src=- shape=fd592461 vocab=62ddefef
-/
theorem direction_decomposition (v : Triple) :
    v = vsmul (directionScale v) (primitiveDirection v) := by
  have hcontent := content_mul_primitivePartTriple v
  by_cases h : FirstNonzeroPositive (primitivePartTriple v)
  · simpa [directionScale, primitiveDirection, orientDirection, h] using hcontent
  · calc
      v = vsmul (tripleContent v) (primitivePartTriple v) := hcontent
      _ = vsmul (-tripleContent v) (negTriple (primitivePartTriple v)) := by
        ext <;> simp [vsmul, negTriple]
      _ = vsmul (directionScale v) (primitiveDirection v) := by
        simp [directionScale, primitiveDirection, orientDirection, h]

/--
@isnad1 id=ne.1h1v.s5.7a99c437fae3 from=translated src=- shape=dfb49cbf vocab=20664742
-/
theorem primitiveDirection_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection v ≠ ⟨0, 0, 0⟩ := by
  intro hd
  have h := direction_decomposition v
  rw [hd] at h
  apply hv
  simpa [vsmul] using h

/--
@isnad1 id=ne.1h1v.s4.a8e106297cca from=translated src=- shape=cce858f6 vocab=d25dcb5d
-/
theorem directionScale_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionScale v ≠ 0 := by
  by_cases h : FirstNonzeroPositive (primitivePartTriple v) <;>
    simp [directionScale, h, tripleContent_ne_zero hv]

end TunnellMap
