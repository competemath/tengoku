import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

noncomputable def kernelPolynomial (S : Finset (R × R)) : R[X] :=
  ∏ P ∈ S, (X - C P.1)

/--
@isnad1 id=eq.0h1v.s5.b7c372b28765 from=translated src=- shape=6b56a21e vocab=b6dc5640
-/
@[simp] theorem kernelPolynomial_empty : kernelPolynomial (∅ : Finset (R × R)) = 1 := by
  simp [kernelPolynomial]

/--
@isnad1 id=eq.1h3v.s7.071b9feccdd4 from=translated src=- shape=0e057bf0 vocab=cd4a67a9
-/
theorem kernelPolynomial_cons {P : R × R} {S : Finset (R × R)} (hP : P ∉ S) :
    kernelPolynomial (Finset.cons P S hP) = (X - C P.1) * kernelPolynomial S := by
  simp [kernelPolynomial, Finset.prod_cons]

/--
@isnad1 id=eq.1h3v.s7.eda2ead31e58 from=translated src=- shape=b507aa7d vocab=e9f0f9fa
-/
theorem kernelPolynomial_insert [DecidableEq R] {P : R × R} {S : Finset (R × R)} (hP : P ∉ S) :
    kernelPolynomial (insert P S) = (X - C P.1) * kernelPolynomial S := by
  simp [kernelPolynomial, Finset.prod_insert hP]

/--
@isnad1 id=eq.0h2v.s7.ddc2b385a365 from=translated src=- shape=a7e28265 vocab=1ca34f5e
-/
@[simp] theorem kernelPolynomial_singleton (P : R × R) :
    kernelPolynomial ({P} : Finset (R × R)) = X - C P.1 := by
  simp [kernelPolynomial]

/--
@isnad1 id=eq.0h2v.s7.415b83880eb7 from=translated src=- shape=83293f7e vocab=17368626
-/
theorem kernelPolynomial_eq_multiset_prod (S : Finset (R × R)) :
    kernelPolynomial S = ((S.val.map Prod.fst).map fun x => X - C x).prod := by
  rw [kernelPolynomial, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

/--
@isnad1 id=monic.0h2v.s4.b14916b8906c from=translated src=- shape=b2df656f vocab=de6cd0a9
-/
theorem monic_kernelPolynomial (S : Finset (R × R)) : (kernelPolynomial S).Monic :=
  monic_prod_of_monic _ _ fun P _ => monic_X_sub_C P.1

/--
@isnad1 id=eq.0h2v.s4.319424af7a68 from=translated src=- shape=c4b091b5 vocab=e47408cd
-/
theorem natDegree_kernelPolynomial [Nontrivial R] (S : Finset (R × R)) :
    (kernelPolynomial S).natDegree = S.card := by
  rw [kernelPolynomial, natDegree_prod_of_monic _ _ fun P _ => monic_X_sub_C P.1]
  simp

/--
@isnad1 id=eq.0h3v.s5.ccf5790d1c67 from=translated src=- shape=53b0dd63 vocab=f7500cb8
-/
theorem eval_kernelPolynomial (S : Finset (R × R)) (x : R) :
    (kernelPolynomial S).eval x = ∏ P ∈ S, (x - P.1) := by
  simp [kernelPolynomial, eval_prod]

/--
@isnad1 id=eq.1h3v.s6.82899106937b from=translated src=- shape=640f5d7b vocab=053ae73b
-/
theorem eval_kernelPolynomial_eq_zero {S : Finset (R × R)} {P : R × R} (hP : P ∈ S) :
    (kernelPolynomial S).eval P.1 = 0 := by
  rw [eval_kernelPolynomial]
  exact Finset.prod_eq_zero hP (sub_self _)

/--
@isnad1 id=eq.0h4v.s7.8a3891643e3a from=translated src=- shape=ce9484c3 vocab=0d7decdf
-/
theorem map_kernelPolynomial {S' : Type*} [CommRing S'] (f : R →+* S') (S : Finset (R × R)) :
    (kernelPolynomial S).map f = ∏ P ∈ S, (X - C (f P.1)) := by
  simp [kernelPolynomial, Polynomial.map_prod]

/--
@isnad1 id=eq.1h4v.s8.7accf74f91c4 from=translated src=- shape=922d1ef7 vocab=9cbfdb19
-/
theorem map_kernelPolynomial_of_injOn {S' : Type*} [CommRing S'] [DecidableEq S'] (f : R →+* S')
    (S : Finset (R × R)) (hf : Set.InjOn (Prod.map f f) S) :
    (kernelPolynomial S).map f = kernelPolynomial (S.image (Prod.map f f)) := by
  rw [map_kernelPolynomial, kernelPolynomial, Finset.prod_image hf]
  simp

/--
@isnad1 id=eq.0h2v.s5.6c11361aefff from=translated src=- shape=e3234b86 vocab=486e037a
-/
theorem roots_kernelPolynomial [IsDomain R] (S : Finset (R × R)) :
    (kernelPolynomial S).roots = S.val.map Prod.fst := by
  rw [kernelPolynomial_eq_multiset_prod, roots_multiset_prod_X_sub_C]

/--
@isnad1 id=iff.0h3v.s6.1bcfc614be35 from=translated src=- shape=4cacf20f vocab=83e6ddfe
-/
theorem eval_kernelPolynomial_eq_zero_iff [IsDomain R] {S : Finset (R × R)} {x : R} :
    (kernelPolynomial S).eval x = 0 ↔ ∃ P ∈ S, P.1 = x := by
  rw [eval_kernelPolynomial, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

end WeierstrassCurve
