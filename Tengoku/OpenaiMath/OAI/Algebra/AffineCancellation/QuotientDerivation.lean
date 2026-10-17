import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.QuotientDerivation
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (I : Ideal R) (D : Derivation k R R)
  (hD : ∀ r ∈ I, D r ∈ I)

def linear : (R ⧸ I) →ₗ[k] (R ⧸ I) :=
  (I.restrictScalars k).liftQ ((Ideal.Quotient.mkₐ k I).toLinearMap.comp D.toLinearMap)
    (by intro r hr; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hD r hr))

/--
@isnad1 id=eq.1h5v.s10.a82248f17b79 from=translated src=- shape=b5d08a5c vocab=e6ed2e76
-/
@[simp] lemma linear_mk (r : R) : linear I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl

def derivation : Derivation k (R ⧸ I) (R ⧸ I) := Derivation.mk' (linear I D hD) (by
  intro r s
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  change linear I D hD ((Ideal.Quotient.mk I) r * (Ideal.Quotient.mk I) s) = _
  rw [← map_mul, linear_mk]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, linear_mk])

/--
@isnad1 id=eq.1h5v.s9.fb797d2b18e5 from=translated src=- shape=3a0abe5d vocab=a7140b82
-/
@[simp] lemma derivation_mk (r : R) : derivation I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl

/--
@isnad1 id=eq.1h6v.s9.515c284b0bd3 from=translated src=- shape=16dadb78 vocab=ace83f11
-/
lemma iterate_mk (r : R) (n : ℕ) :
    (derivation I D hD : (R ⧸ I) → (R ⧸ I))^[n] (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk I ((D : R → R)^[n] r) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, derivation_mk,
      Function.iterate_succ_apply']

/--
@isnad1 id=ex.2h5v.s9.2ba09ba4eef0 from=translated src=- shape=af6614ab vocab=f2e065ff
-/
lemma locallyNilpotent (hn : ∀ r, ∃ n, (D : R → R)^[n] r = 0) :
    ∀ r, ∃ n, (derivation I D hD : (R ⧸ I) → (R ⧸ I))^[n] r = 0 := by
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨n, hn⟩ := hn r
  exact ⟨n, by rw [iterate_mk, hn, map_zero]⟩

/--
@isnad1 id=mem.2h5v.s8.2d4723d36e67 from=translated src=- shape=c3b9d5c0 vocab=35f74989
-/
lemma span_singleton_stable {h : R} (hh : D h ∈ Ideal.span {h}) :
    ∀ r ∈ Ideal.span {h}, D r ∈ Ideal.span {h} := by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ hh)

end ComplexCancellation.QuotientDerivation

end

end OAI
