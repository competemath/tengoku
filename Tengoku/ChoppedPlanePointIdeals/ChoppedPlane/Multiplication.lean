module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Quotient
public import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Multiplication by a genuine family of homogeneous generators. Adapted from
`Froberg.Koszul` by allowing an arbitrary multiplier degree. -/
noncomputable section
namespace ChoppedPlane
open Module
variable {K : Type*} [Field K] {n d e r : ℕ}

def generatorSpace (q : Fin r → Forms K n d) : Submodule K (Poly K n) :=
  Submodule.span K (Set.range (fun i => (q i).val))

/--
@isnad1 id=le.0h5v.s9.2ca1661568c6 from=translated src=- shape=d73c7602 vocab=4d0cb19b
-/
theorem generatorSpace_le (q : Fin r → Forms K n d) :
    generatorSpace q ≤ Forms K n d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (q i).property

def multiplication (q : Fin r → Forms K n d) :
    (Fin r → Forms K n e) →ₗ[K] Forms K n (d + e) :=
  ∑ i, (mulForm (e := e) (q i)).comp (LinearMap.proj i)

/--
@isnad1 id=eq.0h7v.s12.46dfcfbcfc2f from=translated src=- shape=a5e55f52 vocab=9f079294
-/
theorem multiplication_val (q : Fin r → Forms K n d) (a : Fin r → Forms K n e) :
    (multiplication q a).val = ∑ i, (q i).val * (a i).val := by
  simp [multiplication, mulForm]

/--
@isnad1 id=eq.0h6v.s11.4dc557c7639e from=translated src=- shape=3025ed6d vocab=1c30ab39
-/
theorem range_ambient_multiplication (q : Fin r → Forms K n d) :
    LinearMap.range ((Forms K n (d + e)).subtype.comp (multiplication q)) =
      generatorSpace q * Forms K n e := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    change (multiplication q a).val ∈ _
    rw [multiplication_val]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (a i).property
  · apply Submodule.mul_le.mpr
    intro f hf a ha
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine ⟨fun i => c i • (⟨a, ha⟩ : Forms K n e), ?_⟩
    change (multiplication q (fun i => c i • (⟨a, ha⟩ : Forms K n e))).val = _
    simp [multiplication_val, Finset.sum_mul]

/--
@isnad1 id=eq.0h6v.s11.544217316858 from=translated src=- shape=bc11b75b vocab=a7a15e2a
-/
theorem range_multiplication (q : Fin r → Forms K n d) :
    LinearMap.range (multiplication (e := e) q) = generatedProducts (d := d) (generatorSpace q) e := by
  have h := congrArg (fun P : Submodule K (Poly K n) =>
      P.comap (Forms K n (d + e)).subtype) (range_ambient_multiplication (e := e) q)
  rw [LinearMap.range_comp,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)] at h
  exact h

/--
@isnad1 id=eq.0h6v.s12.cadcfa46a97c from=translated src=- shape=b465e339 vocab=92c4bbb0
-/
theorem generatedHilbertFunction_add_rank (q : Fin r → Forms K n d) :
    generatedHilbertFunction (generatorSpace q) (d + e) +
      finrank K (LinearMap.range (multiplication (e := e) q)) =
        finrank K (Forms K n (d + e)) := by
  rw [← generated_finrank_eq_hilbertFunction _ (generatorSpace_le q) e,
    range_multiplication]
  exact (generatedProducts (d := d) (generatorSpace q) e).finrank_quotient_add_finrank

/--
@isnad1 id=le.0h6v.s12.13d527995204 from=translated src=- shape=2ca3b325 vocab=31f762eb
-/
theorem multiplication_rank_le (q : Fin r → Forms K n d) :
    finrank K (LinearMap.range (multiplication (e := e) q)) ≤
      r * finrank K (Forms K n e) := by
  simpa [Module.finrank_pi_fintype] using
    LinearMap.finrank_range_le (multiplication (e := e) q)

/-- The source dimension gives the universal lower bound for the quotient.
@isnad1 id=le.0h6v.s10.bd993658d5aa from=translated src=- shape=eca6f45e vocab=9222d614
-/
theorem generatedHilbertFunction_lower_bound (q : Fin r → Forms K n d) :
    finrank K (Forms K n (d + e)) - r * finrank K (Forms K n e) ≤
      generatedHilbertFunction (generatorSpace q) (d + e) := by
  have h := generatedHilbertFunction_add_rank (e := e) q
  have h' := multiplication_rank_le (e := e) q
  omega

end ChoppedPlane
