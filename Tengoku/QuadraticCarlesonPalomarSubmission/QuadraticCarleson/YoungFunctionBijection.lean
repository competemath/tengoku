import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.CounterexampleModular
import Tengoku.Seed.Topology.Order.IntermediateValue
import Tengoku.Seed.Order.Hom.Set

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Young functions are bijections of the nonnegative half-line

This proves the assertion preceding the inverse notation in Section 2.5 of
the paper from the existing Young-function definition, including its identity
exception. No additional growth or regularity hypothesis is imposed.
-/

open Filter Set
open scoped NNReal

namespace QuadraticCarleson.YoungFunction

set_option autoImplicit false

/-- Both the identity exception and superlinear alternative eventually
dominate the identity function.
@isnad1 id=eventual.0h1v.s4.59b665797b05 from=translated src=- shape=bbf4ebab vocab=5e493996
-/
theorem eventually_id_le (Φ : YoungFunction) :
    ∀ᶠ t : ℝ in atTop, t ≤ Φ t := by
  rcases Φ.identity_or_superlinear with hidentity | hsuperlinear
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact le_of_eq (hidentity t ht).symm
  · filter_upwards [hsuperlinear.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_ge_atTop (1 : ℝ)] with t hratio ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    simpa only [one_mul] using (le_div_iff₀ htpos).mp hratio

/--
@isnad1 id=tendsto.0h1v.s3.24e1e7dd1d02 from=translated src=- shape=74931b86 vocab=e49198aa
-/
theorem tendsto_atTop (Φ : YoungFunction) : Tendsto Φ atTop atTop :=
  tendsto_atTop_mono' atTop Φ.eventually_id_le tendsto_id

/-- The source's bijection assertion on exactly `[0,∞)`.
@isnad1 id=bijon.0h1v.s4.c09e307a4159 from=translated src=- shape=31acc366 vocab=1c6f6218
-/
theorem bijOn_nonneg (Φ : YoungFunction) : BijOn Φ (Ici 0) (Ici 0) := by
  refine ⟨fun _ ht ↦ Φ.nonneg ht, Φ.strictMonoOn_nonneg.injOn, ?_⟩
  simpa only [SurjOn, Φ.map_zero] using
    intermediate_value_Ici Φ.continuousOn_nonneg Φ.tendsto_atTop

/-- The Young function and its inverse, as an order-preserving bijection of
the nonnegative real numbers.-/
noncomputable def nonnegOrderIso (Φ : YoungFunction) : ℝ≥0 ≃o ℝ≥0 := by
  apply StrictMono.orderIsoOfSurjective
    (fun t : ℝ≥0 ↦ (⟨Φ t, Φ.nonneg t.property⟩ : ℝ≥0))
  · intro x y hxy
    exact Φ.strictMonoOn_nonneg x.property y.property hxy
  · intro y
    obtain ⟨x, hx, hxy⟩ := Φ.bijOn_nonneg.2.2 y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/--
@isnad1 id=eq.0h2v.s5.a4efa57a16ae from=translated src=- shape=90de9587 vocab=1ebab6fb
-/
@[simp] theorem nonnegOrderIso_apply (Φ : YoungFunction) (t : ℝ≥0) :
    (Φ.nonnegOrderIso t : ℝ) = Φ t := rfl

/-- The inverse provided by the paper's notation is a right inverse.
@isnad1 id=eq.0h2v.s5.8849c1bcd43a from=translated src=- shape=64fab260 vocab=fc52b193
-/
@[simp] theorem apply_nonnegOrderIso_symm (Φ : YoungFunction) (t : ℝ≥0) :
    Φ (Φ.nonnegOrderIso.symm t : ℝ) = t :=
  congrArg (fun y : ℝ≥0 ↦ (y : ℝ)) (Φ.nonnegOrderIso.apply_symm_apply t)

/-- The same inverse is a left inverse on the entire nonnegative half-line.
@isnad1 id=eq.0h2v.s6.1bc18ef873b4 from=translated src=- shape=0ddba147 vocab=998ab8c2
-/
@[simp] theorem nonnegOrderIso_symm_apply (Φ : YoungFunction) (t : ℝ≥0) :
    Φ.nonnegOrderIso.symm ⟨Φ t, Φ.nonneg t.property⟩ = t :=
  Φ.nonnegOrderIso.symm_apply_apply t

end QuadraticCarleson.YoungFunction
