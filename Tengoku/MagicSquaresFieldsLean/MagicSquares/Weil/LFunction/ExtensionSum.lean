import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.SplitPolynomial
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.NormLift
import Tengoku.Seed.RingTheory.Norm.Transitivity
import Tengoku.Seed.FieldTheory.Finite.Extension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- The norm of an algebraic element, expressed through its minimal
polynomial and the relative degree of its generated subfield.
@isnad1 id=eq.0h3v.s8.1f49ffbe13b0 from=translated src=- shape=193707d0 vocab=e7834cdd
-/
theorem norm_eq_minpoly_constant (x : E) :
    Algebra.norm F x =
      ((-1 : F) ^ (minpoly F x).natDegree * (minpoly F x).coeff 0) ^
        (Module.finrank F E / (minpoly F x).natDegree) := by
  have hx := IsIntegral.of_finite F x
  have hd : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hx
  have hr : Module.finrank F E / (minpoly F x).natDegree =
      Module.finrank F⟮x⟯ E := by
    rw [← adjoin.finrank hx, ← Module.finrank_mul_finrank F F⟮x⟯ E]
    exact Nat.mul_div_right _ (by rwa [adjoin.finrank hx])
  rw [hr, Algebra.norm_eq_norm_adjoin F x, ← adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, adjoin.powerBasis_dim,
    adjoin.powerBasis_gen, IntermediateField.minpoly_gen]

/-- The norm of `x-a` is the signed evaluation of the minimal polynomial
of `x`, raised to the number of repetitions of its conjugates in `E`.
@isnad1 id=eq.0h4v.s8.ec649d5aff39 from=translated src=- shape=1206aa53 vocab=f6095a1a
-/
theorem norm_sub_algebraMap_eq_minpoly_eval (x : E) (a : F) :
    Algebra.norm F (x - algebraMap F E a) =
      ((-1 : F) ^ (minpoly F x).natDegree * (minpoly F x).eval a) ^
        (Module.finrank F E / (minpoly F x).natDegree) := by
  rw [norm_eq_minpoly_constant, minpoly.sub_algebraMap]
  simp only [natDegree_comp, natDegree_X_add_C, mul_one,
    coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]

variable [Fintype F] [Fintype E]

/-- The actual character sum over an extension, with every character
lifted by the extension norm.-/
noncomputable def splitExtensionSum {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) : ℂ :=
  ∑ x : E, ∏ i, normLift (E := E) (chars i) (x - algebraMap F E (roots i))

omit [Fintype F] in
/-- The summand is the weight of the minimal polynomial raised to the
relative extension degree. This includes points where a character vanishes.
@isnad1 id=eq.0h6v.s8.5e398ba98a0e from=translated src=- shape=9c721cd5 vocab=a83474fa
-/
theorem splitExtensionSummand_eq_minpoly_weight {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (x : E) :
    (∏ i, normLift (E := E) (chars i) (x - algebraMap F E (roots i))) =
      splitDegreeWeight roots chars (minpoly F x).natDegree (minpoly F x) ^
        (Module.finrank F E / (minpoly F x).natDegree) := by
  simp only [normLift_apply, norm_sub_algebraMap_eq_minpoly_eval,
    map_pow, map_mul, Finset.prod_pow, Finset.prod_mul_distrib,
    splitDegreeWeight, splitWeightPhase, splitEvaluationWeight]

/-- The finite set of minimal polynomials represented by elements of `E`.-/
noncomputable def extensionMinimalPolynomials : Finset (Polynomial F) := by
  classical
  exact Finset.univ.image (minpoly F : E → Polynomial F)

omit [Fintype F] in
/-- A polynomial occurs as a minimal polynomial in `E` exactly when it is
monic irreducible and its degree divides the extension degree.
@isnad1 id=iff.0h3v.s7.94d4cd672126 from=translated src=- shape=a1104a4d vocab=e288b928
-/
theorem mem_extensionMinimalPolynomials_iff (p : Polynomial F) :
    p ∈ extensionMinimalPolynomials (F := F) (E := E) ↔
      p.Monic ∧ Irreducible p ∧ p.natDegree ∣ Module.finrank F E := by
  classical
  constructor
  · intro hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    have hx := IsIntegral.of_finite F x
    exact ⟨minpoly.monic hx, minpoly.irreducible hx, minpoly.degree_dvd hx⟩
  · rintro ⟨hmon, hirr, hd⟩
    letI : Fact (Irreducible p) := ⟨hirr⟩
    have hr : Module.finrank F (AdjoinRoot p) = p.natDegree :=
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank
    obtain ⟨phi⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
      (F := F) (K := AdjoinRoot p) (L := E) (hr.symm ▸ hd)
    have he := minpoly.eq_of_irreducible hirr (AdjoinRoot.aeval_algHom_eq_zero p phi)
    apply Finset.mem_image.mpr
    refine ⟨phi (AdjoinRoot.root p), Finset.mem_univ _, ?_⟩
    simpa only [hmon.leadingCoeff, inv_one, C_1, mul_one] using he.symm

/-- In a finite field extension, every represented minimal polynomial has
exactly its degree many roots.
@isnad1 id=eq.1h3v.s7.6a9ffcb6db5b from=translated src=- shape=f192df5b vocab=7e23c094
-/
theorem card_minpoly_fiber (p : Polynomial F)
    (hp : p ∈ extensionMinimalPolynomials (F := F) (E := E)) :
    (Finset.univ.filter (fun x : E => minpoly F x = p)).card = p.natDegree := by
  classical
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
  have hx := IsIntegral.of_finite F x
  have hmon := minpoly.monic hx
  have hirr := minpoly.irreducible hx
  have hnz : (minpoly F x).map (algebraMap F E) ≠ 0 :=
    (hmon.map _).ne_zero
  have hfiber : Finset.univ.filter (fun y : E => minpoly F y = minpoly F x) =
      ((minpoly F x).map (algebraMap F E)).roots.toFinset := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset, mem_roots hnz, IsRoot.def, eval_map_algebraMap]
    constructor
    · intro h
      rw [← h]
      exact minpoly.aeval F y
    · intro h
      have he := minpoly.eq_of_irreducible hirr h
      simpa only [hmon.leadingCoeff, inv_one, C_1, mul_one] using he.symm
  rw [hfiber, Multiset.card_toFinset,
    Multiset.dedup_eq_self.mpr (nodup_roots
      (PerfectField.separable_of_irreducible hirr).map),
    ← (Normal.splits (inferInstance : Normal F E) x).natDegree_eq_card_roots,
    natDegree_map]

/-- Group the actual extension-field sum by minimal polynomials. Each
irreducible contributes its degree times its weight to the relative power.
@isnad1 id=eq.0h5v.s7.6d65ca2d8928 from=translated src=- shape=e14bc6e1 vocab=87dbdea8
-/
theorem splitExtensionSum_eq_sum_minpoly_weights {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) :
    splitExtensionSum (E := E) roots chars =
      ∑ p ∈ extensionMinimalPolynomials (F := F) (E := E),
        (p.natDegree : ℂ) *
          splitDegreeWeight roots chars p.natDegree p ^
            (Module.finrank F E / p.natDegree) := by
  classical
  unfold splitExtensionSum
  simp_rw [splitExtensionSummand_eq_minpoly_weight]
  rw [← Finset.sum_fiberwise_of_maps_to'
    (s := Finset.univ) (t := extensionMinimalPolynomials (F := F) (E := E))
    (g := minpoly F) (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
    (fun p : Polynomial F => splitDegreeWeight roots chars p.natDegree p ^
      (Module.finrank F E / p.natDegree))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_const, nsmul_eq_mul, card_minpoly_fiber p hp]

end MagicSquares.LN97
