import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.NewtonPowers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact restriction to a supporting zero face, including multiplication,
powers, constant terms, and the full Newton-polytope face identity. -/

open Set
namespace DuistermaatVanDerKallen
noncomputable section

variable {M : Type*} [AddCommGroup M]

/-- Retain precisely the terms of zero weight.-/
def facePart (w : M →+ ℝ) (f : AddMonoidAlgebra ℂ M) : AddMonoidAlgebra ℂ M := by
  classical
  exact .ofCoeff (f.coeff.filter (fun a => w a = 0))

/--
@isnad1 id=eq.0h4v.s7.05511f39c2f6 from=translated src=- shape=7c01b10e vocab=56ff656d
-/
theorem facePart_coeff (w : M →+ ℝ) (f : AddMonoidAlgebra ℂ M) (a : M) :
    (facePart w f).coeff a = if w a = 0 then f.coeff a else 0 := by
  classical
  rfl

/--
@isnad1 id=eq.2h4v.s8.407a31902617 from=translated src=- shape=97d4b75d vocab=9fcf5792
-/
theorem facePart_mul (w : M →+ ℝ) (f g : AddMonoidAlgebra ℂ M)
    (hf : ∀ a ∈ f.coeff.support, 0 ≤ w a) (hg : ∀ a ∈ g.coeff.support, 0 ≤ w a) :
    facePart w (f * g) = facePart w f * facePart w g := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext x
  rw [facePart_coeff, AddMonoidAlgebra.coeff_mul, AddMonoidAlgebra.coeff_mul]
  simp only [facePart, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum_filter_index]
  simp only [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]
  by_cases hx : w x = 0
  · simp only [hx, ite_true]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ha0 : w a = 0
    · simp only [ha0, ite_true]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hb0 : w b = 0
      · simp [hb0]
      · have hab : a + b ≠ x := by
          intro he
          apply hb0
          have he' := congrArg w he
          simpa [map_add, ha0, hx] using he'
        simp [hb0, hab]
    · simp only [ha0, ite_false]
      apply Finset.sum_eq_zero
      intro b hb
      have hab : a + b ≠ x := by
        intro he
        have he' := congrArg w he
        simp only [map_add, hx] at he'
        exact ha0 (by linarith [hf a ha, hg b hb])
      simp [hab]
  · simp only [hx, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    by_cases ha0 : w a = 0
    · simp only [ha0, ite_true]
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hb0 : w b = 0
      · have hab : a + b ≠ x := by
          intro he
          apply hx
          rw [← he, map_add, ha0, hb0, add_zero]
        simp [hb0, hab]
      · simp [hb0]
    · simp [ha0]

/--
@isnad1 id=eq.0h2v.s6.9d758dea56db from=translated src=- shape=9c55ec2c vocab=bf19daf0
-/
theorem facePart_one (w : M →+ ℝ) : facePart w (1 : AddMonoidAlgebra ℂ M) = 1 := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext a
  rw [facePart_coeff]
  by_cases ha : a = 0
  · simp [ha]
  · simp [AddMonoidAlgebra.one_def, ha]

/--
@isnad1 id=eq.1h4v.s7.bad41a1b16c3 from=translated src=- shape=5c9d8f12 vocab=5e2ab880
-/
theorem facePart_pow (w : M →+ ℝ) (f : AddMonoidAlgebra ℂ M)
    (hf : ∀ a ∈ f.coeff.support, 0 ≤ w a) (n : ℕ) :
    facePart w (f ^ n) = facePart w f ^ n := by
  induction n with
  | zero => simpa using facePart_one w
  | succ n ih =>
    have hn : ∀ a ∈ (f ^ n).coeff.support, 0 ≤ w a := by
      simpa using support_pow_lower_bound w f 0 hf n
    rw [pow_succ, facePart_mul w (f ^ n) f hn hf, ih, pow_succ]

/--
@isnad1 id=eq.1h4v.s8.ecbe3b77a8f0 from=translated src=- shape=dc54e3e8 vocab=e2debac5
-/
theorem facePart_pow_coeff_zero (w : M →+ ℝ) (f : AddMonoidAlgebra ℂ M)
    (hf : ∀ a ∈ f.coeff.support, 0 ≤ w a) (n : ℕ) :
    (facePart w f ^ n).coeff 0 = (f ^ n).coeff 0 := by
  rw [← facePart_pow w f hf n, facePart_coeff]
  simp

/-- Cutting a finite convex hull by a supporting zero hyperplane commutes
with taking the convex hull.
@isnad1 id=eq.2h3v.s9.3c0ceefbacd3 from=translated src=- shape=a246f429 vocab=667022c0
-/
theorem finite_convexHull_inter_zero {d : ℕ} {S : Set (Fin d → ℝ)} (hS : S.Finite)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (hL : ∀ x ∈ S, 0 ≤ L x) :
    convexHull ℝ (S ∩ {x | L x = 0}) = convexHull ℝ S ∩ {x | L x = 0} := by
  let Q := convexHull ℝ S ∩ {x | L x = 0}
  have hnonneg : ∀ x ∈ convexHull ℝ S, 0 ≤ L x :=
    convexHull_min hL ((convex_Ici (0 : ℝ)).linear_preimage L.toLinearMap)
  have hQconv : Convex ℝ Q := (convex_convexHull ℝ S).inter
    ((convex_singleton (0 : ℝ)).linear_preimage L.toLinearMap)
  have hQcomp : IsCompact Q := (hS.isCompact_convexHull ℝ).inter_right
    (isClosed_eq L.continuous continuous_const)
  have hface : IsExtreme ℝ (convexHull ℝ S) Q := by
    refine ⟨inter_subset_left, ?_⟩
    intro x hx y hy z hz hseg
    obtain ⟨a, b, ha, hb, _, he⟩ := hseg
    refine ⟨hx, ?_⟩
    have he' := congrArg L he
    simp only [map_add, map_smul, smul_eq_mul] at he'
    have hz0 : L z = 0 := hz.2
    have hm : a * L x = 0 := by
      nlinarith [mul_nonneg ha.le (hnonneg x hx), mul_nonneg hb.le (hnonneg y hy)]
    exact (mul_eq_zero.mp hm).resolve_left ha.ne'
  apply Subset.antisymm
  · exact convexHull_min (fun x hx => ⟨subset_convexHull ℝ S hx.1, hx.2⟩) hQconv
  · have hv : Q.extremePoints ℝ ⊆ S ∩ {x | L x = 0} := by
      intro x hx
      exact ⟨extremePoints_convexHull_subset (hface.extremePoints_subset_extremePoints hx), hx.1.2⟩
    have he := closure_convexHull_extremePoints hQcomp hQconv
    change Q ⊆ _
    rw [← he]
    exact closure_minimal (convexHull_mono hv) ((hS.inter_of_left _).isCompact_convexHull ℝ).isClosed

/-- The additive weight of an exponent induced by a real linear functional.-/
def exponentFunctional {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) : (Fin d → ℤ) →+ ℝ where
  toFun a := L (exponentVector a)
  map_zero' := by
    have hz : exponentVector (0 : Fin d → ℤ) = 0 := by ext i; simp [exponentVector]
    rw [hz, map_zero]
  map_add' a b := by rw [exponentVector_add, map_add]

/--
@isnad1 id=iff.0h4v.s7.921faca504c2 from=translated src=- shape=58f80cbb vocab=2ae6dd47
-/
theorem mem_support_facePart (w : M →+ ℝ) (f : AddMonoidAlgebra ℂ M) (a : M) :
    a ∈ (facePart w f).coeff.support ↔ a ∈ f.coeff.support ∧ w a = 0 := by
  classical
  simp only [facePart, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.support_filter, Finset.mem_filter]

/-- Face restriction has exactly the intersection polytope, with no extra
hypothesis excluding coefficient cancellation in products.
@isnad1 id=eq.1h3v.s8.f56a5e760cfa from=translated src=- shape=09c88a1b vocab=f32400ac
-/
theorem newtonPolytope_facePart {d : ℕ} (f : MultiLaurent d)
    (L : (Fin d → ℝ) →L[ℝ] ℝ)
    (hL : ∀ a ∈ f.coeff.support, 0 ≤ L (exponentVector a)) :
    newtonPolytope (facePart (exponentFunctional L) f) =
      newtonPolytope f ∩ {x | L x = 0} := by
  have he : exponentVector '' ((facePart (exponentFunctional L) f).coeff.support : Set (Fin d → ℤ)) =
      (exponentVector '' (f.coeff.support : Set (Fin d → ℤ))) ∩ {x | L x = 0} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' := (mem_support_facePart (exponentFunctional L) f a).mp ha
      exact ⟨⟨a, ha'.1, rfl⟩, ha'.2⟩
    · rintro ⟨⟨a, ha, rfl⟩, hLa⟩
      exact ⟨a, (mem_support_facePart (exponentFunctional L) f a).mpr ⟨ha, hLa⟩, rfl⟩
  unfold newtonPolytope
  rw [he]
  exact finite_convexHull_inter_zero (f.coeff.support.finite_toSet.image exponentVector) L
    (by rintro _ ⟨a, ha, rfl⟩; exact hL a ha)

/--
@isnad1 id=mem.2h3v.s8.f5406c398cf0 from=translated src=- shape=c20bbef0 vocab=c40f4cc4
-/
theorem origin_mem_newtonPolytope_facePart {d : ℕ} (f : MultiLaurent d)
    (L : (Fin d → ℝ) →L[ℝ] ℝ)
    (hL : ∀ a ∈ f.coeff.support, 0 ≤ L (exponentVector a))
    (hf : (0 : Fin d → ℝ) ∈ newtonPolytope f) :
    (0 : Fin d → ℝ) ∈ newtonPolytope (facePart (exponentFunctional L) f) := by
  rw [newtonPolytope_facePart f L hL]
  exact ⟨hf, map_zero L⟩

/--
@isnad1 id=ne.2h3v.s8.daf1e77788e1 from=translated src=- shape=229936d8 vocab=fb3cdc05
-/
theorem facePart_ne_zero {d : ℕ} (f : MultiLaurent d)
    (L : (Fin d → ℝ) →L[ℝ] ℝ)
    (hL : ∀ a ∈ f.coeff.support, 0 ≤ L (exponentVector a))
    (hf : (0 : Fin d → ℝ) ∈ newtonPolytope f) :
    facePart (exponentFunctional L) f ≠ 0 := by
  intro he
  have hm := origin_mem_newtonPolytope_facePart f L hL hf
  rw [he] at hm
  simp [newtonPolytope] at hm

/-- Every power constant term is unchanged on a supporting face through zero.
@isnad1 id=eq.1h4v.s8.5f027dd77c86 from=translated src=- shape=4c73af4c vocab=1654d247
-/
theorem constantTerm_facePart_pow {d : ℕ} (f : MultiLaurent d)
    (L : (Fin d → ℝ) →L[ℝ] ℝ)
    (hL : ∀ a ∈ f.coeff.support, 0 ≤ L (exponentVector a)) (n : ℕ) :
    constantTerm (facePart (exponentFunctional L) f ^ n) = constantTerm (f ^ n) :=
  facePart_pow_coeff_zero (exponentFunctional L) f hL n

/-- A proper supporting cut decreases the number of support exponents.
@isnad1 id=lt.2h4v.s7.bd8b218b6d48 from=translated src=- shape=075f6708 vocab=a8910b08
-/
theorem facePart_support_card_lt (w : M →+ ℝ) (f : AddMonoidAlgebra ℂ M)
    {a : M} (ha : a ∈ f.coeff.support) (hwa : w a ≠ 0) :
    (facePart w f).coeff.support.card < f.coeff.support.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro b hb
    exact ((mem_support_facePart w f b).mp hb).1
  · intro he
    have hm : a ∈ (facePart w f).coeff.support := he.symm ▸ ha
    exact hwa ((mem_support_facePart w f a).mp hm).2

end
end DuistermaatVanDerKallen
