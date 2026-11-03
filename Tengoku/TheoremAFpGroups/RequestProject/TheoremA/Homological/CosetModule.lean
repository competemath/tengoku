module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Homological.Induction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coset module `M = ℤ[E / ι B]` and the induced augmentation

`εM : ℤ[E]^{c 0} → M` is the induced augmentation `ℤ[E] ⊗_{ℤ[B]} F_0 → ℤ[E] ⊗_{ℤ[B]} ℤ = M`.
-/

@[expose] public section

namespace TheoremA

universe u

open MonoidAlgebra

variable {B E : Type u} [Group B] [Group E] (ι : B →* E) (hι : Function.Injective ι)

/-- The projection `ℤ[E] → ℤ[E / ι B]`.-/
noncomputable def πM : ZG E →+ ((E ⧸ ι.range) →₀ ℤ) :=
  (Finsupp.mapDomain.addMonoidHom (cosetOf ι)).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

/--
@isnad1 id=eq.0h5v.s8.b907a65d0061 from=translated src=- shape=e52009b8 vocab=b8bb032f
-/
theorem πM_single (e : E) (n : ℤ) :
    πM ι (MonoidAlgebra.single e n) = Finsupp.single (cosetOf ι e) n := by
  show Finsupp.mapDomain _ (Finsupp.single e n) = _
  exact Finsupp.mapDomain_single

/--
@isnad1 id=eq.1h5v.s9.1d8bcf319947 from=translated src=- shape=4f8b5891 vocab=ce47ae35
-/
theorem πM_apply (f : ZG E) (q : E ⧸ ι.range) : πM ι f q = augZG (decomp ι hι f q) := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, ha, hb, map_add]
  | single e n =>
    rw [πM_single, decomp_single]
    by_cases h : cosetOf ι e = q
    · subst h; simp
    · simp [h]

/-- The sum of coefficients `M → ℤ`.-/
noncomputable def augM : ((E ⧸ ι.range) →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

/--
@isnad1 id=eq.0h5v.s8.3d2098e032a2 from=translated src=- shape=8e08cbdc vocab=2053a4fc
-/
theorem augM_single (q : E ⧸ ι.range) (n : ℤ) : augM ι (Finsupp.single q n) = n := by
  unfold augM
  rw [Finsupp.liftAddHom_apply_single]; rfl

/--
@isnad1 id=eq.0h4v.s8.f61017a87902 from=translated src=- shape=68c6c369 vocab=71e750f3
-/
theorem augM_πM (f : ZG E) : augM ι (πM ι f) = augZG f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | single e n => rw [πM_single, augM_single, augZG_single]

variable {k : ℕ} (R : Res B k)

/-- The induced augmentation `ℤ[E]^{c 0} → M`.-/
noncomputable def εM : FreeMod E (R.c 0) →+ ((E ⧸ ι.range) →₀ ℤ) where
  toFun v := ∑ j, R.ε (Pi.single j 1) • πM ι (v j)
  map_zero' := by simp
  map_add' v w := by simp [smul_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h4v.s9.23a37ca5e2fb from=translated src=- shape=54af1032 vocab=459279df
-/
theorem ε_eq_sum (x : FreeMod B (R.c 0)) :
    R.ε x = ∑ j, augZG (x j) * R.ε (Pi.single j 1) := by
  conv_lhs => rw [eq_sum_single x]
  simp [map_sum, Res.ε_smul]

/--
@isnad1 id=eq.1h7v.s10.492351f5bbda from=translated src=- shape=f7134529 vocab=f1cddcd8
-/
theorem εM_apply (v : FreeMod E (R.c 0)) (q : E ⧸ ι.range) :
    εM ι R v q = R.ε (compV ι hι q v) := by
  rw [ε_eq_sum]
  simp only [εM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, πM_apply ι hι, compV_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The induced augmentation `ℤ[E]^{c 0} → ℤ`.-/
noncomputable def εA : FreeMod E (R.c 0) →+ ℤ := (augM ι).comp (εM ι R)

/--
@isnad1 id=eq.0h6v.s9.a9f4e67907b9 from=translated src=- shape=f436950f vocab=0ce3ebee
-/
theorem εA_apply (v : FreeMod E (R.c 0)) : εA ι R v = ∑ j, augZG (v j) * R.ε (Pi.single j 1) := by
  simp [εA, εM, augM_πM, mul_comm]

/--
@isnad1 id=eq.0h7v.s9.20e052d6b828 from=translated src=- shape=8774f987 vocab=ef9e16f4
-/
theorem εA_inv (g : E) (v : FreeMod E (R.c 0)) :
    εA ι R (MonoidAlgebra.of ℤ E g • v) = εA ι R v := by
  simp [εA_apply, map_mul]

include hι in
/-- Exactness of the induced sequence at `ℤ[E]^{c 0}`: `ker εM = im (ℤ[E] ⊗ d_0)`.
@isnad1 id=mem.2h6v.s10.1da29712fd8a from=translated src=- shape=2da87f72 vocab=ef2f5614
-/
theorem ker_εM (v : FreeMod E (R.c 0)) (h : εM ι R v = 0) :
    v ∈ LinearMap.range (indMap ι (R.d 0)) := by
  apply mem_range_indMap ι hι
  intro q
  have : compV ι hι q v ∈ R.ε.ker := by
    show R.ε _ = 0
    rw [← εM_apply ι hι, h, Finsupp.zero_apply]
  rw [R.exact0] at this
  exact this

include hι in
/--
@isnad1 id=eq.1h6v.s10.35fb39849afb from=translated src=- shape=0e2396c3 vocab=a0e078f0
-/
theorem indMap_d0_εM (x : FreeMod E (R.c 1)) : εM ι R (indMap ι (R.d 0) x) = 0 := by
  ext q
  rw [εM_apply ι hι, compV_indMap, R.ε_d, Finsupp.zero_apply]

include hι in
/--
@isnad1 id=eq.1h7v.s10.f455f8e396d2 from=translated src=- shape=dce42b05 vocab=103e74e2
-/
theorem εM_out_smul (q : E ⧸ ι.range) (w : FreeMod B (R.c 0)) :
    εM ι R (MonoidAlgebra.single q.out (1 : ℤ) • ρV ι w) = Finsupp.single q (R.ε w) := by
  classical
  ext q'
  rw [εM_apply ι hι, compV_out_smul]
  by_cases h : q = q'
  · subst h; simp
  · simp [h]

include hι in
/--
@isnad1 id=surjecti.1h5v.s8.19bb1146688f from=translated src=- shape=a4adfc2f vocab=bb3584d1
-/
theorem εM_surjective : Function.Surjective (εM ι R) := by
  obtain ⟨y, hy⟩ := R.ε_surj 1
  intro x
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨a, rfl⟩ := hf; obtain ⟨b, rfl⟩ := hg
    exact ⟨a + b, map_add _ _ _⟩
  | single q n =>
    refine ⟨n • (MonoidAlgebra.single q.out (1 : ℤ) • ρV ι y), ?_⟩
    rw [map_zsmul, εM_out_smul ι hι, hy]
    simp

end TheoremA
