module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Homological.Lifts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `ℤ[E]` is free as a right `ℤ[B]`-module (coset decomposition)

For an injective homomorphism `ι : B → E`, every element of `ℤ[E]` decomposes uniquely along the
left cosets `E / ι(B)`.  We use this to show that induction `ℤ[E] ⊗_{ℤ[B]} –`, written in
coordinates as `indMap`, preserves exactness (the step "induction is exact" in the proof of
Proposition 5.1).
-/

@[expose] public section

namespace TheoremA

universe u

open MonoidAlgebra

variable {B E : Type u} [Group B] [Group E] (ι : B →* E) (hι : Function.Injective ι)

/-- The ring homomorphism `ℤ[B] → ℤ[E]`.-/
noncomputable def ρ : ZG B →+* ZG E := MonoidAlgebra.mapDomainRingHom ℤ ι

/--
@isnad1 id=eq.0h5v.s7.9ecaddc4bfbf from=translated src=- shape=bc9ef0a6 vocab=6168b1db
-/
theorem ρ_single (b : B) (n : ℤ) : ρ ι (MonoidAlgebra.single b n) = MonoidAlgebra.single (ι b) n := by
  simp [ρ, MonoidAlgebra.mapDomainRingHom_apply]

/-- The coset of `e`, in the quotient by `ι(B)`.-/
abbrev cosetOf (e : E) : E ⧸ ι.range := (e : E ⧸ ι.range)

/--
@isnad1 id=mem.0h4v.s6.ad585f9144c2 from=translated src=- shape=0c7e5955 vocab=a5a0530b
-/
theorem out_inv_mul_mem (e : E) : (cosetOf ι e).out⁻¹ * e ∈ ι.range := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range e
  rw [hh, mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem h.2

/-- The element `b_e ∈ B` with `e = out(eB) · ι(b_e)`.-/
noncomputable def bOf (e : E) : B :=
  (MonoidHom.ofInjective hι).symm ⟨_, out_inv_mul_mem ι e⟩

/--
@isnad1 id=eq.1h4v.s7.fdfae61e0b96 from=translated src=- shape=0082f60f vocab=bdc7e5b9
-/
theorem ι_bOf (e : E) : ι (bOf ι hι e) = (cosetOf ι e).out⁻¹ * e := by
  have := (MonoidHom.ofInjective hι).apply_symm_apply ⟨_, out_inv_mul_mem ι e⟩
  exact congrArg Subtype.val this

/--
@isnad1 id=eq.1h4v.s7.f94c1fbf4595 from=translated src=- shape=354d155a vocab=aca7eb9e
-/
theorem out_mul_ι_bOf (e : E) : (cosetOf ι e).out * ι (bOf ι hι e) = e := by
  rw [ι_bOf, mul_inv_cancel_left]

/--
@isnad1 id=eq.0h5v.s7.dcc1ed731f47 from=translated src=- shape=48a8c6d2 vocab=70ed4727
-/
theorem cosetOf_mul_ι (e : E) (b : B) : cosetOf ι (e * ι b) = cosetOf ι e := by
  rw [QuotientGroup.eq]
  simp

/--
@isnad1 id=eq.1h5v.s7.f4d863e3e51b from=translated src=- shape=cdeda5f8 vocab=7ab47b91
-/
theorem bOf_mul_ι (e : E) (b : B) : bOf ι hι (e * ι b) = bOf ι hι e * b := by
  apply hι
  rw [map_mul, ι_bOf, ι_bOf, cosetOf_mul_ι, mul_assoc]

/--
@isnad1 id=eq.1h4v.s7.416569b49af7 from=translated src=- shape=4257d3d9 vocab=0a6b12b6
-/
theorem bOf_out (q : E ⧸ ι.range) : bOf ι hι q.out = 1 := by
  apply hι
  rw [ι_bOf, map_one]
  have : cosetOf ι q.out = q := Quotient.out_eq' q
  rw [this, inv_mul_cancel]

/--
@isnad1 id=eq.0h4v.s6.5a0b4176961d from=translated src=- shape=a630c4ef vocab=d77b8a01
-/
theorem cosetOf_out (q : E ⧸ ι.range) : cosetOf ι q.out = q := Quotient.out_eq' q

/-- The coset decomposition `ℤ[E] → ⊕_{E / ι B} ℤ[B]`.-/
noncomputable def decomp : ZG E →+ ((E ⧸ ι.range) →₀ ZG B) :=
  (Finsupp.liftAddHom fun e =>
    (Finsupp.singleAddHom (cosetOf ι e)).comp
      (MonoidAlgebra.singleAddHom (bOf ι hι e) : ℤ →+ ZG B)).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

/--
@isnad1 id=eq.1h5v.s8.1f8f6ca29d15 from=translated src=- shape=d95cb9f5 vocab=98ae497f
-/
theorem decomp_single (e : E) (n : ℤ) :
    decomp ι hι (MonoidAlgebra.single e n) =
      Finsupp.single (cosetOf ι e) (MonoidAlgebra.single (bOf ι hι e) n) := by
  simp [decomp]

/-- Reassembly `⊕_{E / ι B} ℤ[B] → ℤ[E]`, `(q, l) ↦ out(q) · ι(l)`.-/
noncomputable def assemble : ((E ⧸ ι.range) →₀ ZG B) →+ ZG E :=
  Finsupp.liftAddHom fun q =>
    (AddMonoidHom.mulLeft (MonoidAlgebra.single q.out (1 : ℤ))).comp (ρ ι).toAddMonoidHom

/--
@isnad1 id=eq.0h5v.s9.161c95da4b79 from=translated src=- shape=aa6c334f vocab=0a2b4fae
-/
theorem assemble_single (q : E ⧸ ι.range) (l : ZG B) :
    assemble ι (Finsupp.single q l) = MonoidAlgebra.single q.out 1 * ρ ι l := by
  simp [assemble]

/--
@isnad1 id=eq.1h4v.s9.54b6b2a3a2be from=translated src=- shape=5c582d8a vocab=697b7e65
-/
theorem assemble_decomp (f : ZG E) : assemble ι (decomp ι hι f) = f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single e n =>
    rw [decomp_single, assemble_single]
    simp [ρ_single, MonoidAlgebra.single_mul_single, out_mul_ι_bOf]

/--
@isnad1 id=eq.1h6v.s9.d2afcd19086d from=translated src=- shape=2f5adfc0 vocab=46a4f2fb
-/
theorem decomp_mul_ρ (f : ZG E) (l : ZG B) (q : E ⧸ ι.range) :
    decomp ι hι (f * ρ ι l) q = decomp ι hι f q * l := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_mul, map_add, Finsupp.add_apply, ha, hb, map_add,
      Finsupp.add_apply, add_mul]
  | single e n =>
    induction l using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, mul_add, map_add, Finsupp.add_apply, ha, hb, mul_add]
    | single b m =>
      simp only [ρ_single,
        MonoidAlgebra.single_mul_single, decomp_single, cosetOf_mul_ι, bOf_mul_ι]
      by_cases hq : cosetOf ι e = q
      · subst hq; simp [MonoidAlgebra.single_mul_single]
      · simp [hq]

open scoped Classical in
/--
@isnad1 id=eq.1h6v.s9.65dd783c21dc from=translated src=- shape=09707cdc vocab=d4c03ab8
-/
theorem decomp_out_mul (q q' : E ⧸ ι.range) (l : ZG B) :
    decomp ι hι (MonoidAlgebra.single q'.out 1 * ρ ι l) q = if q' = q then l else 0 := by
  rw [decomp_mul_ρ, decomp_single, bOf_out, cosetOf_out]
  by_cases h : q' = q
  · subst h; simp only [Finsupp.single_eq_same, ite_true]; rw [← MonoidAlgebra.one_def, one_mul]
  · simp [h]

end TheoremA
