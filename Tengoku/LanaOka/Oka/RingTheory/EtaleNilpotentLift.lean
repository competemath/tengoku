/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.Smooth.StandardSmoothOfFree
import Tengoku.Seed.RingTheory.Extension.Presentation.Submersive
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Tengoku.Seed.RingTheory.Polynomial.Basic
import Tengoku.Seed.Algebra.Polynomial.Lifts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting finite étale algebras along nil thickenings

Let `π : A →+* A₀` be surjective with kernel contained in the nilradical. Every finite étale
`A₀`-algebra `B₀` lifts to a finite étale `A`-algebra `B`: there is a surjection `φ : B →+* B₀`
over `π` whose kernel is contained in the nilradical of `B`.

The lift is obtained from a global submersive presentation `B₀ = A₀[x₁, …, xₙ] ⧸ (f₁, …, fₙ)`
(`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`) by lifting the relations to `A`:
the Jacobian of the lifted relations maps to the Jacobian of the `fⱼ`, hence is a unit. Finiteness
follows because every element of `B` is integral over `A` modulo a nil ideal.

## Main results

- `Algebra.Etale.exists_lift_of_ker_le_nilradical`: the lifting statement.
-/

universe u

open MvPolynomial

namespace Algebra.Etale

/-- A surjective ring homomorphism with kernel contained in the nilradical reflects units. -/
lemma _root_.RingHom.isUnit_of_isUnit_of_ker_le_nilradical {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical R)
    {x : R} (hx : IsUnit (f x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := hf ↑hx.unit⁻¹
  have hn : IsNilpotent (x * y - 1) := hker <| by simp [RingHom.mem_ker, hy]
  have h : IsUnit (x * y) := by simpa using hn.isUnit_add_one
  exact isUnit_of_mul_isUnit_left h

variable {A A₀ B₀ : Type u} [CommRing A] [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]

/-- **Finite étale algebras lift along nil thickenings.** If `π : A →+* A₀` is surjective with
kernel contained in the nilradical, every finite étale `A₀`-algebra `B₀` is the target of a
surjection `φ : B →+* B₀` over `π` from a finite étale `A`-algebra `B`, with kernel contained in
the nilradical of `B`. -/
theorem exists_lift_of_ker_le_nilradical [Algebra.Etale A₀ B₀] [Module.Finite A₀ B₀]
    (π : A →+* A₀) (hπ : Function.Surjective π) (hker : RingHom.ker π ≤ nilradical A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (φ : B →+* B₀),
      Algebra.Etale A B ∧ Module.Finite A B ∧ Function.Surjective φ ∧
        RingHom.ker φ ≤ nilradical B ∧ φ.comp (algebraMap A B) = (algebraMap A₀ B₀).comp π := by
  classical
  obtain ⟨ι, σ, _, _, P₀, hdim⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›).out
  have : Fintype σ := Fintype.ofFinite σ
  choose F hF using fun j ↦ MvPolynomial.map_surjective π hπ (P₀.relation j)
  let B := MvPolynomial ι A ⧸ Ideal.span (Set.range F)
  let ψ : MvPolynomial ι A →+* B₀ := (aeval P₀.val).toRingHom.comp (MvPolynomial.map π)
  have hψF : Ideal.span (Set.range F) ≤ RingHom.ker ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp [ψ, hF]
  let φ : B →+* B₀ := Ideal.Quotient.lift _ ψ hψF
  have hφ (x) : φ (Ideal.Quotient.mk _ x) = ψ x := rfl
  have hψ : Function.Surjective ψ :=
    P₀.aeval_val_surjective.comp (MvPolynomial.map_surjective π hπ)
  have hφs : Function.Surjective φ := Ideal.Quotient.lift_surjective_of_surjective _ _ hψ
  have hφker : RingHom.ker φ ≤ nilradical B := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy : MvPolynomial.map π y ∈
        Ideal.map (MvPolynomial.map π) (Ideal.span (Set.range F)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      simp only [Function.comp_def, hF]
      rw [P₀.span_range_relation_eq_ker, P₀.ker_eq_ker_aeval_val, RingHom.mem_ker]
      exact hx
    obtain ⟨z, hz, hzy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective π hπ)).mp hy
    have hyz : y - z ∈ nilradical (MvPolynomial ι A) := by
      have : y - z ∈ Ideal.map (C : A →+* MvPolynomial ι A) (RingHom.ker π) := by
        rw [← MvPolynomial.ker_map, RingHom.mem_ker, map_sub, hzy, sub_self]
      refine Ideal.map_le_iff_le_comap.mpr (fun a ha ↦ ?_) this
      exact mem_nilradical.mpr ((mem_nilradical.mp (hker ha)).map C)
    have : Ideal.Quotient.mk (Ideal.span (Set.range F)) y =
        Ideal.Quotient.mk _ (y - z) := by
      rw [map_sub, (Ideal.Quotient.eq_zero_iff_mem).mpr hz, sub_zero]
    rw [this]
    exact IsNilpotent.map hyz _
  have hcomp : φ.comp (algebraMap A B) = (algebraMap A₀ B₀).comp π := by
    ext a
    change φ (Ideal.Quotient.mk _ (C a)) = _
    simp [hφ, ψ]
  -- the lifted presentation
  let Q : PreSubmersivePresentation A B ι σ :=
    PreSubmersivePresentation.naive (v := F) P₀.map P₀.map_inj
  have hQ : IsUnit Q.jacobian := by
    refine φ.isUnit_of_isUnit_of_ker_le_nilradical hφs hφker ?_
    convert P₀.jacobian_isUnit using 1
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    change ψ Q.jacobiMatrix.det = algebraMap P₀.Ring B₀ P₀.jacobiMatrix.det
    rw [P₀.algebraMap_apply]
    change aeval P₀.val (MvPolynomial.map π Q.jacobiMatrix.det) = _
    rw [RingHom.map_det]
    congr 2
    refine Matrix.ext fun i j ↦ ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      PreSubmersivePresentation.jacobiMatrix_apply]
    change MvPolynomial.map π (pderiv (P₀.map i) (F j)) = _
    rw [← pderiv_map, hF]
  let Q' : SubmersivePresentation A B ι σ := ⟨Q, hQ⟩
  have hQdim : Q'.dimension = 0 := hdim
  have hEt : Algebra.Etale A B :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
      (Q'.isStandardSmoothOfRelativeDimension hQdim)
  have hint : Algebra.IsIntegral A B := by
    refine ⟨fun b ↦ ?_⟩
    obtain ⟨p₀, hp₀, hp₀b⟩ := Algebra.IsIntegral.isIntegral (R := A₀) (φ b)
    obtain ⟨p, hpmap, -, hp⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.map_surjective π hπ p₀) hp₀
    have hpb : Polynomial.aeval b p ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp,
        ← Polynomial.eval₂_map, hpmap]
      exact hp₀b
    obtain ⟨k, hk⟩ := hφker hpb
    exact ⟨p ^ k, hp.pow k, by rw [Polynomial.eval₂_pow]; exact hk⟩
  exact ⟨B, inferInstance, inferInstance, φ, hEt, Algebra.IsIntegral.finite, hφs, hφker, hcomp⟩

end Algebra.Etale
