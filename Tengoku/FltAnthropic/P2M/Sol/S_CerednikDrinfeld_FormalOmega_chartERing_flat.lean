import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_FormalOmega_chartERing_flat.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_flat

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega
open Polynomial

noncomputable section

namespace ChartFlat

variable (R : Type) [CommRing R] (π : R)

def g : (R[X])[X] := X ^ 2 + (C (X : R[X]) * X - C (C π))

/--
@isnad1 id=monic.0h2v.s4.ebb88462d4dc from=translated src=- shape=80417741 vocab=e48b4802
-/
theorem g_monic : (g R π).Monic := by
  unfold g
  refine monic_X_pow_add ?_
  refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
  · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast one_lt_two)
  · exact degree_C_le.trans_lt (by exact_mod_cast two_pos)

abbrev B : Type := AdjoinRoot (g R π)

scoped instance : Module.Free R[X] (B R π) := (g_monic R π).free_adjoinRoot

scoped instance : Module.Flat R (B R π) := Module.Flat.trans R R[X] (B R π)

abbrev ξq : edgeQuot R π := edgeQuot.mk R π (MvPolynomial.X 0)
abbrev ηq : edgeQuot R π := edgeQuot.mk R π (MvPolynomial.X 1)

/--
@isnad1 id=eq.0h2v.s7.96f852786b74 from=translated src=- shape=86d81ff1 vocab=bfcacd35
-/
theorem ξq_mul_ηq : ξq R π * ηq R π = algebraMap R (edgeQuot R π) π := by
  have h := edgeQuot.mk_edgeRel R π
  unfold edgeRel at h
  rw [map_sub, map_mul, sub_eq_zero] at h
  rw [h]; exact (edgeQuot.mk R π).commutes π

def gen (i : Fin 2) : B R π := if i = 0 then AdjoinRoot.root (g R π) else AdjoinRoot.root (g R π) + AdjoinRoot.of (g R π) X

/--
@isnad1 id=eq.0h2v.s5.3f854d6c1f91 from=translated src=- shape=d2af95a8 vocab=edee23cb
-/
theorem gen_zero : gen R π 0 = AdjoinRoot.root (g R π) := rfl
/--
@isnad1 id=eq.0h2v.s8.9cfee64891fe from=translated src=- shape=68136dfe vocab=9c673d89
-/
theorem gen_one : gen R π 1 = AdjoinRoot.root (g R π) + AdjoinRoot.of (g R π) X := rfl

/--
@isnad1 id=eq.0h2v.s9.3154ca7b96da from=translated src=- shape=bf04f769 vocab=83bd9821
-/
theorem root_rel : AdjoinRoot.root (g R π) * (AdjoinRoot.root (g R π) + AdjoinRoot.of (g R π) X) =
    algebraMap R (B R π) π := by
  have h : Polynomial.aeval (AdjoinRoot.root (g R π)) (X ^ 2 + (C (X : R[X]) * X - C (C π)) : (R[X])[X]) = 0 :=
    (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  rw [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, aeval_C] at h
  rw [IsScalarTower.algebraMap_apply R R[X] (B R π), algebraMap_eq, ← AdjoinRoot.algebraMap_eq]
  linear_combination h

def φ : edgeQuot R π →ₐ[R] B R π :=
  Ideal.Quotient.liftₐ (Ideal.span {edgeRel R π}) (MvPolynomial.aeval (gen R π))
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul]
      refine mul_eq_zero_of_left ?_ _
      show MvPolynomial.aeval (gen R π) (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = 0
      rw [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_C, gen_zero, gen_one,
        root_rel, sub_self])

/--
@isnad1 id=eq.0h3v.s9.828d8ac5e798 from=translated src=- shape=aa4c2ca3 vocab=adf371ac
-/
theorem φ_mk (p : MvPolynomial (Fin 2) R) : φ R π (edgeQuot.mk R π p) = MvPolynomial.aeval (gen R π) p := rfl

def ψ : B R π →ₐ[R] edgeQuot R π :=
  AdjoinRoot.liftAlgHom (g R π) (Polynomial.aeval (R := R) (ηq R π - ξq R π)) (ξq R π)
    (by
      unfold g
      rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
      simp only [AlgHom.coe_toRingHom, aeval_X, aeval_C]
      rw [← ξq_mul_ηq]; ring)

/--
@isnad1 id=eq.0h2v.s7.bb9325172de8 from=translated src=- shape=3c88ffd8 vocab=0f382f65
-/
theorem ψ_root : ψ R π (AdjoinRoot.root (g R π)) = ξq R π := AdjoinRoot.liftAlgHom_root _ _ _ _

/--
@isnad1 id=eq.0h3v.s9.7705a34489a0 from=translated src=- shape=dcd6afa9 vocab=161252d8
-/
theorem ψ_of (p : R[X]) : ψ R π (AdjoinRoot.of (g R π) p) = Polynomial.aeval (R := R) (ηq R π - ξq R π) p :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ p

/--
@isnad1 id=eq.0h3v.s8.1c8bf3c7e938 from=translated src=- shape=27a2d168 vocab=0e9a9bb5
-/
theorem ψ_φ (x : edgeQuot R π) : ψ R π (φ R π x) = x := by
  suffices h : (ψ R π).comp (φ R π) = AlgHom.id R (edgeQuot R π) from AlgHom.congr_fun h x
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · show ψ R π (φ R π (edgeQuot.mk R π (MvPolynomial.X 0))) = edgeQuot.mk R π (MvPolynomial.X 0)
    rw [φ_mk, MvPolynomial.aeval_X, gen_zero, ψ_root]
  · show ψ R π (φ R π (edgeQuot.mk R π (MvPolynomial.X 1))) = edgeQuot.mk R π (MvPolynomial.X 1)
    rw [φ_mk, MvPolynomial.aeval_X, gen_one, map_add, ψ_root, ψ_of, aeval_X]; ring

/--
@isnad1 id=eq.0h3v.s8.c835d2dc9762 from=translated src=- shape=27a2d168 vocab=0e9a9bb5
-/
theorem φ_ψ (y : B R π) : φ R π (ψ R π y) = y := by
  have hroot : φ R π (ψ R π (AdjoinRoot.root (g R π))) = AdjoinRoot.root (g R π) := by
    rw [ψ_root]; show φ R π (edgeQuot.mk R π (MvPolynomial.X 0)) = _; rw [φ_mk, MvPolynomial.aeval_X, gen_zero]
  have hX : φ R π (ψ R π (AdjoinRoot.of (g R π) X)) = AdjoinRoot.of (g R π) X := by
    rw [ψ_of, aeval_X, map_sub]
    show φ R π (edgeQuot.mk R π (MvPolynomial.X 1)) - φ R π (edgeQuot.mk R π (MvPolynomial.X 0)) = _
    rw [φ_mk, φ_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, gen_zero, gen_one]; ring

  suffices h : ((φ R π).comp (ψ R π)).toRingHom.comp (AdjoinRoot.mk (g R π)) =
      (AlgHom.id R (B R π)).toRingHom.comp (AdjoinRoot.mk (g R π)) by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    exact RingHom.congr_fun h p
  apply Polynomial.ringHom_ext
  · intro p
    show φ R π (ψ R π (AdjoinRoot.mk (g R π) (C p))) = AdjoinRoot.mk (g R π) (C p)
    rw [AdjoinRoot.mk_C]

    suffices h' : ((φ R π).comp (ψ R π)).toRingHom.comp (AdjoinRoot.of (g R π)) = AdjoinRoot.of (g R π) from
      RingHom.congr_fun h' p
    apply Polynomial.ringHom_ext
    · intro r
      show φ R π (ψ R π (AdjoinRoot.of (g R π) (C r))) = AdjoinRoot.of (g R π) (C r)
      rw [← algebraMap_eq, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply R R[X] (B R π),
        AlgHom.commutes, AlgHom.commutes]
    · exact hX
  · show φ R π (ψ R π (AdjoinRoot.mk (g R π) X)) = AdjoinRoot.mk (g R π) X
    rw [AdjoinRoot.mk_X]; exact hroot

def e : edgeQuot R π ≃ₗ[R] B R π :=
  LinearEquiv.ofBijective (φ R π).toLinearMap
    ⟨Function.LeftInverse.injective (g := ψ R π) (ψ_φ R π), Function.RightInverse.surjective (g := ψ R π) (φ_ψ R π)⟩

/--
@isnad1 id=flat.0h2v.s5.2aeb76f15283 from=translated src=- shape=d0042f13 vocab=c428ce24
-/
theorem flat_edgeQuot : Module.Flat R (edgeQuot R π) := Module.Flat.of_linearEquiv (e R π)

end ChartFlat
open scoped _root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_flat.ChartFlat

end
open scoped _root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_flat.ChartFlat

/--
@isnad1 id=flat.0h3v.s8.814e897bfead from=translated src=- shape=19e44a15 vocab=8f25a013
-/
theorem solution
    (R : Type) [CommRing R] (π : R) (q : ℕ) :
    Module.Flat R (chartERing R π q) := by
  have h1 : Module.Flat R (edgeQuot R π) := ChartFlat.flat_edgeQuot R π
  have h2 : Module.Flat (edgeQuot R π) (chartERing R π q) := IsLocalization.flat _ (Submonoid.powers (edgeQuot.discr R π q))
  exact @Module.Flat.trans R (edgeQuot R π) (chartERing R π q) _ _ _ _ _ _ _ h1 h2
