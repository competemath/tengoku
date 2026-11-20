/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.KernelRank
import Tengoku.Srg266NonexistenceLean.SRG266.Mod11Rank
import Tengoku.Seed.LinearAlgebra.FreeModule.ModN
import Tengoku.Seed.LinearAlgebra.FreeModule.PID

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def integralKernelReductionAddHom (x : V) :
    integralGramKernel G x →+
      (SecondSubconstituent G x → ZMod 11) where
  toFun z := fun B => z.1 B
  map_zero' := by
    funext B
    simp
  map_add' z w := by
    funext B
    simp

/--
@isnad1 id=eq.0h4v.s12.ec2a63742e7d from=translated src=- shape=e8d1b3c3 vocab=cfe0a4ef
-/
theorem eleven_nsmul_integralKernelReductionAddHom
    (x : V) (z : integralGramKernel G x) :
    11 • integralKernelReductionAddHom G x z = 0 := by
  ext B
  change 11 • (z.1 B : ZMod 11) = 0
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 11)]
  have h11 : ((11 : ℕ) : ZMod 11) = 0 := ZMod.natCast_self 11
  rw [h11, zero_smul]

noncomputable def integralKernelReduction (x : V) :
    ModN (integralGramKernel G x) 11 →ₗ[ZMod 11]
      (SecondSubconstituent G x → ZMod 11) :=
  (ModN.liftEquiv' (G := integralGramKernel G x) (n := 11)).symm
    ⟨integralKernelReductionAddHom G x,
      eleven_nsmul_integralKernelReductionAddHom G x⟩

/--
@isnad1 id=eq.0h4v.s16.7c796e817652 from=translated src=- shape=f9d1e9c2 vocab=ce0867a3
-/
@[simp]
theorem integralKernelReduction_mkQ
    (x : V) (z : integralGramKernel G x) :
    integralKernelReduction G x (ModN.mkQ 11 z) =
      integralKernelReductionAddHom G x z := by
  rfl

/--
@isnad1 id=injectiv.0h3v.s15.1a2fe40f656a from=translated src=- shape=aea6bade vocab=2df0a764
-/
theorem integralKernelReduction_injective (x : V) :
    Function.Injective (integralKernelReduction G x) := by
  apply (injective_iff_map_eq_zero (integralKernelReduction G x)).mpr
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      have hreduce :
          integralKernelReductionAddHom G x z = 0 := by
        change
          integralKernelReduction G x (ModN.mkQ 11 z) = 0 at hq
        simpa using hq
      have hcast :
          ∀ B : SecondSubconstituent G x, (z.1 B : ZMod 11) = 0 := by
        intro B
        exact congrFun hreduce B
      have hdiv :
          ∀ B : SecondSubconstituent G x, ∃ a : ℤ, z.1 B = 11 * a := by
        intro B
        have hdvd :
            (11 : ℤ) ∣ z.1 B :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (z.1 B) 11).mp (hcast B)
        rcases hdvd with ⟨a, ha⟩
        exact ⟨a, by omega⟩
      choose a ha using hdiv
      have hza :
          z.1 = (11 : ℤ) • a := by
        funext B
        simpa [smul_eq_mul] using ha B
      have haKernel :
          a ∈ integralGramKernel G x := by
        rw [integralGramKernel, LinearMap.mem_ker]
        funext B
        have hzKernel :
            localGramMatrix G x *ᵥ z.1 = 0 :=
          LinearMap.mem_ker.mp z.2
        have hzB := congrFun hzKernel B
        change
          ∑ C, localGramMatrix G x B C * a C = 0
        have hmultiple :
            11 * (∑ C, localGramMatrix G x B C * a C) = 0 := by
          calc
            11 * (∑ C, localGramMatrix G x B C * a C) =
                ∑ C, localGramMatrix G x B C * z.1 C := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro C _
              rw [hza]
              simp only [Pi.smul_apply, smul_eq_mul]
              ring
            _ = 0 := by
              simpa [Matrix.mulVec_apply, dotProduct] using hzB
        omega
      let aKernel : integralGramKernel G x := ⟨a, haKernel⟩
      have hzSubtype : z = (11 : ℤ) • aKernel := by
        apply Subtype.ext
        exact hza
      rw [hzSubtype]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨aKernel, rfl⟩

def mod11GramKernel (x : V) :
    Submodule (ZMod 11)
      (SecondSubconstituent G x → ZMod 11) :=
  LinearMap.ker (localGramMatrixMod11 G x).mulVecLin

/--
@isnad1 id=mem.0h4v.s15.5ce2b96ccdc4 from=translated src=- shape=fa7330c5 vocab=596a1acf
-/
theorem integralKernelReduction_mem_mod11GramKernel
    (x : V) (q : ModN (integralGramKernel G x) 11) :
    integralKernelReduction G x q ∈ mod11GramKernel G x := by
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      change
        integralKernelReduction G x (ModN.mkQ 11 z) ∈
          mod11GramKernel G x
      rw [integralKernelReduction_mkQ]
      rw [mod11GramKernel, LinearMap.mem_ker]
      funext B
      have hz :
          localGramMatrix G x *ᵥ z.1 = 0 :=
        LinearMap.mem_ker.mp z.2
      have hzB := congrFun hz B
      change
        ∑ C,
          (localGramMatrix G x B C : ZMod 11) * (z.1 C : ZMod 11) = 0
      have hcast :
          (∑ C,
              (localGramMatrix G x B C : ZMod 11) * (z.1 C : ZMod 11)) =
            ((∑ C, localGramMatrix G x B C * z.1 C : ℤ) : ZMod 11) := by
        norm_cast
      rw [hcast]
      have :
          ∑ C, localGramMatrix G x B C * z.1 C = 0 := by
        simpa [Matrix.mulVec_apply, dotProduct] using hzB
      rw [this]
      norm_num

noncomputable def integralKernelReductionToKernel (x : V) :
    ModN (integralGramKernel G x) 11 →ₗ[ZMod 11]
      mod11GramKernel G x :=
  (integralKernelReduction G x).codRestrict
    (mod11GramKernel G x)
    (integralKernelReduction_mem_mod11GramKernel G x)

/--
@isnad1 id=injectiv.0h3v.s15.63568ae84767 from=translated src=- shape=267e5aaa vocab=0ede277a
-/
theorem integralKernelReductionToKernel_injective (x : V) :
    Function.Injective (integralKernelReductionToKernel G x) := by
  intro q r hqr
  apply integralKernelReduction_injective G x
  exact congrArg Subtype.val hqr

/--
@isnad1 id=eq.0h3v.s14.17ad518ee8c8 from=translated src=- shape=4d1ec8f7 vocab=9352624c
-/
theorem finrank_modN_integralGramKernel (x : V) :
    Module.finrank (ZMod 11) (ModN (integralGramKernel G x) 11) =
      Module.finrank ℤ (integralGramKernel G x) := by
  let b := Module.Free.chooseBasis ℤ (integralGramKernel G x)
  calc
    Module.finrank (ZMod 11) (ModN (integralGramKernel G x) 11) =
        Fintype.card (Module.Free.ChooseBasisIndex ℤ
          (integralGramKernel G x)) :=
      Module.finrank_eq_card_basis (ModN.basis b)
    _ = Module.finrank ℤ (integralGramKernel G x) :=
      (Module.finrank_eq_card_basis b).symm

/--
@isnad1 id=le.2h3v.s9.215b45d70901 from=translated src=- shape=dff26cae vocab=3095395d
-/
theorem localGramMatrixMod11_rank_le_twelve_of_integralKernel_finrank
    (hG : IsHypothetical G) (x : V)
    (hkernel : Module.finrank ℤ (integralGramKernel G x) = 208) :
    (localGramMatrixMod11 G x).rank ≤ 12 := by
  have hinj := integralKernelReductionToKernel_injective G x
  have hdimle :
      Module.finrank (ZMod 11)
          (ModN (integralGramKernel G x) 11) ≤
        Module.finrank (ZMod 11) (mod11GramKernel G x) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_modN_integralGramKernel G x, hkernel] at hdimle
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (localGramMatrixMod11 G x).mulVecLin
  rw [Module.finrank_pi] at hnull
  change
    (localGramMatrixMod11 G x).rank +
        Module.finrank (ZMod 11) (mod11GramKernel G x) =
      Fintype.card (SecondSubconstituent G x) at hnull
  rw [secondSubconstituent_card G hG x] at hnull
  omega

/--
@isnad1 id=surjecti.2h3v.s15.6d611ada416a from=translated src=- shape=04746e57 vocab=e8fa5c0e
-/
theorem integralKernelReductionToKernel_surjective
    (hG : IsHypothetical G) (x : V)
    (hkernel : Module.finrank ℤ (integralGramKernel G x) = 208) :
    Function.Surjective (integralKernelReductionToKernel G x) := by
  have hupper :=
    localGramMatrixMod11_rank_le_twelve_of_integralKernel_finrank
      G hG x hkernel
  have hrank :=
    localGramMatrixMod11_rank_eq_twelve_of_rank_le_twelve
      G hG x hupper
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (localGramMatrixMod11 G x).mulVecLin
  rw [Module.finrank_pi] at hnull
  change
    (localGramMatrixMod11 G x).rank +
        Module.finrank (ZMod 11) (mod11GramKernel G x) =
      Fintype.card (SecondSubconstituent G x) at hnull
  rw [hrank, secondSubconstituent_card G hG x] at hnull
  have hdim :
      Module.finrank (ZMod 11)
          (ModN (integralGramKernel G x) 11) =
        Module.finrank (ZMod 11) (mod11GramKernel G x) := by
    rw [finrank_modN_integralGramKernel G x, hkernel]
    omega
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (integralKernelReductionToKernel_injective G x)

/--
@isnad1 id=hasmod11.2h3v.s9.97492f68f18c from=translated src=- shape=32cb62f7 vocab=fead712c
-/
theorem hasMod11KernelLift_of_integralKernel_finrank
    (hG : IsHypothetical G) (x : V)
    (hkernel : Module.finrank ℤ (integralGramKernel G x) = 208) :
    HasMod11KernelLift G x := by
  have hone :
      (1 : SecondSubconstituent G x → ZMod 11) ∈
        mod11GramKernel G x := by
    rw [mod11GramKernel, LinearMap.mem_ker]
    exact localGramMatrixMod11_mulVec_one G hG x
  obtain ⟨q, hq⟩ :=
    integralKernelReductionToKernel_surjective G hG x hkernel
      ⟨1, hone⟩
  obtain ⟨z, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (LinearMap.range
        (LinearMap.lsmul ℤ (integralGramKernel G x) 11)) q
  refine ⟨z.1, ?_, ?_⟩
  · rw [← integralGramKernel_eq_relations G x]
    exact z.2
  · intro B
    have hcast :
        (z.1 B : ZMod 11) = 1 := by
      have := congrArg (fun w => w.1 B) hq
      change
        ((integralKernelReduction G x (ModN.mkQ 11 z)) B) = 1 at this
      rw [integralKernelReduction_mkQ] at this
      exact this
    have hzero : ((1 - z.1 B : ℤ) : ZMod 11) = 0 := by
      push_cast
      rw [hcast]
      ring
    have hdvd :
        (11 : ℤ) ∣ 1 - z.1 B :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (1 - z.1 B) 11).mp hzero
    rcases hdvd with ⟨a, ha⟩
    exact ⟨a, by omega⟩

/--
@isnad1 id=le.1h3v.s6.74cc702bba1f from=translated src=- shape=1dda14e9 vocab=099013b6
-/
theorem localGramMatrixMod11_rank_le_twelve
    (hG : IsHypothetical G) (x : V) :
    (localGramMatrixMod11 G x).rank ≤ 12 :=
  localGramMatrixMod11_rank_le_twelve_of_integralKernel_finrank
    G hG x (integralGramKernel_finrank G hG x)

/--
@isnad1 id=eq.1h3v.s6.5b3ee0f48b0c from=translated src=- shape=1dda14e9 vocab=a4ec3274
-/
theorem localGramMatrixMod11_rank
    (hG : IsHypothetical G) (x : V) :
    (localGramMatrixMod11 G x).rank = 12 :=
  localGramMatrixMod11_rank_eq_twelve_of_rank_le_twelve
    G hG x (localGramMatrixMod11_rank_le_twelve G hG x)

/--
@isnad1 id=hasmod11.1h3v.s5.a71bf6ecb0de from=translated src=- shape=659c14ca vocab=8eed91ec
-/
theorem hasMod11KernelLift
    (hG : IsHypothetical G) (x : V) :
    HasMod11KernelLift G x :=
  hasMod11KernelLift_of_integralKernel_finrank
    G hG x (integralGramKernel_finrank G hG x)

/--
@isnad1 id=ex.1h3v.s7.126001fd1f25 from=translated src=- shape=249a3c23 vocab=e8a50694
-/
theorem exists_integral_centroid
    (hG : IsHypothetical G) (x : V) :
    ∃ c : IntegralGramLattice G x,
      (11 : ℤ) • c = integralGramGeneratorSum G x :=
  exists_integral_centroid_of_mod11KernelLift
    G x (hasMod11KernelLift G hG x)

end SRG266
