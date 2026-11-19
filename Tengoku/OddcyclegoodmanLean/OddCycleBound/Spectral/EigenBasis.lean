import Tengoku.OddcyclegoodmanLean.OddCycleBound.Necklace
import Tengoku.OddcyclegoodmanLean.OddCycleBound.Spectral.CompactGraphonOperator
import Tengoku.OddcyclegoodmanLean.OddCycleBound.Spectral.GraphonL2Operator
import Tengoku.Seed.Analysis.InnerProductSpace.Rayleigh
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound
namespace Spectral
namespace InfiniteSpectral

universe u

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable {W : Omega -> Omega -> Real}

/--
@isnad1 id=eq.1h6v.s9.41beeb981bf5 from=translated src=- shape=119f8fed vocab=36af0870
-/
theorem inner_eq_zero_of_forall_hilbertBasis_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {U : Submodule Real E} [CompleteSpace U]
    (b : HilbertBasis ι Real U) {x : E}
    (hbasis : ∀ i : ι, inner Real ((b i : U) : E) x = 0) :
    ∀ y : U, inner Real ((y : U) : E) x = 0 := by
  intro y
  let p : U := U.orthogonalProjectionOnto x
  have hbasis_proj : ∀ i : ι, inner Real (b i) p = 0 := by
    intro i
    simpa [p] using hbasis i
  have hseries :
      HasSum (fun _i : ι => (0 : Real)) (inner Real y p) := by
    refine (b.hasSum_inner_mul_inner y p).congr_fun ?_
    intro i
    simp [hbasis_proj i]
  have hinner_proj : inner Real y p = 0 := by
    have htsum := hseries.tsum_eq
    simpa using htsum.symm
  simpa [p] using hinner_proj

/--
@isnad1 id=eq.0h5v.s10.e23786901748 from=translated src=- shape=9c0b3ecd vocab=f07819d4
-/
theorem orthogonal_span_sigma_hilbertBasis_eq_iSup_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {α : ι -> Type*}
    (U : ι -> Submodule Real E) [∀ i, CompleteSpace (U i)]
    (b : ∀ i, HilbertBasis (α i) Real (U i)) :
    (Submodule.span Real
      (Set.range fun a : Sigma α => ((b a.1 a.2 : U a.1) : E)))ᗮ =
      (⨆ i, U i)ᗮ := by
  let M : Submodule Real E :=
    Submodule.span Real
      (Set.range fun a : Sigma α => ((b a.1 a.2 : U a.1) : E))
  let S : Submodule Real E := ⨆ i, U i
  have hMS : M ≤ S := by
    change
      Submodule.span Real
        (Set.range fun a : Sigma α => ((b a.1 a.2 : U a.1) : E)) ≤
        ⨆ i, U i
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (le_iSup U a.1) (b a.1 a.2).property
  apply le_antisymm
  · intro x hxM
    rw [Submodule.mem_orthogonal] at hxM ⊢
    intro y hy
    refine Submodule.iSup_induction' U
      (motive := fun y _hy => inner Real y x = 0) ?mem ?zero ?add hy
    · intro i y hyi
      exact
        inner_eq_zero_of_forall_hilbertBasis_inner_eq_zero
          (b i) (x := x) (by
            intro a
            exact hxM ((b i a : U i) : E)
              (Submodule.subset_span ⟨⟨i, a⟩, rfl⟩)) ⟨y, hyi⟩
    · simp
    · intro u v _hu _hv hu hv
      simp [inner_add_left, hu, hv]
  · exact Submodule.orthogonal_le hMS

/--
@isnad1 id=eq.1h4v.s11.073fa9e4922c from=translated src=- shape=e7dce4df vocab=40c7ca5f
-/
theorem submodule_span_orthogonal_eq_bot_of_ambient_orthogonal_inf_eq_bot
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {U : Submodule Real E} (v : ι -> U)
    (h :
      ((Submodule.span Real (Set.range fun i : ι => ((v i : U) : E)))ᗮ ⊓ U) =
        ⊥) :
    (Submodule.span Real (Set.range v))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  let A : Submodule Real E :=
    Submodule.span Real (Set.range fun i : ι => ((v i : U) : E))
  have hxA : (x : E) ∈ Aᗮ := by
    change (x : E) ∈
      (Submodule.span Real (Set.range fun i : ι => ((v i : U) : E)))ᗮ
    rw [Submodule.mem_orthogonal]
    intro y hy
    refine Submodule.span_induction
      (s := Set.range fun i : ι => ((v i : U) : E))
      ?gen ?zero ?add ?smul hy
    · rintro z ⟨i, rfl⟩
      have hx' :=
        (Submodule.mem_orthogonal (Submodule.span Real (Set.range v)) x).1
          hx (v i) (Submodule.subset_span ⟨i, rfl⟩)
      simpa using hx'
    · simp
    · intro y z hy hz hiy hiz
      simp [inner_add_left, hiy, hiz]
    · intro a y hy hiy
      simp [inner_smul_left, hiy]
  have hxinf : (x : E) ∈ Aᗮ ⊓ U := ⟨hxA, x.property⟩
  have hxbot : (x : E) ∈ (⊥ : Submodule Real E) := by
    simpa [A, h] using hxinf
  ext
  simpa using hxbot

/--
@isnad1 id=eq.2h4v.s13.285078d3a3a3 from=translated src=- shape=47b0e55b vocab=9957f474
-/
theorem compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_dense_in_zero_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E]
    (T : E →L[Real] E)
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    {α : {lambda : Real // lambda ≠ 0} -> Type*}
    (b : ∀ lambda : {lambda : Real // lambda ≠ 0},
      HilbertBasis (α lambda) Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1)) :
    (Submodule.span Real
      (Set.range fun a : Sigma α =>
        (⟨((b a.1 a.2 :
            Module.End.eigenspace (T : Module.End Real E) a.1.1) : E),
          by
            rw [Submodule.mem_orthogonal]
            intro y hy
            have horth :
                Module.End.eigenspace (T : Module.End Real E) a.1.1 ⟂
                  Module.End.eigenspace (T : Module.End Real E) 0 :=
              (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
                (T := (T : Module.End Real E)) hsymm).isOrtho a.1.2
            exact horth.symm.inner_eq hy (b a.1 a.2).property⟩ :
          (Module.End.eigenspace (T : Module.End Real E) 0)ᗮ)))ᗮ = ⊥ := by
  let Z : Submodule Real E :=
    (Module.End.eigenspace (T : Module.End Real E) 0)ᗮ
  let v : Sigma α -> Z := fun a =>
    ⟨((b a.1 a.2 :
        Module.End.eigenspace (T : Module.End Real E) a.1.1) : E),
      by
        rw [Submodule.mem_orthogonal]
        intro y hy
        have horth :
            Module.End.eigenspace (T : Module.End Real E) a.1.1 ⟂
              Module.End.eigenspace (T : Module.End Real E) 0 :=
          (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
            (T := (T : Module.End Real E)) hsymm).isOrtho a.1.2
        exact horth.symm.inner_eq hy (b a.1 a.2).property⟩
  change (Submodule.span Real (Set.range v))ᗮ = ⊥
  refine submodule_span_orthogonal_eq_bot_of_ambient_orthogonal_inf_eq_bot
    v ?_
  have hspan :
      (Submodule.span Real
        (Set.range fun a : Sigma α =>
          ((b a.1 a.2 :
            Module.End.eigenspace (T : Module.End Real E) a.1.1) : E)))ᗮ =
        (⨆ lambda : {lambda : Real // lambda ≠ 0},
          Module.End.eigenspace (T : Module.End Real E) lambda.1)ᗮ :=
    orthogonal_span_sigma_hilbertBasis_eq_iSup_orthogonal
      (fun lambda : {lambda : Real // lambda ≠ 0} =>
        Module.End.eigenspace (T : Module.End Real E) lambda.1)
      b
  have hdense :
      ((⨆ lambda : {lambda : Real // lambda ≠ 0},
          Module.End.eigenspace (T : Module.End Real E) lambda.1)ᗮ ⊓ Z) =
        ⊥ := by
    simpa [Z] using
      CompactSpectral.compactSelfAdjoint_nonzero_iSup_orthogonal_inf_zero_eigenspace_orthogonal_eq_bot
        (T := T) hcompact hsymm
  simpa [v, Z, hspan] using hdense

/--
@isnad1 id=orthonor.1h4v.s11.78e5923ba4e9 from=translated src=- shape=d12dba3f vocab=d3e98def
-/
theorem compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E)
    (hsymm : T.IsSymmetric)
    {α : {lambda : Real // lambda ≠ 0} -> Type*}
    (b : ∀ lambda : {lambda : Real // lambda ≠ 0},
      HilbertBasis (α lambda) Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1)) :
    Orthonormal Real
      (fun a : Sigma α =>
        ((b a.1 a.2 :
          Module.End.eigenspace (T : Module.End Real E) a.1.1) : E)) := by
  exact
    ((LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : Module.End Real E)) hsymm).comp
        Subtype.coe_injective).orthonormal_sigma_orthonormal
      (fun lambda => (b lambda).orthonormal)

/--
@isnad1 id=countabl.2h2v.s9.804600950adf from=translated src=- shape=2e420b49 vocab=d24db943
-/
theorem compactSelfAdjoint_countable_nonzero_eigenspace_finIndex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E]
    (T : E →L[Real] E)
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Countable
      (Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace (T : Module.End Real E) lambda.1))) := by
  let eigs : Set Real :=
    {lambda : Real |
      Module.End.HasEigenvalue (T : Module.End Real E) lambda ∧ lambda ≠ 0}
  have hcount_eigs : eigs.Countable := by
    simpa [eigs] using
      CompactSpectral.compactSelfAdjoint_countable_nonzero_eigenvalues
        (T := T) hcompact hsymm
  let F :
      (Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
        Fin (Module.finrank Real
          (Module.End.eigenspace (T : Module.End Real E) lambda.1))) ->
        eigs × Nat :=
    fun a =>
      (⟨a.1.1,
        by
          have hfinpos :
              0 < Module.finrank Real
                (Module.End.eigenspace (T : Module.End Real E) a.1.1) :=
            Nat.pos_of_ne_zero (by
              intro hzero
              have hlt := a.2.2
              omega)
          have hnebot :
              Module.End.eigenspace (T : Module.End Real E) a.1.1 ≠ ⊥ := by
            intro hbot
            have hfinzero :
                Module.finrank Real
                  (Module.End.eigenspace (T : Module.End Real E) a.1.1) = 0 := by
              rw [hbot, finrank_bot]
            omega
          exact ⟨Module.End.hasEigenvalue_iff.mpr hnebot, a.1.2⟩⟩,
        a.2.1)
  have hF_inj : Function.Injective F := by
    intro a b hab
    cases a with
    | mk lambda i =>
      cases b with
      | mk nu j =>
        simp [F] at hab
        rcases hab with ⟨hlambda, hidx⟩
        have hsub : lambda = nu := Subtype.ext hlambda
        cases hsub
        congr
        exact Fin.ext hidx
  haveI : Countable eigs := hcount_eigs.to_subtype
  exact hF_inj.countable

/--
@isnad1 id=summable.1h4v.s6.9619f5030d59 from=translated src=- shape=3a492099 vocab=dbda3f6b
-/
theorem summable_inner_sq_of_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {mode : ι -> E} (hmode : Orthonormal Real mode) (f : E) :
    Summable fun n : ι => inner Real f (mode n) ^ 2 := by
  simpa [real_inner_comm, Real.norm_eq_abs, sq_abs] using
    hmode.inner_products_summable f

/--
@isnad1 id=le.1h4v.s6.4f98b0daf3bd from=translated src=- shape=90e3a4e8 vocab=eb0f8084
-/
theorem tsum_inner_sq_le_self_of_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {mode : ι -> E} (hmode : Orthonormal Real mode) (f : E) :
    (∑' n : ι, inner Real f (mode n) ^ 2) <= inner Real f f := by
  simpa [real_inner_comm, Real.norm_eq_abs, sq_abs, real_inner_self_eq_norm_sq] using
    hmode.tsum_inner_products_le f

/--
@isnad1 id=le.1h5v.s6.4c342deafb6e from=translated src=- shape=a252dad5 vocab=12c8c03b
-/
theorem sum_inner_sq_le_self_of_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {ι : Type*} {mode : ι -> E} (hmode : Orthonormal Real mode) (f : E)
    (s : Finset ι) :
    s.sum (fun n : ι => inner Real f (mode n) ^ 2) <= inner Real f f := by
  have hsumm : Summable fun n : ι => inner Real f (mode n) ^ 2 :=
    summable_inner_sq_of_orthonormal hmode f
  have hsum_le :
      s.sum (fun n : ι => inner Real f (mode n) ^ 2) <=
        ∑' n : ι, inner Real f (mode n) ^ 2 := by
    exact hsumm.sum_le_tsum s (fun n _hn => sq_nonneg _)
  exact hsum_le.trans (tsum_inner_sq_le_self_of_orthonormal hmode f)

noncomputable def opIter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (T : E →L[Real] E) : Nat -> E -> E
  | 0, f => f
  | n + 1, f => T (opIter T n f)

/--
@isnad1 id=eq.0h5v.s11.a022eb4f477f from=translated src=- shape=a1434f9b vocab=acec715e
-/
theorem opIter_eq_l2_clmIter
    (T : Lp Real 2 mu →L[Real] Lp Real 2 mu) :
    ∀ n f, opIter T n f = L2Kernel.clmIter (mu := mu) T n f := by
  intro n
  induction n with
  | zero =>
      intro f
      rfl
  | succ n ih =>
      intro f
      change T (opIter T n f) =
        T (L2Kernel.clmIter (mu := mu) T n f)
      rw [ih f]

def HasGoodRepresentative [IsProbabilityMeasure mu] (v : Lp Real 2 mu) : Prop :=
  ∃ (f : Omega -> Real), ∃ hf : Good f, v = L2Kernel.goodL2 (mu := mu) hf

/--
@isnad1 id=hasgoodr.2h5v.s11.1fcdbc41d90c from=translated src=- shape=cf9532a9 vocab=25227ee9
-/
theorem hasGoodRepresentative_of_eq_smul_goodL2
    [IsProbabilityMeasure mu]
    {v : Lp Real 2 mu} {c : Real} {f : Omega -> Real} (hf : Good f)
    (hv : v = c • L2Kernel.goodL2 (mu := mu) hf) :
    HasGoodRepresentative (mu := mu) v := by
  refine ⟨c • f, good_smul c hf, ?_⟩
  rw [hv, L2Kernel.goodL2_smul]

/--
@isnad1 id=hasgoodr.4h6v.s14.7539211e40cc from=translated src=- shape=366de1dc vocab=b547593f
-/
theorem hasGoodRepresentative_of_nonzero_eigenmode_and_good_operator_image
    [IsProbabilityMeasure mu]
    {T : Lp Real 2 mu →L[Real] Lp Real 2 mu}
    {mode : Lp Real 2 mu} {lambda : Real}
    {g : Omega -> Real} (hg : Good g)
    (himage : T mode = L2Kernel.goodL2 (mu := mu) hg)
    (hdiag : T mode = lambda • mode)
    (hlambda : lambda ≠ 0) :
    HasGoodRepresentative (mu := mu) mode := by
  refine hasGoodRepresentative_of_eq_smul_goodL2
    (mu := mu) (c := lambda⁻¹) hg ?_
  calc
    mode = (lambda⁻¹ * lambda) • mode := by
      rw [inv_mul_cancel₀ hlambda, one_smul]
    _ = lambda⁻¹ • (lambda • mode) := by
      rw [smul_smul]
    _ = lambda⁻¹ • L2Kernel.goodL2 (mu := mu) hg := by
      rw [← hdiag, himage]

end InfiniteSpectral
end Spectral
end OddCycleBound
