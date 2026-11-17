import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul

set_option autoImplicit false

namespace OrdLat
namespace Corner

open IharaLemma

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)
variable {M : Type} [AddCommGroup M] [Module B M]

noncomputable def cornerRestrict (f : M →ₗ[B] M) :
    ↥(cornerSubmodule (M := M) (S.e i)) →ₗ[S.CornerRing i] ↥(cornerSubmodule (M := M) (S.e i)) where
  toFun x := ⟨f (x : M), by
    refine ⟨f (x : M), ?_⟩
    show S.e i • f (x : M) = f (x : M)
    rw [← map_smul, S.e_smul_coe]⟩
  map_add' x y := Subtype.ext (by
    show f ((x : M) + (y : M)) = f (x : M) + f (y : M)
    exact map_add f _ _)
  map_smul' z x := Subtype.ext (by
    show f ((z : B) • (x : M)) = (z : B) • f (x : M)
    exact map_smul f _ _)

theorem cornerBasis_linearIndependent {ι : Type} (b : Module.Basis ι B M) :
    LinearIndependent (S.CornerRing i) (fun k => toCorner (M := M) (S.e i) (b k)) := by
  rw [linearIndependent_iff']
  intro s g hg k hk
  have h0 : ∑ k ∈ s, (g k : B) • b k = 0 := by
    have := congrArg Subtype.val hg
    rw [Submodule.coe_sum, Submodule.coe_zero] at this
    simpa only [IdempotentSplitting.coe_cornerSmul, toCorner_apply, smul_smul,
      IdempotentSplitting.coe_mul_e] using this
  have := linearIndependent_iff'.mp b.linearIndependent s (fun k => (g k : B)) h0 k hk
  exact IdempotentSplitting.ext_cornerRing S i this

theorem cornerBasis_span {ι : Type} (b : Module.Basis ι B M) :
    ⊤ ≤ Submodule.span (S.CornerRing i) (Set.range fun k => toCorner (M := M) (S.e i) (b k)) := by
  rintro x -
  have hsum : ∑ k ∈ (b.repr (x : M)).support, b.repr (x : M) k • b k = (x : M) := by
    have := b.linearCombination_repr (x : M)
    rwa [Finsupp.linearCombination_apply] at this
  have hx : x = ∑ k ∈ (b.repr (x : M)).support,
      (S.toCornerRing i (b.repr (x : M) k)) • toCorner (M := M) (S.e i) (b k) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [IdempotentSplitting.coe_cornerSmul, toCorner_apply,
      IdempotentSplitting.coe_toCornerRing, smul_smul]
    have he : ∀ k, S.e i * (b.repr (x : M) k) * S.e i * S.e i = S.e i * b.repr (x : M) k := by
      intro k
      rw [mul_assoc, (S.idem i).eq, mul_assoc, mul_comm _ (S.e i), ← mul_assoc, (S.idem i).eq]
    simp only [he, ← smul_smul, ← Finset.smul_sum]
    rw [hsum, S.e_smul_coe]
  rw [hx]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

noncomputable def cornerBasis {ι : Type} (b : Module.Basis ι B M) :
    Module.Basis ι (S.CornerRing i) ↥(cornerSubmodule (M := M) (S.e i)) :=
  Module.Basis.mk (cornerBasis_linearIndependent S i b) (cornerBasis_span S i b)

theorem coe_cornerBasis {ι : Type} (b : Module.Basis ι B M) (k : ι) :
    ((cornerBasis S i b k : cornerSubmodule (M := M) (S.e i)) : M) = S.e i • b k := by
  unfold cornerBasis
  rw [Module.Basis.mk_apply]
  rfl

end OrdLat.Corner

theorem solution
    {B : Type} [CommRing B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    {M : Type} [AddCommGroup M] [Module B M] {ι : Type} (b : Module.Basis ι B M) :
    ∃ bj : Module.Basis ι (S.CornerRing i) ↥(IharaLemma.cornerSubmodule (M := M) (S.e i)),
      ∀ k : ι, ((bj k : IharaLemma.cornerSubmodule (M := M) (S.e i)) : M) = S.e i • b k :=
  ⟨OrdLat.Corner.cornerBasis S i b, OrdLat.Corner.coe_cornerBasis S i b⟩
