import Tengoku.TdaLib.TDA.Persistence.FiniteHookDeflationExamples
import Tengoku.TdaLib.TDA.Persistence.FiniteRankProjectiveResolutionKan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples for finite-presentable rank-projective resolutions

The main theorem consumes only finite presentation. A principal upset is a
nonzero free, hence finitely presented, module and provides a direct downstream
application of that interface.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveResolutionKanExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence
open TDA.Persistence.FiniteRankProjectiveResolution
open TDA.Persistence.FiniteHookDeflation.Examples
open scoped ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

/-- A nonzero principal-upset free module has a finite rank-projective
resolution by the finite-presentation existence theorem.
@isnad1 id=nonempty.1h3v.s6.67474a0fccd6 from=translated src=- shape=5ef6e37f vocab=16213c8e
-/
theorem principalUpset_has_finiteRankProjectiveResolution
    (hn : 0 < n) (a : Fin n → ℝ) :
    Nonempty (FiniteRankProjectiveResolution
      (HookInfinity.module (R := k) a)) := by
  apply FiniteRankProjectiveResolution.finitelyPresented_exists_finiteRankProjectiveResolution
    hn
  exact GradedFree.free_finitelyPresented (R := k) (P := Fin n → ℝ)
    (HookInfinity.generators (P := Fin n → ℝ) a)

/-- The nonzero principal-upset free module has a finite resolution whose
actual quotient rows all satisfy the transferred projective-cover certificate.
@isnad1 id=and.1h3v.s10.8706260787fb from=translated src=- shape=8a231787 vocab=7e497272
-/
theorem principalUpset_has_minimalFiniteRankProjectiveResolution
    (hn : 0 < n) (a : Fin n → ℝ) :
    (∃ R : MinimalFiniteRankProjectiveResolution (k := k)
        (M := HookInfinity.module (R := k) a),
      ∀ i, IsRankProjectiveCover (R.resolution.quotient i)) ∧
      ∃ x : (HookInfinity.module (R := k) a).obj a, x ≠ 0 := by
  constructor
  · obtain ⟨R⟩ :=
      FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
        hn (HookInfinity.module (R := k) a)
        (GradedFree.free_finitelyPresented (R := k) (P := Fin n → ℝ)
          (HookInfinity.generators (P := Fin n → ℝ) a))
    exact ⟨R, R.quotient_is_cover⟩
  · let e := HookInfinity.fiberEquivOfLe (R := k) (i := a) (a := a) le_rfl
    refine ⟨e.symm 1, ?_⟩
    intro hx
    have hone := congrArg e hx
    exact (one_ne_zero : (1 : k) ≠ 0) (by simpa using hone)

private theorem identity_isRankProjectiveCover
    {k : Type u} [Field k] {P : Type} [PartialOrder P]
    (M : PModule.{u,0,u} k P) (hfd : ∀ p, FiniteDimensional k (M.obj p))
    (hprojective : IsRankProjective M) : IsRankProjectiveCover (𝟙 M) := by
  letI : ∀ p, FiniteDimensional k (M.obj p) := hfd
  refine ⟨hprojective, ?_, ?_⟩
  · exact RankKernel.rankExact (𝟙 M)
      (fun p x => ⟨x, rfl⟩)
      (by
        intro a b hab x hx
        exact ⟨x, by simp, hx⟩)
  · intro u hu
    have hu' : u = 𝟙 M := by simpa using hu
    rw [hu']
    infer_instance

/-- The zero object satisfies the public cover certificate, including its
empty-fiber boundary case.
@isnad1 id=isrankpr.0h0v.s8.65956c611b81 from=translated src=- shape=12bccded vocab=3c5b1a53
-/
theorem zero_identity_isRankProjectiveCover :
    IsRankProjectiveCover (𝟙 (0 : PModule ℚ (Fin 2))) := by
  apply identity_isRankProjectiveCover
  · intro p
    infer_instance
  · intro L A B ι π hs α
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

/-- A shortest cover of the zero module on a finite poset is genuinely empty,
and its public certificate still records the actual empty quotient row.-/
noncomputable def zeroSelectedMinimalHookSumCover :
    MinimalHookSumCover (0 : PModule ℚ ForkGrade) :=
  Classical.choice <| exists_minimalHookSumCover
    (0 : PModule ℚ ForkGrade) (by intro p; infer_instance)

/--
@isnad1 id=isempty.0h0v.s6.9163781a211a from=translated src=- shape=93f688d9 vocab=0f8fc40b
-/
theorem zero_selected_minimal_cover_index_isEmpty :
    IsEmpty zeroSelectedMinimalHookSumCover.cover.Index := by
  apply Fintype.card_eq_zero_iff.mp
  have hminimal := zeroSelectedMinimalHookSumCover.minimal
    (canonicalHookSumCover (0 : PModule ℚ ForkGrade) (by intro p; infer_instance))
  change Fintype.card zeroSelectedMinimalHookSumCover.cover.Index ≤
    Fintype.card (FiniteHookDeflation.Index (0 : PModule ℚ ForkGrade)) at hminimal
  rw [zero_occurrences] at hminimal
  omega

/--
@isnad1 id=isrankpr.0h0v.s8.0fb59e94a841 from=translated src=- shape=5ed187af vocab=700951fa
-/
theorem zero_selected_minimal_cover_is_projective_cover :
    IsRankProjectiveCover zeroSelectedMinimalHookSumCover.cover.quotient :=
  zeroSelectedMinimalHookSumCover.isRankProjectiveCover

/-- A principal-upset projective also satisfies the public cover certificate
for its identity quotient.
@isnad1 id=isrankpr.0h1v.s7.f0e4230d962f from=translated src=- shape=515d36f2 vocab=fa15ab36
-/
theorem principalUpset_identity_isRankProjectiveCover (a : Fin 2) :
    IsRankProjectiveCover
      (𝟙 (HookInfinity.module (R := ℚ) a)) := by
  apply identity_isRankProjectiveCover
  · intro p
    infer_instance
  · exact HookInfinity.isRankProjective a

/-- A selected shortest hook-sum cover of a principal upset compares with its
identity cover through the public common-quotient uniqueness theorem.-/
noncomputable def principalUpsetSelectedMinimalHookSumCover (a : Fin 2) :
    MinimalHookSumCover (HookInfinity.module (R := ℚ) a) :=
  Classical.choice <| exists_minimalHookSumCover
    (HookInfinity.module (R := ℚ) a) (by intro p; infer_instance)

/-- The identity cover and a selected minimal hook-sum cover of a nonzero
principal upset are isomorphic over their shared target.
@isnad1 id=and.0h1v.s11.34bf66f5c041 from=translated src=- shape=b9c2e833 vocab=129d62c3
-/
theorem principalUpset_identity_iso_minimal_cover (a : Fin 2) :
    (∃ e : HookInfinity.module (R := ℚ) a ≅
        (⨁ (principalUpsetSelectedMinimalHookSumCover a).cover.summand),
      e.hom ≫ (principalUpsetSelectedMinimalHookSumCover a).cover.quotient =
        𝟙 (HookInfinity.module (R := ℚ) a)) ∧
      ∃ x : (HookInfinity.module (R := ℚ) a).obj a, x ≠ 0 := by
  constructor
  · exact IsRankProjectiveCover.exists_iso_over_quotient
      (principalUpset_identity_isRankProjectiveCover a)
      (principalUpsetSelectedMinimalHookSumCover a).isRankProjectiveCover
  · let e := HookInfinity.fiberEquivOfLe (R := ℚ) (i := a) (a := a) le_rfl
    refine ⟨e.symm 1, ?_⟩
    intro hx
    have hone := congrArg e hx
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa using hone)

/-- A selected shortest cover of the nonzero branching module has nonzero
kernel. If its kernel vanished, the rank-exact quotient would be an
isomorphism, making this non-projective module rank projective.-/
noncomputable def forkSelectedMinimalHookSumCover :
    MinimalHookSumCover (forkModule : PModule ℚ ForkGrade) :=
  Classical.choice <| exists_minimalHookSumCover forkModule
    (fun p => forkModule_finiteDimensional p)

/--
@isnad1 id=isrankpr.0h0v.s7.23941c0362a3 from=translated src=- shape=9fb6433c vocab=95b73c11
-/
theorem fork_selected_cover_is_projective_cover :
    IsRankProjectiveCover forkSelectedMinimalHookSumCover.cover.quotient :=
  forkSelectedMinimalHookSumCover.isRankProjectiveCover

/--
@isnad1 id=not.0h0v.s7.77cb684bd6c3 from=translated src=- shape=7996667e vocab=1511fc4c
-/
theorem fork_selected_cover_kernel_nonzero :
    ¬ IsZero (kernel forkSelectedMinimalHookSumCover.cover.quotient) := by
  intro hkernel
  let q := forkSelectedMinimalHookSumCover.cover.quotient
  haveI : Mono q := Preadditive.mono_of_isZero_kernel q hkernel
  haveI : ∀ p, Epi (q.app p) := fun p =>
    (ModuleCat.epi_iff_surjective _).mpr
      (forkSelectedMinimalHookSumCover.cover.row_rank_exact.surjective p)
  haveI : Epi q := (NatTrans.epi_iff_epi_app q).mpr fun p => inferInstance
  haveI : IsIso q := isIso_of_mono_of_epi q
  exact fork_not_rankProjective
    (IsRankProjective.of_iso
      forkSelectedMinimalHookSumCover.cover.term_isRankProjective (asIso q))

/-- The canonical cover of a two-dimensional singleton-poset module retains
two occurrences with the same hook tag.-/
private noncomputable def doubleCanonicalHookSumCover :
    HookSumCover (doubleModule : PModule ℚ (Fin 1)) :=
  canonicalHookSumCover doubleModule (fun p => doubleModule_finiteDimensional p)

private theorem doubleCanonicalHookSumCover_tag (i : doubleCanonicalHookSumCover.Index) :
    doubleCanonicalHookSumCover.tag i = .inr (0 : Fin 1) := by
  cases i with
  | inl t =>
      have hEq : t.1.1.1 = t.1.1.2 := Subsingleton.elim _ _
      exact False.elim ((not_lt_of_ge (le_of_eq hEq.symm)) t.1.property)
  | inr t =>
      have hgrade : t.1 = (0 : Fin 1) := Subsingleton.elim _ _
      change (Sum.inr t.1 :
        FiniteRankProjectiveClassification.RankProjectiveHookTag (Fin 1)) =
        (Sum.inr (0 : Fin 1) :
          FiniteRankProjectiveClassification.RankProjectiveHookTag (Fin 1))
      rw [hgrade]

/--
@isnad1 id=and.0h0v.s7.8e00a8c517ab from=translated src=- shape=dce47241 vocab=907eb56a
-/
theorem double_canonical_cover_retains_repeated_occurrences :
    Fintype.card doubleCanonicalHookSumCover.Index = 2 ∧
      ∀ i j : doubleCanonicalHookSumCover.Index,
        doubleCanonicalHookSumCover.tag i = doubleCanonicalHookSumCover.tag j := by
  constructor
  · change Fintype.card (FiniteHookDeflation.Index doubleModule) = 2
    exact repeated_occurrences
  · intro i j
    rw [doubleCanonicalHookSumCover_tag, doubleCanonicalHookSumCover_tag]

end TDA.Persistence.FiniteRankProjectiveResolutionKanExamples
