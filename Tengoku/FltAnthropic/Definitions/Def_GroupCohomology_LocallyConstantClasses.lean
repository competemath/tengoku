import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

noncomputable abbrev inflation (M : Rep k G) (S : Subgroup G) [S.Normal] :
    H1 (M.quotientToInvariants S) ⟶ H1 M :=
  groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (M.ρ.quotientToInvariants_lift S)) 1

/--
@isnad1 id=eq.0h4v.s7.27f588def3d6 from=translated src=- shape=deccc114 vocab=c1a3bfef
-/
lemma inflation_eq_H1InfRes_f (M : Rep k G) (S : Subgroup G) [S.Normal] :
    inflation M S = (H1InfRes M S).f :=
  rfl

noncomputable def inflationImage (M : Rep k G) (S : Subgroup G) [S.Normal] :
    Submodule k (H1 M) :=
  LinearMap.range (inflation M S).hom

/--
@isnad1 id=iff.0h5v.s9.a5ec1201d85d from=translated src=- shape=8e7d9423 vocab=6d53e96e
-/
lemma mem_inflationImage_iff (M : Rep k G) (S : Subgroup G) [S.Normal] (x : H1 M) :
    x ∈ inflationImage M S ↔ ∃ y, (inflation M S).hom y = x :=
  Iff.rfl

/--
@isnad1 id=mem.0h5v.s9.e2c23acb6065 from=translated src=- shape=a43df404 vocab=6d53e96e
-/
lemma inflation_mem_inflationImage (M : Rep k G) (S : Subgroup G) [S.Normal]
    (y : H1 (M.quotientToInvariants S)) :
    (inflation M S).hom y ∈ inflationImage M S :=
  LinearMap.mem_range_self _ y

noncomputable def locallyConstantClasses (M : Rep k G) : Submodule k (H1 M) :=
  ⨆ S : {S : Subgroup G // S.Normal ∧ S.FiniteIndex},
    haveI : S.1.Normal := S.2.1
    inflationImage M S.1

/--
@isnad1 id=le.0h4v.s8.0e1a8b46d86f from=translated src=- shape=96603bc7 vocab=0bdd7a08
-/
lemma inflationImage_le_locallyConstantClasses (M : Rep k G) (S : Subgroup G) [hN : S.Normal]
    [hF : S.FiniteIndex] : inflationImage M S ≤ locallyConstantClasses M :=
  le_iSup (fun S : {S : Subgroup G // S.Normal ∧ S.FiniteIndex} =>
    haveI : S.1.Normal := S.2.1
    inflationImage M S.1) ⟨S, hN, hF⟩

/--
@isnad1 id=le.1h5v.s9.a0d3372757e4 from=translated src=- shape=d0f95d5e vocab=0bdd7a08
-/
lemma le_locallyConstantClasses_of_le_inflationImage (M : Rep k G) {L : Submodule k (H1 M)}
    {S : Subgroup G} [S.Normal] [S.FiniteIndex] (hL : L ≤ inflationImage M S) :
    L ≤ locallyConstantClasses M :=
  hL.trans (inflationImage_le_locallyConstantClasses M S)

end groupCohomology
