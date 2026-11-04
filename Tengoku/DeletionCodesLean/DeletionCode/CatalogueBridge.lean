import Tengoku.DeletionCodesLean.DeletionCode.CatalogueWords
import Tengoku.DeletionCodesLean.DeletionCode.SignedRuleCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms differentLengths` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ValidCatalogue.geometry` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ValidCatalogue.rank_disjoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms word_generating` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms valid_generatingRuleSet` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms catalogueGeneratingSet_card_bound` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The manuscript's local-word grammar and catalogue geometry imply the signed
rule-count hypotheses. The unequal path lengths are derived from the grammar's
header bounds; neither the edit identity nor support noncancellation is assumed.
The optional balanced class also requires t bubbles of each orientation per
rule and exactly R distinct resulting rules. Linear independence can further
restrict this class and is unnecessary for the bound proved here.
-/

namespace DeletionCode.CatalogueBridge

open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount

def indexedFamily {k ν R : ℕ} (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) :
    EditedFamily (Fin ν) k := editedFamily bubbles (fun b => (group b).val)

/-- Header lengths alone already imply that the two paths have unequal numbers of windows.
@isnad1 id=ne.0h4v.s4.f17bdc99e21e from=translated src=- shape=5478aa6c vocab=af13001f
-/
theorem differentLengths {B : Type*} {k : ℕ} (E : EditedFamily B k) (b : B) :
    E.family.extra b false ≠ E.family.extra b true := by
  have hlo := E.rho_lower b
  have hhi := E.rho_upper b
  cases ho : (E.header b).orientation <;>
    simp only [EditedFamily.family, PathMemory.pathLength, Bool.false_eq_true,
      ite_false, ite_true, negativeLength, positiveLength, shortLength, longLength,
      windowLength, ho] <;> omega

/-- Exactly the local word-boundary and path restrictions used by the catalogue.-/
structure ValidCatalogue {k ν R : ℕ}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) : Prop where
  boundary : ∀ b, (bubbles b).left.getLast? = some (!(bubbles b).bit) ∧
    (bubbles b).right.head? = some (!(bubbles b).bit)
  simple : ∀ b side, Function.Injective
    (fun i : Fin ((indexedFamily bubbles group).family.extra b side + 2) =>
      SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b side i.val)
  endpoints : ∀ b i j,
    i ≤ (indexedFamily bubbles group).family.extra b false + 1 →
    j ≤ (indexedFamily bubbles group).family.extra b true + 1 →
    SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b false i =
      SupportComponents.vertex (indexedFamily bubbles group).family (windowLength k) b true j →
    (i = 0 ∧ j = 0) ∨
      (i = (indexedFamily bubbles group).family.extra b false + 1 ∧
        j = (indexedFamily bubbles group).family.extra b true + 1)
  within_rule_disjoint : ∀ r : Fin R,
    VertexDisjointOn (indexedFamily bubbles group).family (windowLength k)
      (Finset.univ.filter (fun b => group b = r))

/--
@isnad1 id=bubblege.1h5v.s5.9bc3bc11c3b5 from=translated src=- shape=33921cad vocab=3256e651
-/
theorem ValidCatalogue.geometry {k ν R : ℕ}
    {bubbles : Fin ν → BubbleWord k} {group : Fin ν → Fin R}
    (h : ValidCatalogue bubbles group) :
    BubbleGeometry (indexedFamily bubbles group).family (windowLength k) :=
  ⟨h.simple, h.endpoints, differentLengths (indexedFamily bubbles group)⟩

/--
@isnad1 id=vertexdi.1h6v.s5.3ae787fe618e from=translated src=- shape=abe36351 vocab=cb8a8b1f
-/
theorem ValidCatalogue.rank_disjoint {k ν R : ℕ}
    {bubbles : Fin ν → BubbleWord k} {group : Fin ν → Fin R}
    (h : ValidCatalogue bubbles group) :
    ∀ i, VertexDisjointOn (indexedFamily bubbles group).family (windowLength k)
      (ruleBubbles (indexedFamily bubbles group).family i) := by
  intro i a ha b hb hab sa sb j l hj hl
  have hra := (Finset.mem_filter.mp ha).2
  have hrb := (Finset.mem_filter.mp hb).2
  change (group a).val = i at hra
  change (group b).val = i at hrb
  have hgroup : group b = group a := Fin.ext (hrb.trans hra.symm)
  exact h.within_rule_disjoint (group a) a (by simp) b (by simp [hgroup]) hab sa sb j l hj hl

/-- Signed provenance supplies every actual negative L-window's source.
@isnad1 id=generati.2h7v.s6.b8239ced39d7 from=translated src=- shape=199b1a33 vocab=6393bed3
-/
theorem word_generating {k ν R n : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k)) :
    (indexedFamily bubbles group).family.Generating x n (windowLength k) :=
  signed_generating_implies_generating (indexedFamily bubbles group).family x n
    (windowLength k) hvalid.geometry hvalid.rank_disjoint hgen

/-- The concrete catalogue conditions imply the entire signed counting interface.
@isnad1 id=generati.3h8v.s6.df720ebbad72 from=translated src=- shape=681856cd vocab=c47841ed
-/
theorem valid_generatingRuleSet {k ν R n c : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k))
    (hc : Fintype.card
      (SupportComponents.GraphComponents (indexedFamily bubbles group).family (windowLength k)) = c) :
    GeneratingRuleSet x n k ν R c group (rulesOfFamily (indexedFamily bubbles group) group) := by
  exact ⟨indexedFamily bubbles group, fun _ => rfl, hvalid.geometry,
    hvalid.rank_disjoint, hgen, hc, rfl⟩

/-- A rule contains exactly t deletions and t insertions, as in the manuscript.-/
def OrientationBalanced {k ν R : ℕ} (t : ℕ)
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R) : Prop :=
  ∀ r : Fin R,
    (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .deletion)).card = t ∧
    (Finset.univ.filter (fun b => group b = r ∧ (bubbles b).orientation = .insertion)).card = t

/-- The grammar-defined, balanced catalogue class; independence may further restrict it.-/
def CatalogueGeneratingSet (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (Q : RuleSet k) : Prop :=
  ∃ bubbles : Fin ν → BubbleWord k,
    ValidCatalogue bubbles group ∧ OrientationBalanced t bubbles group ∧
    SignedGenerating (indexedFamily bubbles group).family x n (windowLength k) ∧
    Fintype.card
      (SupportComponents.GraphComponents (indexedFamily bubbles group).family (windowLength k)) = c ∧
    rulesOfFamily (indexedFamily bubbles group) group = Q ∧ Q.card = R

/--
@isnad1 id=generati.1h9v.s5.b2f23b508237 from=translated src=- shape=9c8db4c3 vocab=0010526a
-/
theorem catalogueGeneratingSet_included (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (Q : RuleSet k)
    (hQ : CatalogueGeneratingSet x n k ν R t c group Q) :
    GeneratingRuleSet x n k ν R c group Q := by
  obtain ⟨bubbles, hvalid, _, hgen, hc, rfl, _⟩ := hQ
  exact valid_generatingRuleSet bubbles group hvalid hgen hc

/-- The complete grammar-defined catalogue class inherits the finite-record count.
@isnad1 id=le.2h8v.s6.af46d0ff923d from=translated src=- shape=729c3e88 vocab=8159b730
-/
theorem catalogueGeneratingSet_card_bound (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // CatalogueGeneratingSet x n k ν R t c group Q} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  let : Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    generatingRuleSet_finite x n k ν R c group hν hx
  let inclusion : {Q : RuleSet k // CatalogueGeneratingSet x n k ν R t c group Q} →
      {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    fun Q => ⟨Q.val, catalogueGeneratingSet_included x n k ν R t c group Q.val Q.property⟩
  have hinj : Function.Injective inclusion := by
    intro Q₁ Q₂ heq
    apply Subtype.ext
    exact congrArg (fun Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} => Q.val) heq
  exact (Nat.card_le_card_of_injective inclusion hinj).trans
    (generatingRuleSet_card_bound x n k ν R c group hν hx)

end DeletionCode.CatalogueBridge
