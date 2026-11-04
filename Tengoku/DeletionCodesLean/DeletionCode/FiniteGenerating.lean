import Tengoku.DeletionCodesLean.DeletionCode.RelationBlockSavings
import Tengoku.DeletionCodesLean.DeletionCode.BlockAdjunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms independent_restrict` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generating_restrict` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms GeneratingAt.restrict` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generating_blockHull` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generating_blockOf` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Ordered generation on actual finite sets of integer rules. A strict rank
assignment records the inherited order. Restriction to whole rule blocks
preserves both that order and rational independence, and retains each supplier
because it shares the actual negative gram.
-/
namespace DeletionCode.FiniteGenerating

open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

def GeneratingOn {k : ℕ} (v : Gram (windowLength k) → ℤ) (G : RuleSet k)
    (rank : (Gram (windowLength k) → ℤ) → ℕ) : Prop :=
  ∀ u ∈ G, ∀ g, u g = -1 → v g ≠ 0 ∨ ∃ z ∈ G, rank z < rank u ∧ z g ≠ 0

def Independent {k : ℕ} (G : RuleSet k) : Prop :=
  LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ))

/-- A finite independent generating set with an actual strict ordering.-/
structure GeneratingAt {k : ℕ} (v : Gram (windowLength k) → ℤ) (G : RuleSet k) : Prop where
  independent : Independent G
  ordered : ∃ rank : (Gram (windowLength k) → ℤ) → ℕ,
    Set.InjOn rank (↑G : Set _) ∧ GeneratingOn v G rank

def ClosedIn {k : ℕ} (G U : RuleSet k) : Prop :=
  ∀ a ∈ U, ∀ b ∈ G, ConnectedIn G a b → b ∈ U

/--
@isnad1 id=independ.2h3v.s5.e0cc30c2aec2 from=translated src=- shape=60619e67 vocab=955fb27f
-/
theorem independent_restrict {k : ℕ} {G U : RuleSet k} (hUG : U ⊆ G)
    (hind : Independent G) : Independent U := by
  let f : U → G := fun u => ⟨u.val, hUG u.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun u : G => u.val) hab)
  exact hind.comp f hf

/--
@isnad1 id=generati.3h5v.s5.25a7352e14db from=translated src=- shape=92edb70b vocab=c23faeef
-/
theorem generating_restrict {k : ℕ} (v : Gram (windowLength k) → ℤ)
    (G U : RuleSet k) (rank : (Gram (windowLength k) → ℤ) → ℕ)
    (hUG : U ⊆ G) (hclosed : ClosedIn G U) (hgen : GeneratingOn v G rank) :
    GeneratingOn v U rank := by
  intro u hu g hneg
  rcases hgen u (hUG hu) g hneg with hv | ⟨z, hz, hrank, hzg⟩
  · exact Or.inl hv
  · have hconnect : ConnectedIn G u z := Relation.EqvGen.rel _ _
      ⟨hUG hu, hz, gramPrefix g,
        GeneratingBlocks.nonzero_incident u g (by omega),
        GeneratingBlocks.nonzero_incident z g hzg⟩
    exact Or.inr ⟨z, hclosed u hu z hz hconnect, hrank, hzg⟩

/--
@isnad1 id=generati.3h4v.s5.8eb277f10eda from=translated src=- shape=277ce223 vocab=e61bf0c8
-/
theorem GeneratingAt.restrict {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G U : RuleSet k} (hgen : GeneratingAt v G) (hUG : U ⊆ G)
    (hclosed : ClosedIn G U) : GeneratingAt v U := by
  obtain ⟨rank, hinj, horder⟩ := hgen.ordered
  refine ⟨independent_restrict hUG hgen.independent, rank, ?_,
    generating_restrict v G U rank hUG hclosed horder⟩
  intro a ha b hb hab
  exact hinj (hUG ha) (hUG hb) hab

/--
@isnad1 id=closedin.0h3v.s3.55029ade60eb from=translated src=- shape=617d5f33 vocab=736d464d
-/
theorem blockHull_closed {k : ℕ} (G I : RuleSet k) :
    ClosedIn G (RelationBlockSavings.blockHull G I) := by
  intro a ha b _ hab
  exact RelationBlockSavings.blockHull_closed G I ha hab

/--
@isnad1 id=generati.1h4v.s4.6a2002512010 from=translated src=- shape=24727f20 vocab=c3f41386
-/
theorem generating_blockHull {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (I : RuleSet k) :
    GeneratingAt v (RelationBlockSavings.blockHull G I) :=
  hgen.restrict (RelationBlockSavings.blockHull_subset G I) (blockHull_closed G I)

/--
@isnad1 id=closedin.0h3v.s4.81fdc9b8d59f from=translated src=- shape=9f42b38c vocab=a4d24339
-/
theorem blockOf_closed {k : ℕ} (G : RuleSet k) (a : Gram (windowLength k) → ℤ) :
    ClosedIn G (blockOf G a) := by
  intro b hb c hc hbc
  exact (mem_blockOf G a c).mpr
    ⟨hc, Relation.EqvGen.trans _ _ _ ((mem_blockOf G a b).mp hb).2 hbc⟩

/--
@isnad1 id=generati.1h4v.s4.8645f0cfcd2d from=translated src=- shape=412bdd08 vocab=e6831ad2
-/
theorem generating_blockOf {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (a : Gram (windowLength k) → ℤ) :
    GeneratingAt v (blockOf G a) := by
  apply hgen.restrict
  · intro u hu
    exact ((mem_blockOf G a u).mp hu).1
  · exact blockOf_closed G a

end DeletionCode.FiniteGenerating
