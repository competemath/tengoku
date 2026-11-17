import Tengoku.Seed.Data.ZMod.Units
import Tengoku.Seed.GroupTheory.Index

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CohCarrier_index_comap_unitsMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CohCarrier_index_comap_unitsMap

set_option autoImplicit false

/--
@isnad1 id=eq.1h3v.s7.72ca8c2420c2 from=translated src=- shape=7ee27b52 vocab=8c619bb6
-/
theorem solution
    {M M' : ℕ} [NeZero M'] (hMM' : M ∣ M') (H₀ : Subgroup (ZMod M)ˣ) :
    (H₀.comap (ZMod.unitsMap hMM')).index = H₀.index :=
  Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hMM')
