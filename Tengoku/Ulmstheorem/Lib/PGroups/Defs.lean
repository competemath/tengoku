import Tengoku.Ulmstheorem.Lib.PGroups.Heights

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduced abelian p-groups: legacy compatibility import

Historically the core algebra for reduced abelian `p`-groups lived in this file.
It now re-exports the reorganized `PGroups` layer:

- `Lib.PGroups.Subgroups`
- `Lib.PGroups.UlmSubgroups`
- `Lib.PGroups.Heights`

Existing imports of `Lib.PGroups.Defs` therefore continue to work while the
library is migrated to the new layout.
-/
