module

public import Tengoku.Seed.Logic.IsEmpty.Basic

namespace IsEmpty
end IsEmpty

namespace FoundationFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

namespace IsEmpty
open _root_.IsEmpty
variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim' {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim := funext h.elim

end IsEmpty

end
