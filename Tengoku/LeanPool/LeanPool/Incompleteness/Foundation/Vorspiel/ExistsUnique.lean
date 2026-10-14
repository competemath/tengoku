/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku

/-! # ExistsUnique -/

@[expose] public section

namespace Classical
variable {α : Sort*} {φ : α → Prop} (h : ∃! x, φ x)

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def «choose!» : α := choose h.exists

lemma «choose!_spec» : φ (choose! h) := choose_spec h.exists

/--
@isnad1 id=eq.1h4v.s4.0a931f92292e from=translated src=- shape=392cf232 vocab=72ed6b9d
-/
lemma choose_uniq (hx : φ x) : x = choose! h := h.unique hx (choose!_spec h)

lemma «choose!_eq_iff» : x = choose! h ↔ φ x := ⟨by rintro rfl; exact choose!_spec h, choose_uniq _⟩

end Classical
