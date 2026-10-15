/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic

/-! # Closure -/

@[expose] public section

namespace LO
namespace Modal

namespace Kripke

variable {F : Frame} {x y z : F.World}

open Relation

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.RelReflTransGen : _root_.Rel F.World F.World :=
  ReflTransGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺^* " => Frame.RelReflTransGen

namespace Frame
namespace RelReflTransGen

/--
@isnad1 id=relreflt.1h3v.s4.3a6b3b508270 from=translated src=- shape=b257a80e vocab=0e824ce9
-/
@[simp] lemma single (hxy : x ≺ y) : x ≺^* y := ReflTransGen.single hxy

/--
@isnad1 id=refl.0h1v.s2.dbd1fe2022bf from=translated src=- shape=fc2c1e2b vocab=29b4be19
-/
@[simp] lemma reflexive : Std.Refl F.RelReflTransGen := ⟨fun _ => ReflTransGen.refl⟩

/--
@isnad1 id=relreflt.0h2v.s3.1aac3e9e2907 from=translated src=- shape=f3577ae2 vocab=99d00556
-/
@[simp] lemma refl {x : F.World} : x ≺^* x := reflexive.refl x

/--
@isnad1 id=istrans.0h1v.s2.8f9fbd6b0727 from=translated src=- shape=fc2c1e2b vocab=0e95339c
-/
@[simp] lemma transitive : IsTrans F.World F.RelReflTransGen :=
  ⟨fun _ _ _ hxy hyz => ReflTransGen.trans hxy hyz⟩

/--
@isnad1 id=issymmet.1h1v.s3.c86b559b9d72 from=translated src=- shape=2c5f3b97 vocab=f3e71005
-/
@[simp] lemma symmetric : IsSymmetric F.Rel → IsSymmetric F.RelReflTransGen := fun h => by
  let : Std.Symm F.Rel := ⟨fun _ _ => @h _ _⟩
  exact fun _ _ hxy => Std.Symm.symm (r := F.RelReflTransGen) _ _ hxy

end RelReflTransGen
end Frame

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^* ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^*" => Frame.TransitiveReflexiveClosure

namespace Frame
namespace TransitiveReflexiveClosure

/--
@isnad1 id=rel.1h3v.s4.7d7a0f5a4069 from=translated src=- shape=68259aca vocab=1a9ba177
-/
lemma single (hxy : x ≺ y) : F^*.Rel x y := ReflTransGen.single hxy

/--
@isnad1 id=refl.0h1v.s3.1a4c07449f5f from=translated src=- shape=615d4b79 vocab=c0de9502
-/
lemma rel_reflexive : Std.Refl (F^*.Rel) := ⟨fun _ => ReflTransGen.refl⟩

/--
@isnad1 id=istrans.0h1v.s3.d6d571409d11 from=translated src=- shape=615d4b79 vocab=2c41f7ce
-/
lemma rel_transitive : IsTrans (F^*) (F^*.Rel) := ⟨fun _ _ _ hxy hyz => ReflTransGen.trans hxy hyz⟩

/--
@isnad1 id=issymmet.1h1v.s3.e202e40dff9f from=translated src=- shape=9b982a1d vocab=0a7eb72a
-/
lemma rel_symmetric : IsSymmetric F.Rel → IsSymmetric (F^*) := fun h => by
  simp_all

end TransitiveReflexiveClosure
end Frame

end «lp_section_1»

section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World :=
  TransGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺^+ " => Frame.RelTransGen

namespace Frame
namespace RelTransGen

/--
@isnad1 id=reltrans.1h3v.s4.8968bcf47b02 from=translated src=- shape=b257a80e vocab=30a20dcc
-/
@[simp] lemma single (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

/--
@isnad1 id=istrans.0h1v.s2.2fe59d0a7307 from=translated src=- shape=fc2c1e2b vocab=0442d0cf
-/
@[simp]
lemma transitive : IsTrans F.World F.RelTransGen := ⟨fun _ _ _ => TransGen.trans⟩

/--
@isnad1 id=issymmet.1h1v.s3.f38be0cf43c0 from=translated src=- shape=2c5f3b97 vocab=81c71ba6
-/
@[simp]
lemma symmetric (hSymm : IsSymmetric F.Rel) : IsSymmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single <| hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single <| hSymm hyz) ih

end RelTransGen
end Frame

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^+ ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^+" => Frame.TransitiveClosure

namespace Frame
namespace TransitiveClosure

/--
@isnad1 id=rel.1h3v.s4.004e9f64dfd2 from=translated src=- shape=68259aca vocab=8755a564
-/
lemma single (hxy : x ≺ y) : F^+.Rel x y := TransGen.single hxy

/--
@isnad1 id=istrans.0h1v.s3.a12fb618d053 from=translated src=- shape=615d4b79 vocab=dc8d85b5
-/
lemma rel_transitive : IsTrans (F^+) (F^+.Rel) := ⟨fun _ _ _ => TransGen.trans⟩

/--
@isnad1 id=issymmet.1h1v.s3.a287042654b2 from=translated src=- shape=9b982a1d vocab=9442a557
-/
lemma rel_symmetric (hSymm : IsSymmetric F.Rel) : IsSymmetric (F^+) := by simp_all

end TransitiveClosure
end Frame

end «lp_section_2»

section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelReflGen : _root_.Rel F.World F.World :=
  ReflGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ≺^= " => Frame.RelReflGen

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.ReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^= ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^=" => Frame.ReflexiveClosure

end «lp_section_3»

section «lp_section_4»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelIrreflGen : _root_.Rel F.World F.World :=
  IrreflGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ≺^≠ " => Frame.RelIrreflGen

namespace Frame
namespace RelIrreflGen

/--
@isnad1 id=irrefl.0h1v.s2.5021fa570881 from=translated src=- shape=fc2c1e2b vocab=42e58ac9
-/
@[simp] lemma rel_irreflexive : Std.Irrefl F.RelIrreflGen := by exact ⟨fun x h => h.1 rfl⟩

end RelIrreflGen
end Frame

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.IrreflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^≠ ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^≠" => Frame.IrreflexiveClosure

namespace Frame
namespace IrreflexiveClosure

/--
@isnad1 id=irrefl.0h1v.s3.b5f8974cfc21 from=translated src=- shape=615d4b79 vocab=a120e4e6
-/
lemma rel_irreflexive : Std.Irrefl (F^≠.Rel) := by exact ⟨fun x h => h.1 rfl⟩

end IrreflexiveClosure
end Frame

end «lp_section_4»

end Kripke

end Modal
end LO
