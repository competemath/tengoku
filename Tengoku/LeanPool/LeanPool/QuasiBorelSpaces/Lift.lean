/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Defs
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic

/-!
# LeanPool.QuasiBorelSpaces.Lift

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Lift`.
-/

@[expose] public section

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

namespace QuasiBorelSpace.ULift

instance : QuasiBorelSpace (ULift A) := lift ULift.down

/--
@isnad1 id=iff.0h3v.s5.ee5e9a198b16 from=translated src=- shape=1b8e0fd2 vocab=cd308fc1
-/
@[simp]
lemma isHom_def {φ : A → ULift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by
  simp only [isHom_to_lift]

/--
@isnad1 id=ishom.1h3v.s5.0875cc1364fa from=translated src=- shape=3ee43307 vocab=a8485d7b
-/
@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ ULift.up (f x)) := by
  simp only [isHom_def, hf]

/--
@isnad1 id=ishom.1h3v.s5.c69e35b7b2e8 from=translated src=- shape=926bfecc vocab=cd308fc1
-/
@[fun_prop]
lemma isHom_down {f : A → ULift B} (hf : IsHom f) : IsHom (fun x ↦ ULift.down (f x)) := by
  simp_all

end QuasiBorelSpace.ULift

namespace QuasiBorelSpace.PLift

instance : QuasiBorelSpace (PLift A) := lift PLift.down

/--
@isnad1 id=iff.0h3v.s5.c26ebfb388f3 from=translated src=- shape=1b8e0fd2 vocab=7f723650
-/
@[simp]
lemma isHom_def {φ : A → PLift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by
  simp only [isHom_to_lift]

/--
@isnad1 id=ishom.1h3v.s5.14c5b0c6376c from=translated src=- shape=3ee43307 vocab=2614e91d
-/
@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ PLift.up (f x)) := by
  simp only [isHom_def, hf]

/--
@isnad1 id=ishom.1h3v.s5.0777a3d10d54 from=translated src=- shape=926bfecc vocab=7f723650
-/
@[fun_prop]
lemma isHom_down {f : A → PLift B} (hf : IsHom f) : IsHom (fun x ↦ PLift.down (f x)) := by
  simp_all

end QuasiBorelSpace.PLift
