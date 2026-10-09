/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Group.Completion
public import Tengoku.Seed.Analysis.Asymptotics.Defs
public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Order

/-!
# Asymptotics in the completion of a normed space

In this file we prove lemmas relating `f = O(g)` etc
for composition of functions with coercion of a seminormed group to its completion.
-/

public section

variable {α E F : Type*} [Norm E] [SeminormedAddCommGroup F]
  {f : α → E} {g : α → F} {l : Filter α}

local postfix:100 "̂" => UniformSpace.Completion

open UniformSpace.Completion

namespace Asymptotics

/--
@isnad1 id=iff.0h6v.s6.decc50b7544b from=seed src=0 shape=d92731ea vocab=5350b4fa
-/
@[simp, norm_cast]
lemma isBigO_completion_left : (fun x ↦ g x : α → F̂) =O[l] f ↔ g =O[l] f := by
  simp only [isBigO_iff, norm_coe]

/--
@isnad1 id=iff.0h6v.s6.0c101c51264c from=seed src=0 shape=2f4c2beb vocab=5350b4fa
-/
@[simp, norm_cast]
lemma isBigO_completion_right : f =O[l] (fun x ↦ g x : α → F̂) ↔ f =O[l] g := by
  simp only [isBigO_iff, norm_coe]

/--
@isnad1 id=iff.0h6v.s6.20bf22375490 from=seed src=0 shape=d92731ea vocab=a6d12073
-/
@[simp, norm_cast]
lemma isTheta_completion_left : (fun x ↦ g x : α → F̂) =Θ[l] f ↔ g =Θ[l] f :=
  and_congr isBigO_completion_left isBigO_completion_right

/--
@isnad1 id=iff.0h6v.s6.a59ef5d17191 from=seed src=0 shape=2f4c2beb vocab=a6d12073
-/
@[simp, norm_cast]
lemma isTheta_completion_right : f =Θ[l] (fun x ↦ g x : α → F̂) ↔ f =Θ[l] g :=
  and_congr isBigO_completion_right isBigO_completion_left

/--
@isnad1 id=iff.0h6v.s6.dcb5571108a6 from=seed src=0 shape=d92731ea vocab=6328e09e
-/
@[simp, norm_cast]
lemma isLittleO_completion_left : (fun x ↦ g x : α → F̂) =o[l] f ↔ g =o[l] f := by
  simp only [isLittleO_iff, norm_coe]

/--
@isnad1 id=iff.0h6v.s6.626e1aa00b87 from=seed src=0 shape=2f4c2beb vocab=6328e09e
-/
@[simp, norm_cast]
lemma isLittleO_completion_right : f =o[l] (fun x ↦ g x : α → F̂) ↔ f =o[l] g := by
  simp only [isLittleO_iff, norm_coe]

end Asymptotics
