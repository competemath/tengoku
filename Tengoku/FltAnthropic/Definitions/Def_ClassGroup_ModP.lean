import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped NumberField nonZeroDivisors

namespace JacobiSumStickelberger

section ModP

variable (p : ℕ) (M : Type*) [AddCommGroup M]

def nsmulRange : AddSubgroup M where
  carrier := Set.range fun x : M => p • x
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, smul_add p x y⟩
  zero_mem' := ⟨0, smul_zero p⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by simp⟩

/--
@isnad1 id=iff.0h3v.s5.b1694d837e2a from=translated src=- shape=1f833a68 vocab=013c8333
-/
@[simp] lemma mem_nsmulRange {x : M} : x ∈ nsmulRange p M ↔ ∃ y, p • y = x := Iff.rfl

/--
@isnad1 id=mem.0h3v.s5.42a549ab5969 from=translated src=- shape=9edc7916 vocab=013c8333
-/
lemma nsmul_mem_nsmulRange (x : M) : p • x ∈ nsmulRange p M := ⟨x, rfl⟩

abbrev ModP : Type _ := M ⧸ nsmulRange p M

instance instModuleZModModP [NeZero p] : Module (ZMod p) (ModP p M) :=
  QuotientAddGroup.zmodModule (nsmul_mem_nsmulRange p M)

def ModP.proj : M →+ ModP p M := QuotientAddGroup.mk' (nsmulRange p M)

/--
@isnad1 id=eq.0h3v.s7.0296994bd152 from=translated src=- shape=55baa4e9 vocab=50382c0c
-/
@[simp] lemma ModP.proj_apply (x : M) : ModP.proj p M x = QuotientAddGroup.mk x := rfl

variable {M} in

/--
@isnad1 id=le.0h3v.s6.b19e2d2e124f from=translated src=- shape=9bf56899 vocab=1711440e
-/
lemma nsmulRange_le_comap (f : M →+ M) : nsmulRange p M ≤ (nsmulRange p M).comap f := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (map_nsmul f p x).symm⟩

variable {M} in

def ModP.mapHom (f : M →+ M) : ModP p M →+ ModP p M :=
  QuotientAddGroup.map (nsmulRange p M) (nsmulRange p M) f (nsmulRange_le_comap p f)

variable {M} in
/--
@isnad1 id=eq.0h4v.s8.a68cc892db70 from=translated src=- shape=d69368b5 vocab=13442345
-/
@[simp] lemma ModP.mapHom_proj (f : M →+ M) (x : M) :
    ModP.mapHom p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

variable {M} in

noncomputable def ModP.mapEnd [NeZero p] (f : M →+ M) : Module.End (ZMod p) (ModP p M) :=
  (ModP.mapHom p f).toZModLinearMap p

variable {M} in
/--
@isnad1 id=eq.0h4v.s8.f7c1ec403987 from=translated src=- shape=403b1653 vocab=35c06155
-/
@[simp] lemma ModP.mapEnd_proj [NeZero p] (f : M →+ M) (x : M) :
    ModP.mapEnd p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

end ModP

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]
variable (R : Type*) [CommRing R] [IsDomain R]

abbrev ClGalModule : Type _ := ModP p (Additive (ClassGroup R))

noncomputable def clProj : Additive (ClassGroup R) →+ ClGalModule p R :=
  ModP.proj p (Additive (ClassGroup R))

variable {R}

noncomputable def clEnd (g : R ≃+* R) : Module.End (ZMod p) (ClGalModule p R) :=
  ModP.mapEnd p (MonoidHom.toAdditive (ClassGroup.mulEquiv g).toMonoidHom)

/--
@isnad1 id=eq.0h4v.s10.d6c8193c3c11 from=translated src=- shape=28cf9306 vocab=97eab924
-/
@[simp] lemma clEnd_clProj (g : R ≃+* R) (C : ClassGroup R) :
    clEnd p g (clProj p R (Additive.ofMul C)) =
      clProj p R (Additive.ofMul (ClassGroup.mulEquiv g C)) := rfl

end ClassGroupCarrier

end JacobiSumStickelberger
