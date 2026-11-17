import Tengoku.StringDiagramsLean.StringDiagrams.Super.SVec

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quotients of superspaces

A graded submodule of a superspace `V` (`StringDiagrams.SVec`) is a submodule stable under the
projection onto the odd part (`SVec.GradedSubmodule`). The quotient `SVec.quot V U` by a graded
submodule is a superspace, with the quotient map `SVec.quotMk` an even linear map. A linear map
`f : V → W` carrying `U` into `U'` descends to `SVec.quotMap f hf : V ⧸ U → W ⧸ U'`; the descent
is compatible with identities, composition, sums, scalars, parity components
(`homProj_quotMap`, `twist_quotMap`) and parities (`quotMap_mem`).

This is used for the balanced tensor product of superbimodules
(`StringDiagrams.Super.BalancedTensor`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe u

namespace SVec

variable {k : Type u} [CommRing k]

/-- A graded submodule of a superspace: a submodule stable under the projection onto the odd
part (equivalently, spanned by homogeneous vectors).-/
structure GradedSubmodule (V : SVec k) where
  /-- The underlying submodule.-/
  toSubmodule : Submodule k V
  odd_mem : ∀ v ∈ toSubmodule, V.odd v ∈ toSubmodule

namespace GradedSubmodule

variable {V : SVec k}

instance : SetLike (GradedSubmodule V) V where
  coe U := U.toSubmodule
  coe_injective U U' h := by
    cases U; cases U'
    congr
    exact SetLike.coe_injective h

/--
@isnad1 id=injectiv.0h2v.s5.8e38cf0dcf61 from=translated src=- shape=dc927cd9 vocab=35de9675
-/
theorem toSubmodule_injective :
    Function.Injective (toSubmodule : GradedSubmodule V → Submodule k V) := by
  rintro ⟨U, _⟩ ⟨U', _⟩ h
  cases h; rfl

/--
@isnad1 id=iff.0h4v.s7.b09376b6f91f from=translated src=- shape=49285856 vocab=29f38033
-/
theorem mem_toSubmodule {U : GradedSubmodule V} {v : V} : v ∈ U.toSubmodule ↔ v ∈ U := Iff.rfl

/--
@isnad1 id=mem.0h3v.s6.a2ea4c093a5b from=translated src=- shape=2556ca4d vocab=9f8d623e
-/
theorem zero_mem (U : GradedSubmodule V) : (0 : V) ∈ U := U.toSubmodule.zero_mem

/--
@isnad1 id=mem.2h5v.s7.3827a7063c44 from=translated src=- shape=c5eec744 vocab=5b1c7f2d
-/
theorem add_mem (U : GradedSubmodule V) {v w : V} (hv : v ∈ U) (hw : w ∈ U) : v + w ∈ U :=
  U.toSubmodule.add_mem hv hw

/--
@isnad1 id=mem.2h5v.s7.38261d247d9b from=translated src=- shape=c5eec744 vocab=ed792e0a
-/
theorem sub_mem (U : GradedSubmodule V) {v w : V} (hv : v ∈ U) (hw : w ∈ U) : v - w ∈ U :=
  U.toSubmodule.sub_mem hv hw

/--
@isnad1 id=mem.1h5v.s7.d1255b530aef from=translated src=- shape=64b0c8a0 vocab=e0bbb983
-/
theorem smul_mem (U : GradedSubmodule V) (r : k) {v : V} (hv : v ∈ U) : r • v ∈ U :=
  U.toSubmodule.smul_mem r hv

/--
@isnad1 id=mem.1h5v.s6.8803ed8894f2 from=translated src=- shape=be2527b4 vocab=dd2c87d1
-/
theorem zsmul_mem (U : GradedSubmodule V) (n : ℤ) {v : V} (hv : v ∈ U) : n • v ∈ U :=
  U.toSubmodule.smul_of_tower_mem n hv

/--
@isnad1 id=mem.1h5v.s7.ee110d1c7468 from=translated src=- shape=1f00b4e4 vocab=b902aad3
-/
theorem proj_mem (U : GradedSubmodule V) (q : ZMod 2) {v : V} (hv : v ∈ U) : V.proj q v ∈ U := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [proj_zero, LinearMap.sub_apply, LinearMap.id_apply]; exact U.sub_mem hv (U.odd_mem v hv)
  · rw [proj_one]; exact U.odd_mem v hv

end GradedSubmodule

section Quot

/-- The quotient of a superspace by a graded submodule.-/
def quot (V : SVec k) (U : GradedSubmodule V) : SVec k where
  carrier := V ⧸ U.toSubmodule
  odd := U.toSubmodule.mapQ U.toSubmodule V.odd fun v hv => U.odd_mem v hv
  odd_comp_odd := by
    refine Submodule.linearMap_qext _ ?_
    ext v
    simp [Submodule.mapQ_apply, odd_apply_odd]

variable (V : SVec k) (U : GradedSubmodule V)

/-- The class of a vector in the quotient superspace.-/
def quotMkFun (v : V) : quot V U := Submodule.Quotient.mk v

/-- The quotient map, as a morphism of `SVec k`.-/
def quotMk : V ⟶ quot V U := ofHom U.toSubmodule.mkQ

/--
@isnad1 id=eq.0h4v.s6.6b0b3ff76ace from=translated src=- shape=2409f1ad vocab=a479b310
-/
theorem quotMk_apply (v : V) : quotMk V U v = quotMkFun V U v := rfl

/--
@isnad1 id=surjecti.0h3v.s5.2f0bfc54ade5 from=translated src=- shape=a67c4c9a vocab=9d07f60f
-/
theorem quotMkFun_surjective : Function.Surjective (quotMkFun V U) :=
  Submodule.mkQ_surjective U.toSubmodule

/--
@isnad1 id=eq.0h5v.s7.33ba6ade16a9 from=translated src=- shape=0780e319 vocab=a12bc53c
-/
theorem quotMkFun_add (v w : V) : quotMkFun V U (v + w) = quotMkFun V U v + quotMkFun V U w := rfl

/--
@isnad1 id=eq.0h5v.s7.e1f8ab35cbec from=translated src=- shape=0780e319 vocab=87e9034f
-/
theorem quotMkFun_sub (v w : V) : quotMkFun V U (v - w) = quotMkFun V U v - quotMkFun V U w := rfl

/--
@isnad1 id=eq.0h5v.s8.b5e30aa7e0cf from=translated src=- shape=5788adaf vocab=e15819f8
-/
theorem quotMkFun_smul (r : k) (v : V) : quotMkFun V U (r • v) = r • quotMkFun V U v := rfl

/--
@isnad1 id=eq.0h5v.s7.3279c7edac25 from=translated src=- shape=ca82d4a1 vocab=de14b5db
-/
theorem quotMkFun_zsmul (n : ℤ) (v : V) : quotMkFun V U (n • v) = n • quotMkFun V U v := rfl

/--
@isnad1 id=eq.0h3v.s7.c29a6cd3956a from=translated src=- shape=521135d9 vocab=93b8dafa
-/
theorem quotMkFun_zero : quotMkFun V U 0 = 0 := rfl

/--
@isnad1 id=iff.0h5v.s6.068d28fdbbf9 from=translated src=- shape=9f1807a1 vocab=30938124
-/
theorem quotMkFun_eq_quotMkFun {v w : V} : quotMkFun V U v = quotMkFun V U w ↔ v - w ∈ U :=
  Submodule.Quotient.eq U.toSubmodule

/--
@isnad1 id=iff.0h4v.s7.8c440d70d2dd from=translated src=- shape=0d56972c vocab=96289c95
-/
theorem quotMkFun_eq_zero {v : V} : quotMkFun V U v = 0 ↔ v ∈ U :=
  Submodule.Quotient.mk_eq_zero U.toSubmodule

/--
@isnad1 id=eq.0h4v.s8.1dfbdccd6f62 from=translated src=- shape=3853be2b vocab=536add46
-/
theorem quot_odd_mk (v : V) : (quot V U).odd (quotMkFun V U v) = quotMkFun V U (V.odd v) := rfl

/--
@isnad1 id=eq.0h5v.s8.2674b0fed162 from=translated src=- shape=9e543e84 vocab=7cfbd5fa
-/
theorem quot_proj_mk (p : ZMod 2) (v : V) :
    (quot V U).proj p (quotMkFun V U v) = quotMkFun V U (V.proj p v) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_zero, proj_zero, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.id_apply, quot_odd_mk, quotMkFun_sub]
  · rw [proj_one, proj_one, quot_odd_mk]

/--
@isnad1 id=mem.0h3v.s8.dc699894e5a1 from=translated src=- shape=aad7b1e5 vocab=95d6af04
-/
theorem quotMk_mem : quotMk V U ∈ parityHom V (quot V U) 0 := by
  intro q
  ext v
  rw [add_zero, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (quot_proj_mk V U q v).symm

/--
@isnad1 id=mem.1h5v.s8.9bd51f00ba12 from=translated src=- shape=c56a7cb8 vocab=13df3853
-/
theorem quotMkFun_mem_part {p : ZMod 2} {v : V} (hv : v ∈ V.part p) :
    quotMkFun V U v ∈ (quot V U).part p := by
  simpa using! apply_mem_part (quotMk_mem V U) (v := v) hv

variable {V U}

/-- Induction on the classes of a quotient superspace.
@isnad1 id=var.0h6v.s5.96101f5f6748 from=translated src=- shape=28647157 vocab=93b8dafa
-/
theorem quot_induction_on {P : quot V U → Prop} (x : quot V U) (h : ∀ v : V, P (quotMkFun V U v)) :
    P x :=
  Submodule.Quotient.induction_on U.toSubmodule x h

variable (V U) in
/-- Linear maps out of a quotient superspace are determined by their values on classes.
@isnad1 id=eq.1h6v.s7.aa2ca6e77d79 from=translated src=- shape=e6339230 vocab=844bfbc1
-/
theorem quot_hom_ext {W : SVec k} {f g : quot V U ⟶ W}
    (h : ∀ v : V, f (quotMkFun V U v) = g (quotMkFun V U v)) : f = g :=
  hom_ext fun x => quot_induction_on (P := fun x => f x = g x) x h

end Quot

/-! ## Descended maps -/

section QuotMap

variable {V W X : SVec k} {U : GradedSubmodule V} {U' : GradedSubmodule W} {U'' : GradedSubmodule X}

/-- A linear map carrying `U` into `U'` descends to the quotients.-/
def quotMap (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') : quot V U ⟶ quot W U' :=
  ofHom (U.toSubmodule.mapQ U'.toSubmodule (toLinearMap f) fun v hv => hf v hv)

/--
@isnad1 id=eq.1h7v.s8.f4959ac787d6 from=translated src=- shape=d543ae16 vocab=0ca4f9f2
-/
@[simp] theorem quotMap_mk (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (v : V) :
    quotMap f hf (quotMkFun V U v) = quotMkFun W U' (f v) :=
  rfl

/--
@isnad1 id=eq.1h6v.s7.2ef2300f7d6a from=translated src=- shape=f093dd5f vocab=fbc9abbb
-/
theorem quotMk_comp_quotMap (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    quotMk V U ≫ quotMap f hf = f ≫ quotMk W U' := rfl

/--
@isnad1 id=eq.0h3v.s6.7e630190438f from=translated src=- shape=7b235d44 vocab=a89bba6d
-/
theorem quotMap_id : quotMap (U := U) (U' := U) (𝟙 V) (fun _ hv => hv) = 𝟙 (quot V U) :=
  quot_hom_ext V U fun _ => rfl

/--
@isnad1 id=eq.2h9v.s8.4d9a2e8b2a62 from=translated src=- shape=01646b63 vocab=fa729a8d
-/
theorem quotMap_comp (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (g : W ⟶ X)
    (hg : ∀ w ∈ U', g w ∈ U'') :
    quotMap (U := U) (U' := U'') (f ≫ g) (fun v hv => hg _ (hf v hv)) =
      quotMap f hf ≫ quotMap g hg :=
  quot_hom_ext V U fun _ => rfl

/--
@isnad1 id=eq.2h7v.s9.a0497d084c26 from=translated src=- shape=421f5ee6 vocab=1f7cd828
-/
theorem quotMap_add (f g : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (hg : ∀ v ∈ U, g v ∈ U') :
    quotMap (f + g) (fun v hv => U'.add_mem (hf v hv) (hg v hv)) = quotMap f hf + quotMap g hg :=
  quot_hom_ext V U fun _ => rfl

/--
@isnad1 id=eq.1h7v.s10.52a476909a78 from=translated src=- shape=47677cf7 vocab=ab4686b9
-/
theorem quotMap_smul (r : k) (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    quotMap (r • f) (fun v hv => U'.smul_mem r (hf v hv)) = r • quotMap f hf :=
  quot_hom_ext V U fun _ => rfl

/--
@isnad1 id=eq.2h7v.s8.c81e87ac246b from=translated src=- shape=b9ee9755 vocab=a8caa520
-/
theorem quotMap_congr {f g : V ⟶ W} (h : f = g) (hf : ∀ v ∈ U, f v ∈ U') :
    quotMap f hf = quotMap g (h ▸ hf) := by
  subst h; rfl

/-- The parity components of a map carrying `U` into `U'` carry `U` into `U'`.
@isnad1 id=mem.2h8v.s9.4e5eb55751ec from=translated src=- shape=e1b19946 vocab=08de7302
-/
theorem homProj_mem_of_mem (p : ZMod 2) {f : V ⟶ W} (hf : ∀ v ∈ U, f v ∈ U') :
    ∀ v ∈ U, homProj p f v ∈ U' := fun v hv => by
  rw [homProj_apply]
  exact U'.add_mem (U'.proj_mem _ (hf _ (U.proj_mem 0 hv))) (U'.proj_mem _ (hf _ (U.proj_mem 1 hv)))

/-- A descended map has the parity of the original map.
@isnad1 id=mem.2h7v.s9.0de32c8cadad from=translated src=- shape=dcbc66d1 vocab=e8afa41d
-/
theorem quotMap_mem {p : ZMod 2} {f : V ⟶ W} (hfp : f ∈ parityHom V W p)
    (hf : ∀ v ∈ U, f v ∈ U') : quotMap f hf ∈ parityHom (quot V U) (quot W U') p := by
  intro q
  refine quot_hom_ext V U fun v => ?_
  change quotMap f hf ((quot V U).proj q (quotMkFun V U v)) =
    (quot W U').proj (q + p) (quotMap f hf (quotMkFun V U v))
  rw [quot_proj_mk, quotMap_mk, quotMap_mk, quot_proj_mk, apply_proj_of_mem hfp]

/--
@isnad1 id=eq.1h7v.s10.9166e1858a48 from=translated src=- shape=f22c7fb0 vocab=4a7f811c
-/
theorem homProj_quotMap (p : ZMod 2) (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    homProj p (quotMap f hf) = quotMap (homProj p f) (homProj_mem_of_mem p hf) := by
  have e : f = homProj p f + homProj (p + 1) f := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [zero_add, homProj_add_homProj]
    · rw [zmod2_one_add_one, add_comm, homProj_add_homProj]
  refine homProj_eq_of_add ?_ (quotMap_mem (homProj_mem p f) _)
    (quotMap_mem (homProj_mem (p + 1) f) (homProj_mem_of_mem _ hf))
  rw [← quotMap_add]
  exact quotMap_congr e hf

/--
@isnad1 id=mem.2h8v.s9.e00512223d31 from=translated src=- shape=96a2c054 vocab=9a6853fd
-/
theorem twist_mem_of_mem (p : ZMod 2) {f : V ⟶ W} (hf : ∀ v ∈ U, f v ∈ U') :
    ∀ v ∈ U, twist k p f v ∈ U' := fun v hv => by
  rw [twist_apply, proj_eq_homProj, proj_eq_homProj]
  exact U'.add_mem (homProj_mem_of_mem 0 hf v hv) (U'.smul_mem _ (homProj_mem_of_mem 1 hf v hv))

/--
@isnad1 id=eq.1h7v.s10.0f49bb791807 from=translated src=- shape=3df843f2 vocab=8f03ad65
-/
theorem twist_quotMap (p : ZMod 2) (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    twist k p (quotMap f hf) = quotMap (twist k p f) (twist_mem_of_mem p hf) := by
  rw [twist_apply, proj_eq_homProj, proj_eq_homProj, homProj_quotMap, homProj_quotMap,
    ← quotMap_smul, ← quotMap_add]
  exact (quotMap_congr (by rw [twist_apply, proj_eq_homProj, proj_eq_homProj]) _).symm

end QuotMap

end SVec

end StringDiagrams

end
