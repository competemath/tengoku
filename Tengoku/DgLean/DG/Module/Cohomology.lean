import Tengoku.Seed.Algebra.Module.GradedModule
import Tengoku.DgLean.DG.Module.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohomology of dg modules

* `DG.cohomology M n`: the `n`-th cohomology group `Hⁿ(M) = Zⁿ(M) / Bⁿ(M)` of a dg abelian group
  `M`, as the quotient of the cocycles `DG.cocycles M n` by the coboundaries `DG.coboundaries M n`.
  `DG.cohomology.mk` is the projection, `DG.cohomology.mkOf hm hd` the class of a cocycle `m`.
* Functoriality: a morphism of dg modules `f : M →ᵈᵍ[A] N` induces
  `DG.cohomology.map f n : cohomology M n →+ cohomology N n`, compatibly with identities,
  composition and addition of morphisms.
* Quasi-isomorphisms: `DG.DGModuleHom.IsQuasiIso f`, closed under composition, with the two
  out of three property.
* `DG.Cohomology M = ⨁ n, cohomology M n`: the total cohomology as a graded abelian group with
  zero differential (a `DGAddCommGroup`).
* For a dg ring `A` and a dg `A`-module `M`, the cohomology `H(M)` is a graded module over the
  graded ring `H(A)`: the graded pieces `Hⁱ(A) × Hʲ(M) → Hⁱ⁺ʲ(M)` are induced by the action
  (`DG.cohomology.smulHom`), giving `DirectSum.Gmodule` data, hence a module structure of
  `H(A) = ⨁ n, cohomology A n` (a graded ring via `DirectSum.GRing`) on `H(M)`; both are dg
  objects with zero differential (`DG.Cohomology.dgRing`, `DG.Cohomology.dgModule`).
* `H` commutes with finite direct sums: `DG.cohomology.prodAddEquiv`.

## Conventions

Gradings are cohomological; see `docs/CONVENTIONS.md`. The sign in the Leibniz rule
`d (a • m) = d a • m + (-1)^{|a|} • (a • d m)` is what makes cocycle times coboundary a
coboundary, so that the action descends to cohomology without any sign.
-/

open scoped DG

open DirectSum

namespace DG

section Cohomology

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M]

/-- The `n`-th cohomology group `Hⁿ(M) = Zⁿ(M) / Bⁿ(M)` of a dg abelian group `M`.-/
def cohomology (M : Type*) [AddCommGroup M] [DGAddCommGroup M] (n : ℤ) : Type _ :=
  cocycles M n ⧸ (coboundaries M n).addSubgroupOf (cocycles M n)

namespace cohomology

variable (M) in
instance instAddCommGroup (n : ℤ) : AddCommGroup (cohomology M n) :=
  QuotientAddGroup.Quotient.addCommGroup _

variable (M) in
/-- The projection of the cocycles onto the cohomology.-/
def mk (n : ℤ) : cocycles M n →+ cohomology M n :=
  QuotientAddGroup.mk' _

variable (M) in
/--
@isnad1 id=surjecti.0h2v.s9.e10a1365a7b1 from=translated src=- shape=2f11d68e vocab=321affad
-/
theorem mk_surjective (n : ℤ) : Function.Surjective (mk M n) :=
  QuotientAddGroup.mk'_surjective _

/--
@isnad1 id=iff.0h3v.s9.354497879d04 from=translated src=- shape=ed805250 vocab=3aa21a8b
-/
theorem mk_eq_zero_iff {n : ℤ} (z : cocycles M n) :
    mk M n z = 0 ↔ (z : M) ∈ coboundaries M n :=
  (QuotientAddGroup.eq_zero_iff z).trans (AddSubgroup.mem_addSubgroupOf)

/--
@isnad1 id=iff.0h4v.s10.a40d59c8ed75 from=translated src=- shape=27c4498c vocab=257b9c49
-/
theorem mk_eq_mk_iff {n : ℤ} (z z' : cocycles M n) :
    mk M n z = mk M n z' ↔ (z : M) - z' ∈ coboundaries M n := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  rfl

/--
@isnad1 id=eq.1h4v.s10.4db3279f47ee from=translated src=- shape=af1e894c vocab=257b9c49
-/
theorem mk_eq_mk_of_sub_mem {n : ℤ} {z z' : cocycles M n}
    (h : (z : M) - z' ∈ coboundaries M n) : mk M n z = mk M n z' :=
  (mk_eq_mk_iff z z').mpr h

/--
@isnad1 id=var.0h5v.s9.aa205216ae91 from=translated src=- shape=7e68b214 vocab=d25a3d21
-/
@[elab_as_elim]
theorem induction_on {n : ℤ} {motive : cohomology M n → Prop} (x : cohomology M n)
    (h : ∀ z : cocycles M n, motive (mk M n z)) : motive x :=
  QuotientAddGroup.induction_on x h

/-- Two additive maps out of `Hⁿ(M)` agreeing on classes of cocycles are equal.
@isnad1 id=eq.1h5v.s9.4883e3c54321 from=translated src=- shape=0bb8363d vocab=db534f6a
-/
@[ext]
theorem addMonoidHom_ext {n : ℤ} {G : Type*} [AddMonoid G] ⦃f g : cohomology M n →+ G⦄
    (h : f.comp (mk M n) = g.comp (mk M n)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext ((coboundaries M n).addSubgroupOf (cocycles M n)) h

/-- The class in `Hⁿ(M)` of a cocycle `m ∈ Mⁿ`, `d m = 0`.-/
def mkOf {n : ℤ} {m : M} (hm : m ∈ grading n) (hd : d m = 0) : cohomology M n :=
  mk M n ⟨m, hm, hd⟩

/--
@isnad1 id=eq.2h3v.s9.d75d6a938fec from=translated src=- shape=a7aaa86d vocab=1f0f953e
-/
theorem mkOf_eq_mk {n : ℤ} {m : M} (hm : m ∈ grading n) (hd : d m = 0) :
    mkOf hm hd = mk M n ⟨m, hm, hd⟩ := rfl

/--
@isnad1 id=iff.2h3v.s7.cc2e62087c73 from=translated src=- shape=87c95bb4 vocab=da2919f3
-/
theorem mkOf_eq_zero_iff {n : ℤ} {m : M} (hm : m ∈ grading n) (hd : d m = 0) :
    mkOf hm hd = 0 ↔ m ∈ coboundaries M n :=
  mk_eq_zero_iff _

/--
@isnad1 id=eq.2h3v.s8.75b5640f832f from=translated src=- shape=adbf509f vocab=142cf25d
-/
theorem mkOf_d {n : ℤ} {m : M} (hm : m ∈ grading (n - 1)) (hd : d (d m) = 0) :
    mkOf (by simpa using d_mem hm) hd = 0 :=
  (mkOf_eq_zero_iff _ _).mpr ⟨m, hm, rfl⟩

/--
@isnad1 id=eq.4h4v.s8.7aa5617054cb from=translated src=- shape=e6a77d32 vocab=9eb1d079
-/
theorem mkOf_add {n : ℤ} {m m' : M} (hm : m ∈ grading n) (hd : d m = 0)
    (hm' : m' ∈ grading n) (hd' : d m' = 0) :
    mkOf (add_mem hm hm') (by rw [d_add, hd, hd', add_zero]) = mkOf hm hd + mkOf hm' hd' :=
  map_add (mk M n) ⟨m, hm, hd⟩ ⟨m', hm', hd'⟩

/--
@isnad1 id=eq.2h3v.s7.552ef9285b30 from=translated src=- shape=2d192bb7 vocab=f5dddd5a
-/
theorem mkOf_neg {n : ℤ} {m : M} (hm : m ∈ grading n) (hd : d m = 0) :
    mkOf (neg_mem hm) (by rw [d_neg, hd, neg_zero]) = -mkOf hm hd :=
  map_neg (mk M n) ⟨m, hm, hd⟩

/--
@isnad1 id=eq.2h4v.s7.e89bd6d23cb2 from=translated src=- shape=65482ea5 vocab=6881a175
-/
theorem mkOf_zsmul {n : ℤ} (k : ℤ) {m : M} (hm : m ∈ grading n) (hd : d m = 0) :
    mkOf (zsmul_mem hm k) (by rw [d_zsmul, hd, smul_zero]) = k • mkOf hm hd :=
  map_zsmul (mk M n) k ⟨m, hm, hd⟩

/-- Classes of cocycles in degrees `n = n'` with the same underlying element are heterogeneously
equal. Used to verify the axioms of the graded structures on cohomology.
@isnad1 id=heq.2h5v.s10.8bacbd90d7f7 from=translated src=- shape=92f717b8 vocab=18fd565b
-/
theorem mk_heq_mk {n n' : ℤ} (h : n = n') {z : cocycles M n} {z' : cocycles M n'}
    (hz : (z : M) = z') : HEq (mk M n z) (mk M n' z') := by
  subst h
  rw [Subtype.ext hz]

/-- Lift an additive map on cocycles vanishing on coboundaries to cohomology.-/
def lift {n : ℤ} {G : Type*} [AddCommGroup G] (φ : cocycles M n →+ G)
    (hφ : ∀ z : cocycles M n, (z : M) ∈ coboundaries M n → φ z = 0) : cohomology M n →+ G :=
  QuotientAddGroup.lift _ φ fun z hz => hφ z (AddSubgroup.mem_addSubgroupOf.mp hz)

/--
@isnad1 id=eq.1h5v.s10.aef5816349ff from=translated src=- shape=63d9d1f2 vocab=56aa0cee
-/
@[simp]
theorem lift_mk {n : ℤ} {G : Type*} [AddCommGroup G] (φ : cocycles M n →+ G)
    (hφ : ∀ z : cocycles M n, (z : M) ∈ coboundaries M n → φ z = 0) (z : cocycles M n) :
    lift φ hφ (mk M n z) = φ z :=
  QuotientAddGroup.lift_mk' _ _ z

end cohomology

end Cohomology

/-! ### Functoriality -/

section Map

variable {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]
  [AddCommGroup P] [DGAddCommGroup P]

namespace cocycles

/--
@isnad1 id=mem.0h3v.s6.3c4eedd75956 from=translated src=- shape=dd17eb39 vocab=98229a56
-/
theorem mem_grading {n : ℤ} (z : cocycles M n) : (z : M) ∈ grading n :=
  z.2.1

/--
@isnad1 id=eq.0h3v.s7.e367bd7f1ce9 from=translated src=- shape=28658712 vocab=5f7e1e3c
-/
theorem d_eq_zero {n : ℤ} (z : cocycles M n) : d (z : M) = 0 :=
  z.2.2

/-- An additive map preserving the gradings and commuting with the differentials restricts to
cocycles.-/
def mapAddMonoidHom (f : M →+ N) (hmem : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n)
    (hd : ∀ m, f (d m) = d (f m)) (n : ℤ) : cocycles M n →+ cocycles N n where
  toFun z := ⟨f z, mem_cocycles.mpr ⟨hmem (mem_grading z), by rw [← hd, d_eq_zero z, map_zero]⟩⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/--
@isnad1 id=eq.2h5v.s10.85f4c17fe308 from=translated src=- shape=7e3ae097 vocab=0b21b552
-/
@[simp]
theorem coe_mapAddMonoidHom_apply (f : M →+ N)
    (hmem : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n)
    (hd : ∀ m, f (d m) = d (f m)) (n : ℤ) (z : cocycles M n) :
    (mapAddMonoidHom f hmem hd n z : N) = f z := rfl

/--
@isnad1 id=mem.3h5v.s10.21291f0f6034 from=translated src=- shape=f1ca2cd5 vocab=1b4458c0
-/
theorem mapAddMonoidHom_mem_coboundaries (f : M →+ N)
    (hmem : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n)
    (hd : ∀ m, f (d m) = d (f m)) (n : ℤ) (z : cocycles M n)
    (hz : (z : M) ∈ coboundaries M n) :
    (mapAddMonoidHom f hmem hd n z : N) ∈ coboundaries N n := by
  obtain ⟨m, hm, hmz⟩ := hz
  exact ⟨f m, hmem hm, by rw [← hd, hmz]; rfl⟩

end cocycles

namespace cohomology

/-- The map on cohomology induced by an additive map preserving the gradings and commuting
with the differentials.-/
def mapAddMonoidHom (f : M →+ N) (hmem : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n)
    (hd : ∀ m, f (d m) = d (f m)) (n : ℤ) : cohomology M n →+ cohomology N n :=
  lift ((mk N n).comp (cocycles.mapAddMonoidHom f hmem hd n)) fun z hz =>
    (mk_eq_zero_iff _).mpr (cocycles.mapAddMonoidHom_mem_coboundaries f hmem hd n z hz)

/--
@isnad1 id=eq.2h5v.s11.16a3a66d4110 from=translated src=- shape=068f9cce vocab=09f1bbe0
-/
@[simp]
theorem mapAddMonoidHom_mk (f : M →+ N)
    (hmem : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n)
    (hd : ∀ m, f (d m) = d (f m)) (n : ℤ) (z : cocycles M n) :
    mapAddMonoidHom f hmem hd n (mk M n z) = mk N n (cocycles.mapAddMonoidHom f hmem hd n z) :=
  lift_mk _ _ z

/--
@isnad1 id=eq.4h5v.s9.1620c86532b2 from=translated src=- shape=30e5a5b6 vocab=14a3e1c1
-/
theorem mapAddMonoidHom_mkOf (f : M →+ N)
    (hmem : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n)
    (hd : ∀ m, f (d m) = d (f m)) {n : ℤ} {m : M} (hm : m ∈ grading n) (hdm : d m = 0) :
    mapAddMonoidHom f hmem hd n (mkOf hm hdm) =
      mkOf (hmem hm) (by rw [← hd, hdm, map_zero]) :=
  mapAddMonoidHom_mk f hmem hd n ⟨m, hm, hdm⟩

section DGModuleHom

variable {A : Type*} [Ring A] [DGAddCommGroup A] [Module A M] [Module A N] [Module A P]

/-- The map `Hⁿ(f) : Hⁿ(M) →+ Hⁿ(N)` induced by a morphism of dg modules `f : M →ᵈᵍ[A] N`.-/
def map (f : M →ᵈᵍ[A] N) (n : ℤ) : cohomology M n →+ cohomology N n :=
  mapAddMonoidHom f.toLinearMap.toAddMonoidHom (fun hm => f.map_mem hm) f.map_d n

/--
@isnad1 id=eq.0h6v.s10.4d856dec56b6 from=translated src=- shape=5a2bd151 vocab=f42b18ee
-/
theorem map_mk (f : M →ᵈᵍ[A] N) (n : ℤ) (z : cocycles M n) :
    map f n (mk M n z) = mk N n ⟨f z, mem_cocycles.mpr ⟨f.map_mem (cocycles.mem_grading z),
      by rw [← f.map_d, cocycles.d_eq_zero z, map_zero]⟩⟩ :=
  mapAddMonoidHom_mk f.toLinearMap.toAddMonoidHom (fun hm => f.map_mem hm) f.map_d n z

/--
@isnad1 id=eq.2h6v.s8.8fe9e9b67e4d from=translated src=- shape=ba2e45cf vocab=db1389e8
-/
@[simp]
theorem map_mkOf (f : M →ᵈᵍ[A] N) {n : ℤ} {m : M} (hm : m ∈ grading n) (hd : d m = 0) :
    map f n (mkOf hm hd) = mkOf (f.map_mem hm) (by rw [← f.map_d, hd, map_zero]) :=
  map_mk f n ⟨m, hm, hd⟩

variable (M) in
/--
@isnad1 id=eq.0h3v.s7.678d8ee4f37d from=translated src=- shape=a500da17 vocab=d5584f6b
-/
@[simp]
theorem map_id (n : ℤ) : map (DGModuleHom.id : M →ᵈᵍ[A] M) n = AddMonoidHom.id _ := by
  ext z
  exact (map_mk _ n z).trans rfl

/--
@isnad1 id=eq.0h7v.s8.fae94310a6ed from=translated src=- shape=a6148a47 vocab=e1b53f8f
-/
theorem map_comp (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) (n : ℤ) :
    map (g.comp f) n = (map g n).comp (map f n) := by
  ext z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_mk]
  rfl

/--
@isnad1 id=eq.0h8v.s9.1471c499f50c from=translated src=- shape=c92f3909 vocab=e494743a
-/
theorem map_comp_apply (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) (n : ℤ) (x : cohomology M n) :
    map (g.comp f) n x = map g n (map f n x) := by
  rw [map_comp]; rfl

variable (M N) in
/--
@isnad1 id=eq.0h4v.s8.08ac9612d723 from=translated src=- shape=ecf78d55 vocab=46472c3e
-/
@[simp]
theorem map_zero (n : ℤ) : map (0 : M →ᵈᵍ[A] N) n = 0 := by
  ext z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_mk, AddMonoidHom.zero_comp,
    AddMonoidHom.zero_apply]
  rw [mk_eq_zero_iff]
  simp only [DGModuleHom.zero_apply]
  exact zero_mem _

/--
@isnad1 id=eq.0h6v.s9.b1b748995b53 from=translated src=- shape=85752ecf vocab=32c475db
-/
theorem map_add (f g : M →ᵈᵍ[A] N) (n : ℤ) : map (f + g) n = map f n + map g n := by
  ext z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_mk, AddMonoidHom.add_comp,
    AddMonoidHom.add_apply, ← _root_.map_add]
  rfl

/--
@isnad1 id=eq.0h5v.s8.cd3613d602f2 from=translated src=- shape=c2c1f039 vocab=c77550c4
-/
theorem map_neg (f : M →ᵈᵍ[A] N) (n : ℤ) : map (-f) n = -map f n := by
  ext z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_mk, AddMonoidHom.neg_comp,
    AddMonoidHom.neg_apply, ← _root_.map_neg]
  rfl

/--
@isnad1 id=eq.0h6v.s9.b696f108246c from=translated src=- shape=85752ecf vocab=5cf75d23
-/
theorem map_sub (f g : M →ᵈᵍ[A] N) (n : ℤ) : map (f - g) n = map f n - map g n := by
  rw [sub_eq_add_neg, map_add, map_neg, sub_eq_add_neg]

/-- `Hⁿ` as an additive map `(M →ᵈᵍ[A] N) →+ (Hⁿ(M) →+ Hⁿ(N))`.-/
def mapAddHom (n : ℤ) : (M →ᵈᵍ[A] N) →+ (cohomology M n →+ cohomology N n) where
  toFun f := map f n
  map_zero' := map_zero M N n
  map_add' f g := map_add f g n

end DGModuleHom

end cohomology

end Map

/-! ### Quasi-isomorphisms -/

namespace DGModuleHom

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

/-- A morphism of dg modules is a quasi-isomorphism if it induces isomorphisms on all
cohomology groups.-/
def IsQuasiIso (f : M →ᵈᵍ[A] N) : Prop :=
  ∀ n : ℤ, Function.Bijective (cohomology.map f n)

/--
@isnad1 id=isquasii.0h2v.s5.5816accb1539 from=translated src=- shape=b45d53b5 vocab=bfd6b16c
-/
theorem isQuasiIso_id : IsQuasiIso (DGModuleHom.id : M →ᵈᵍ[A] M) := fun n => by
  rw [cohomology.map_id]
  exact Function.bijective_id

/--
@isnad1 id=isquasii.2h6v.s7.437186ec9dee from=translated src=- shape=56cc4cbf vocab=73fa15c1
-/
theorem IsQuasiIso.comp {g : N →ᵈᵍ[A] P} {f : M →ᵈᵍ[A] N} (hg : IsQuasiIso g)
    (hf : IsQuasiIso f) : IsQuasiIso (g.comp f) := fun n => by
  rw [cohomology.map_comp, AddMonoidHom.coe_comp]
  exact (hg n).comp (hf n)

/-- Two out of three: if `g ∘ f` and `g` are quasi-isomorphisms, so is `f`.
@isnad1 id=isquasii.2h6v.s7.1a2cbed3749a from=translated src=- shape=5429ac39 vocab=73fa15c1
-/
theorem IsQuasiIso.of_comp_left {g : N →ᵈᵍ[A] P} {f : M →ᵈᵍ[A] N} (hgf : IsQuasiIso (g.comp f))
    (hg : IsQuasiIso g) : IsQuasiIso f := fun n => by
  have h := hgf n
  rw [cohomology.map_comp, AddMonoidHom.coe_comp] at h
  exact ((hg n).of_comp_iff' _).mp h

/-- Two out of three: if `g ∘ f` and `f` are quasi-isomorphisms, so is `g`.
@isnad1 id=isquasii.2h6v.s7.48ef2024a367 from=translated src=- shape=8d840d21 vocab=73fa15c1
-/
theorem IsQuasiIso.of_comp_right {g : N →ᵈᵍ[A] P} {f : M →ᵈᵍ[A] N} (hgf : IsQuasiIso (g.comp f))
    (hf : IsQuasiIso f) : IsQuasiIso g := fun n => by
  have h := hgf n
  rw [cohomology.map_comp, AddMonoidHom.coe_comp] at h
  exact (Function.Bijective.of_comp_iff _ (hf n)).mp h

end DGModuleHom

/-! ### The total cohomology as a graded abelian group -/

section Graded

/-- The canonical internal grading of an external direct sum `⨁ i, β i`: the `i`-th piece is the
range of `DirectSum.of β i`.-/
@[instance_reducible]
def ofRangeDecomposition {ι : Type*} [DecidableEq ι] (β : ι → Type*) [∀ i, AddCommGroup (β i)] :
    DirectSum.Decomposition (fun i => (DirectSum.of β i).range) where
  decompose' := DirectSum.map fun i => (DirectSum.of β i).rangeRestrict
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      obtain ⟨_, y, rfl⟩ := x
      simp only [DirectSum.coeAddMonoidHom_of, DirectSum.map_of]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (M : Type*) [AddCommGroup M] [DGAddCommGroup M]

/-- The total cohomology `H(M) = ⨁ n, Hⁿ(M)` of a dg abelian group `M`.-/
abbrev Cohomology : Type _ := ⨁ n : ℤ, cohomology M n

/-- `H(M)` is a dg abelian group with zero differential, graded by cohomological degree.-/
instance Cohomology.instDGAddCommGroup : DGAddCommGroup (Cohomology M) where
  grading n := (DirectSum.of (fun n => cohomology M n) n).range
  decomposition := ofRangeDecomposition _
  d := 0
  d_mem' _ := zero_mem _
  d_d' _ := rfl

namespace Cohomology

/--
@isnad1 id=eq.0h2v.s8.03ec29fd9c43 from=translated src=- shape=c1618996 vocab=d26aa2e7
-/
@[simp]
theorem d_apply (x : Cohomology M) : d x = 0 := rfl

variable {M}

/--
@isnad1 id=iff.0h3v.s8.317d49e5e08b from=translated src=- shape=1651bc9e vocab=bb0e0f05
-/
theorem mem_grading_iff {n : ℤ} {x : Cohomology M} :
    x ∈ grading n ↔ ∃ y : cohomology M n, DirectSum.of (fun n => cohomology M n) n y = x :=
  Iff.rfl

/--
@isnad1 id=mem.0h3v.s8.7cd8f1d18013 from=translated src=- shape=505a6e25 vocab=bb0e0f05
-/
theorem of_mem_grading (n : ℤ) (y : cohomology M n) :
    DirectSum.of (fun n => cohomology M n) n y ∈ grading (M := Cohomology M) n :=
  ⟨y, rfl⟩

end Cohomology

end Graded

/-! ### The graded `H(A)`-module structure on `H(M)` -/

section Module

variable {A : Type*} [Ring A] [DGAddCommGroup A]
variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

namespace cocycles

/-- The action of cocycles on cocycles: `Zⁱ(A) × Zʲ(M) → Zⁱ⁺ʲ(M)`, `(a, m) ↦ a • m`.-/
def smulHom (i j : ℤ) : cocycles A i →+ cocycles M j →+ cocycles M (i + j) where
  toFun a :=
    { toFun := fun m => ⟨(a : A) • (m : M), mem_cocycles.mpr
        ⟨smul_mem_grading (mem_grading a) (mem_grading m), by
          rw [d_smul_of_d_eq_zero (mem_grading a) (d_eq_zero a), d_eq_zero m, smul_zero,
            smul_zero]⟩⟩
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [smul_add] }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_smul]

/--
@isnad1 id=eq.0h6v.s12.8e63e4d90a50 from=translated src=- shape=1422c3dc vocab=d7d51ee5
-/
@[simp]
theorem coe_smulHom_apply {i j : ℤ} (a : cocycles A i) (m : cocycles M j) :
    (smulHom i j a m : M) = (a : A) • (m : M) := rfl

/-- A cocycle times a coboundary is a coboundary.
@isnad1 id=mem.1h6v.s12.bf7f40c80609 from=translated src=- shape=d90daea6 vocab=6e4d8da0
-/
theorem smulHom_mem_coboundaries_of_right {i j : ℤ} (a : cocycles A i) (m : cocycles M j)
    (hm : (m : M) ∈ coboundaries M j) : (smulHom i j a m : M) ∈ coboundaries M (i + j) := by
  obtain ⟨m', hm', hd⟩ := hm
  refine ⟨koszulSign i • ((a : A) • m'), ?_, ?_⟩
  · rw [Units.smul_def, Int.add_sub_assoc]
    exact zsmul_mem (smul_mem_grading (mem_grading a) hm') _
  · rw [d_units_smul, d_smul_of_d_eq_zero (mem_grading a) (d_eq_zero a), smul_smul,
      Int.units_mul_self, one_smul, coe_smulHom_apply, hd]

/-- A coboundary times a cocycle is a coboundary.
@isnad1 id=mem.1h6v.s12.9dda1afbde2d from=translated src=- shape=96a623de vocab=6e4d8da0
-/
theorem smulHom_mem_coboundaries_of_left {i j : ℤ} (a : cocycles A i)
    (ha : (a : A) ∈ coboundaries A i) (m : cocycles M j) :
    (smulHom i j a m : M) ∈ coboundaries M (i + j) := by
  obtain ⟨a', ha', hd⟩ := ha
  refine ⟨a' • (m : M), ?_, ?_⟩
  · rw [show i + j - 1 = i - 1 + j by omega]
    exact smul_mem_grading ha' (mem_grading m)
  · rw [coe_smulHom_apply, d_smul ha', d_eq_zero m, smul_zero, smul_zero, add_zero, hd]

end cocycles

namespace cohomology

/-- The action `Hⁱ(A) × Hʲ(M) → Hⁱ⁺ʲ(M)` induced by the action of `A` on `M`.-/
def smulHom (i j : ℤ) : cohomology A i →+ cohomology M j →+ cohomology M (i + j) :=
  lift
    { toFun := fun a => lift ((mk M (i + j)).comp (cocycles.smulHom i j a)) fun m hm =>
        (mk_eq_zero_iff _).mpr (cocycles.smulHom_mem_coboundaries_of_right a m hm)
      map_zero' := by ext m; simp
      map_add' := fun a b => by ext m; simp }
    fun a ha => by
      ext m
      exact (mk_eq_zero_iff _).mpr (cocycles.smulHom_mem_coboundaries_of_left a ha m)

/--
@isnad1 id=eq.0h6v.s13.7537eef12bf9 from=translated src=- shape=f3adde76 vocab=e7f82115
-/
@[simp]
theorem smulHom_mk_mk {i j : ℤ} (a : cocycles A i) (m : cocycles M j) :
    smulHom i j (mk A i a) (mk M j m) = mk M (i + j) (cocycles.smulHom i j a m) := by
  simp [smulHom]

end cohomology

namespace Cohomology

open GradedMonoid

variable [DGRing A]

/-- The graded multiplication on `H(A)`, induced by the multiplication of cocycles.-/
instance gmul : GMul (fun n => cohomology A n) where
  mul a b := cohomology.smulHom _ _ a b

/-- The unit of `H(A)`: the class of `1`.-/
instance gone : GOne (fun n => cohomology A n) where
  one := cohomology.mkOf one_mem_grading d_one

/--
@isnad1 id=eq.0h5v.s13.7f2d136114ff from=translated src=- shape=bd59f1e4 vocab=35d3ab0b
-/
theorem mk_mul_mk {i j : ℤ} (a : cocycles A i) (b : cocycles A j) :
    GMul.mul (cohomology.mk A i a) (cohomology.mk A j b) =
      cohomology.mk A (i + j) (cocycles.smulHom i j a b) :=
  cohomology.smulHom_mk_mk a b

/--
@isnad1 id=eq.0h1v.s9.b8e50c7f4d25 from=translated src=- shape=163ce620 vocab=53e6124d
-/
theorem one_def : (GOne.one : cohomology A 0) = cohomology.mk A 0 ⟨1, one_mem_grading, d_one⟩ :=
  rfl

/-- `H(A)` is a graded monoid.-/
instance gmonoid : GMonoid (fun n => cohomology A n) :=
  { gmul, gone with
    one_mul := fun ⟨i, a⟩ => by
      obtain ⟨a, rfl⟩ := cohomology.mk_surjective A i a
      refine Sigma.ext (zero_add i) ?_
      change HEq (GMul.mul (GOne.one : cohomology A 0) (cohomology.mk A i a)) _
      rw [one_def, mk_mul_mk]
      exact cohomology.mk_heq_mk (zero_add i) (one_mul _)
    mul_one := fun ⟨i, a⟩ => by
      obtain ⟨a, rfl⟩ := cohomology.mk_surjective A i a
      refine Sigma.ext (add_zero i) ?_
      change HEq (GMul.mul (cohomology.mk A i a) (GOne.one : cohomology A 0)) _
      rw [one_def, mk_mul_mk]
      exact cohomology.mk_heq_mk (add_zero i) (mul_one _)
    mul_assoc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
      obtain ⟨a, rfl⟩ := cohomology.mk_surjective A i a
      obtain ⟨b, rfl⟩ := cohomology.mk_surjective A j b
      obtain ⟨c, rfl⟩ := cohomology.mk_surjective A k c
      refine Sigma.ext (add_assoc i j k) ?_
      change HEq (GMul.mul (GMul.mul (cohomology.mk A i a) (cohomology.mk A j b))
        (cohomology.mk A k c)) (GMul.mul (cohomology.mk A i a)
        (GMul.mul (cohomology.mk A j b) (cohomology.mk A k c)))
      rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk]
      exact cohomology.mk_heq_mk (add_assoc i j k) (mul_assoc _ _ _) }

/-- `H(A)` is a graded semiring (`DirectSum.GSemiring`), so that `⨁ n, Hⁿ(A)` is a semiring.-/
instance gsemiring : DirectSum.GSemiring (fun n => cohomology A n) :=
  { gmonoid with
    mul_zero := fun a => map_zero (cohomology.smulHom _ _ a)
    zero_mul := fun b => by
      change cohomology.smulHom _ _ 0 b = 0
      rw [map_zero]; rfl
    mul_add := fun a b c => map_add (cohomology.smulHom _ _ a) b c
    add_mul := fun a b c => by
      change cohomology.smulHom _ _ (a + b) c = _
      rw [map_add]; rfl
    natCast := fun n => n • (GOne.one : cohomology A 0)
    natCast_zero := zero_nsmul _
    natCast_succ := fun n => succ_nsmul _ n }

/-- `H(A)` is a graded ring (`DirectSum.GRing`), so that `⨁ n, Hⁿ(A)` is a ring.-/
instance gring : DirectSum.GRing (fun n => cohomology A n) :=
  { gsemiring with
    intCast := fun n => n • (GOne.one : cohomology A 0)
    intCast_ofNat := fun n => natCast_zsmul _ n
    intCast_negSucc_ofNat := fun n => negSucc_zsmul _ n }

/-- The ring structure on the total cohomology `H(A) = ⨁ n, Hⁿ(A)` of a dg ring.-/
instance ring : Ring (Cohomology A) :=
  DirectSum.ring _

/--
@isnad1 id=eq.0h5v.s12.5858e28b3ca3 from=translated src=- shape=73f1ba18 vocab=68b8a667
-/
theorem of_mul_of {i j : ℤ} (a : cohomology A i) (b : cohomology A j) :
    (DirectSum.of (fun n => cohomology A n) i a * DirectSum.of (fun n => cohomology A n) j b :
      Cohomology A) = DirectSum.of (fun n => cohomology A n) (i + j) (cohomology.smulHom i j a b) :=
  DirectSum.of_mul_of a b

/--
@isnad1 id=eq.0h1v.s9.f4cebef5b533 from=translated src=- shape=8e9cd778 vocab=e423f2ac
-/
theorem one_eq : (1 : Cohomology A) = DirectSum.of (fun n => cohomology A n) 0 GOne.one :=
  rfl

/-- `H(A)` is a dg ring with zero differential.
@isnad1 id=dgring.0h1v.s5.c11f088bca63 from=translated src=- shape=7f51ae2a vocab=82466b18
-/
instance dgRing : DGRing (Cohomology A) where
  one_mem := ⟨GOne.one, rfl⟩
  mul_mem _ _ _ _ ha hb := by
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨_, (DirectSum.of_mul_of a b).symm⟩
  d_mul' _ _ := by simp

/-- `H(M)` is a graded module over the graded ring `H(A)` (`DirectSum.Gmodule`), so that
`⨁ n, Hⁿ(M)` is a module over `⨁ n, Hⁿ(A)`.-/
instance gmodule : DirectSum.Gmodule (fun n => cohomology A n) (fun n => cohomology M n) where
  smul a m := cohomology.smulHom _ _ a m
  one_smul := fun ⟨j, m⟩ => by
    obtain ⟨m, rfl⟩ := cohomology.mk_surjective M j m
    refine Sigma.ext (zero_add j) ?_
    change HEq (cohomology.smulHom 0 j (GOne.one : cohomology A 0) (cohomology.mk M j m)) _
    rw [one_def, cohomology.smulHom_mk_mk]
    exact cohomology.mk_heq_mk (zero_add j) (one_smul _ _)
  mul_smul := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, m⟩ => by
    obtain ⟨a, rfl⟩ := cohomology.mk_surjective A i a
    obtain ⟨b, rfl⟩ := cohomology.mk_surjective A j b
    obtain ⟨m, rfl⟩ := cohomology.mk_surjective M k m
    refine Sigma.ext (add_assoc i j k) ?_
    change HEq (cohomology.smulHom (i + j) k (GMul.mul (cohomology.mk A i a) (cohomology.mk A j b))
      (cohomology.mk M k m)) (cohomology.smulHom i (j + k) (cohomology.mk A i a)
      (cohomology.smulHom j k (cohomology.mk A j b) (cohomology.mk M k m)))
    rw [mk_mul_mk, cohomology.smulHom_mk_mk, cohomology.smulHom_mk_mk, cohomology.smulHom_mk_mk]
    exact cohomology.mk_heq_mk (add_assoc i j k) (mul_smul _ _ _)
  smul_add a := map_add (cohomology.smulHom _ _ a)
  smul_zero a := map_zero (cohomology.smulHom _ _ a)
  add_smul a b m := by
    change cohomology.smulHom _ _ (a + b) m = _
    rw [map_add]; rfl
  zero_smul m := by
    change cohomology.smulHom _ _ 0 m = 0
    rw [map_zero]; rfl

/-- The module structure of the total cohomology `H(A)` on `H(M)`.-/
instance module : Module (Cohomology A) (Cohomology M) :=
  DirectSum.Gmodule.module _ _

/--
@isnad1 id=eq.0h6v.s11.fbf49d25abe5 from=translated src=- shape=f0bc8e28 vocab=26fe390c
-/
theorem of_smul_of {i j : ℤ} (a : cohomology A i) (m : cohomology M j) :
    (DirectSum.of (fun n => cohomology A n) i a • DirectSum.of (fun n => cohomology M n) j m :
      Cohomology M) = DirectSum.of (fun n => cohomology M n) (i + j) (cohomology.smulHom i j a m) :=
  DirectSum.Gmodule.of_smul_of _ _ a m

end Cohomology

end Module

/-! ### Finite direct sums -/

section Prod

variable (M N : Type*) [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]

namespace cohomology

set_option backward.isDefEq.respectTransparency false in
/-- Cohomology commutes with finite direct sums: `Hⁿ(M × N) ≃+ Hⁿ(M) × Hⁿ(N)`, induced by the
projections.-/
def prodAddEquiv (n : ℤ) : cohomology (M × N) n ≃+ cohomology M n × cohomology N n where
  toFun := (mapAddMonoidHom (AddMonoidHom.fst M N) (fun h => (Prod.mem_grading.mp h).1)
      (fun _ => rfl) n).prod
    (mapAddMonoidHom (AddMonoidHom.snd M N) (fun h => (Prod.mem_grading.mp h).2)
      (fun _ => rfl) n)
  invFun := (mapAddMonoidHom (AddMonoidHom.inl M N) (fun h => Prod.mem_grading.mpr ⟨h, zero_mem _⟩)
      (fun _ => by ext <;> simp) n).coprod
    (mapAddMonoidHom (AddMonoidHom.inr M N) (fun h => Prod.mem_grading.mpr ⟨zero_mem _, h⟩)
      (fun _ => by ext <;> simp) n)
  left_inv x := by
    induction x using cohomology.induction_on with
    | h z =>
      simp only [AddMonoidHom.prod_apply, mapAddMonoidHom_mk, AddMonoidHom.coprod_apply]
      rw [← _root_.map_add]
      congr 1
      ext <;> simp
  right_inv := by
    rintro ⟨x, y⟩
    induction x using cohomology.induction_on with | h z => ?_
    induction y using cohomology.induction_on with | h w => ?_
    rw [AddMonoidHom.coprod_apply, mapAddMonoidHom_mk, mapAddMonoidHom_mk, ← _root_.map_add,
      AddMonoidHom.prod_apply, mapAddMonoidHom_mk, mapAddMonoidHom_mk]
    refine Prod.ext (congrArg (mk M n) ?_) (congrArg (mk N n) ?_) <;> ext <;> simp
  map_add' := _root_.map_add _

variable {M N}

variable {A : Type*} [Ring A] [DGAddCommGroup A] [Module A M] [Module A N]

end cohomology

end Prod

end DG
