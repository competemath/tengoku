/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku

@[expose] public section

/--
@isnad1 id=eq.2h3v.s4.bdaefb80129f from=translated src=- shape=38418819 vocab=b5a7fabd
-/
theorem Part.get_eq_get {σ : Type*} {a b : Part σ} (ha : a.Dom) (hb : a.get ha ∈ b) : a = b := by
  have hb' : b.Dom := Part.dom_iff_mem.mpr ⟨a.get ha, hb⟩
  rwa [← Part.eq_get_iff_mem hb', Part.eq_iff_of_dom ha hb'] at hb

namespace StateTransition

/--
@isnad1 id=mem.1h3v.s4.906205798f44 from=translated src=- shape=c2eabff1 vocab=5d375997
-/
lemma dom_of_apply_eq_none {σ : Type*} {f : σ → Option σ} {s : σ} (hf : f s = none) :
    s ∈ eval f s := by
  apply PFun.fix_stop
  simp [hf]

/--
@isnad1 id=eq.1h3v.s4.81697b0a2126 from=translated src=- shape=fef46dce vocab=e0046e5b
-/
theorem apply_get_eval {σ : Type*} {f : σ → Option σ} {s : σ} (H : (eval f s).Dom) :
    f ((eval f s).get H) = none := by
  have := Part.get_mem H
  rw [mem_eval] at this
  exact this.right

-- TODO(Paul-Lez): also prove this for `PFun.fix`/golf using the `PFun.fix` API
/--
@isnad1 id=eq.1h3v.s5.794718e46c6e from=translated src=- shape=a9f864e0 vocab=b23a3584
-/
theorem eval_get_eval {σ : Type*} {f : σ → Option σ} {s : σ} (H : (eval f s).Dom) :
    eval f ((eval f s).get H) = eval f s := by
  symm
  apply Part.get_eq_get H (dom_of_apply_eq_none ?_)
  simp [apply_get_eval]

-- TODO(Paul-Lez): also prove this for `PFun.fix`/golf using the `PFun.fix` API
/--
@isnad1 id=eq.1h4v.s5.df2e5a56c7ca from=translated src=- shape=adca586d vocab=72ea0d54
-/
theorem eval_eq_eval {σ : Type*} {f : σ → Option σ} {a a' : σ} (H : f a = some a'):
    eval f a = eval f a' := by
  apply reaches_eval
  apply Relation.ReflTransGen.single
  rw [H]
  rfl

-- TODO(lezeau): this should be generalized to `PFun.fix`
/--
@isnad1 id=iff.0h3v.s5.734fb8cfaf10 from=translated src=- shape=1c174b07 vocab=6ac1a13e
-/
theorem eval_dom_iff {σ : Type*} {f : σ → Option σ} {s : σ} :
    (∃ n, ((Option.bind · f)^[n+1] s) = none) ↔ (eval f s).Dom := by
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun H ↦ ?_⟩
  · induction n generalizing s with
    | zero =>
      rw [zero_add, Function.iterate_one, Option.bind_some] at hn
      simpa [Part.dom_iff_mem] using ⟨s, dom_of_apply_eq_none hn⟩
    | succ n ih =>
      obtain ha | ⟨a', ha'⟩ := (f s).eq_none_or_eq_some
      · simpa [Part.dom_iff_mem] using ⟨s, dom_of_apply_eq_none ha⟩
      · simp_rw [Function.iterate_succ, Function.comp_apply, Option.bind_some] at hn ih
        simp_rw [ha', Option.bind_some] at hn
        have ih := @ih a' ⟨n, hn⟩ hn
        rwa [eval_eq_eval ha']
  · let C (s) : Prop := (eval f s).Dom → ∃ n, (Option.bind · f)^[n+1] s = none
    apply evalInduction (C := C) (a := s) (h := Part.get_mem H) _ H
    intro a ha h HH
    obtain ha | ⟨a', ha'⟩ := (f a).eq_none_or_eq_some
    · use 0
      simp [ha]
    · obtain ⟨n, hn⟩ := h a' ha' (by rwa [← eval_eq_eval ha'])
      use n + 1
      simp only [Function.iterate_succ, Function.comp_apply, Option.bind_some] at hn
      simp [ha', hn]

end StateTransition
