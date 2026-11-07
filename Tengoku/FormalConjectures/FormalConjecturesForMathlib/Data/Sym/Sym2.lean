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

public section

namespace Sym2
variable {α : Type*} {a : α}

/--
@isnad1 id=eq.0h2v.s4.0ca040034842 from=translated src=- shape=3be29236 vocab=5ed53ff7
-/
@[simp] lemma fst_out_mk_self : (Quot.out s(a, a)).1 = a := by simpa using out_fst_mem s(a, a)
/--
@isnad1 id=eq.0h2v.s4.5207635cff23 from=translated src=- shape=3be29236 vocab=ea4a1424
-/
@[simp] lemma snd_out_mk_self : (Quot.out s(a, a)).2 = a := by simpa using out_snd_mem s(a, a)

end Sym2
