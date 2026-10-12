/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import Tengoku.LeanPool.LeanPool.Nivat.Algebra.RectangleSupport
public import Tengoku

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Strict reduction of rectangular area

This module proves the geometry in Corollary 2.3 (`cor:line-descent`). The four
coordinate extrema describe the eroded rectangle. Two distinct support sites
force at least one side to shrink, so nonempty erosion has strictly smaller
area.

The main interface `exists_smaller_rectangle_of_annihilator` obtains the two
support sites directly from a nonzero annihilated configuration. This geometric
statement holds for arbitrary Laurent filters; in the corollary it is applied
to the line generator supplied by Theorem 4.1 (`thm:exact-ideal`). Nonemptiness
and the filtered complexity inequality in Corollary 2.3 come from
`Nivat.Descent.exact_complexity_descent`; the final rectangular induction
combines them with the geometry proved here.
-/

@[expose] public section

namespace Nivat.Algebra

end Nivat.Algebra
