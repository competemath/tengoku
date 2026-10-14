/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 3).
@isnad1 id=eq.0h0v.s5.cecf1a93b8fb from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_03 :
    branchClaimRootValidB 4 3 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 13).
@isnad1 id=eq.0h0v.s5.c89e34107da8 from=translated src=- shape=e9e0773c vocab=b1936de3
-/
theorem coverageBranchRoot_6_13 :
    branchClaimRootValidB 6 13 (.search branchClaims6Row13) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 12), starting at 64.
@isnad1 id=eq.0h0v.s3.125b2af225dc from=translated src=- shape=6f582f20 vocab=738fd675
-/
theorem coverageBranchNodes_6_12_00064 :
    nodeClaimChunkValidB branchClaims6Row12 64 61 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 13), starting at 0.
@isnad1 id=eq.0h0v.s3.362cc6ae46e8 from=translated src=- shape=6f582f20 vocab=bdd43b29
-/
theorem coverageBranchNodes_6_13_00000 :
    nodeClaimChunkValidB branchClaims6Row13 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 13), starting at 64.
@isnad1 id=eq.0h0v.s3.0b67ff0367cb from=translated src=- shape=6f582f20 vocab=bdd43b29
-/
theorem coverageBranchNodes_6_13_00064 :
    nodeClaimChunkValidB branchClaims6Row13 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 13), starting at 128.
@isnad1 id=eq.0h0v.s3.68c0c977e583 from=translated src=- shape=6f582f20 vocab=bdd43b29
-/
theorem coverageBranchNodes_6_13_00128 :
    nodeClaimChunkValidB branchClaims6Row13 128 5 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
