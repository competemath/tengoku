/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 16).
@isnad1 id=eq.0h0v.s5.68fcd7cc688e from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_16 :
    branchClaimRootValidB 3 16 (.patternThree 2) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 29).
@isnad1 id=eq.0h0v.s5.3c21abf71046 from=translated src=- shape=e9e0773c vocab=3cfa984b
-/
theorem coverageBranchRoot_5_29 :
    branchClaimRootValidB 5 29 (.search branchClaims5Row29) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 320.
@isnad1 id=eq.0h0v.s3.3505f62456f4 from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00320 :
    nodeClaimChunkValidB branchClaims5Row28 320 14 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 29), starting at 0.
@isnad1 id=eq.0h0v.s3.ed7627cc8ffa from=translated src=- shape=6f582f20 vocab=a1dc1839
-/
theorem coverageBranchNodes_5_29_00000 :
    nodeClaimChunkValidB branchClaims5Row29 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 29), starting at 64.
@isnad1 id=eq.0h0v.s3.9fa85b3a30d1 from=translated src=- shape=6f582f20 vocab=a1dc1839
-/
theorem coverageBranchNodes_5_29_00064 :
    nodeClaimChunkValidB branchClaims5Row29 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 29), starting at 128.
@isnad1 id=eq.0h0v.s3.f42d68fbfe2a from=translated src=- shape=6f582f20 vocab=a1dc1839
-/
theorem coverageBranchNodes_5_29_00128 :
    nodeClaimChunkValidB branchClaims5Row29 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
