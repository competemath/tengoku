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

/-- Root audit for fixed branch (4, 8).
@isnad1 id=eq.0h0v.s5.d503003b9103 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_08 :
    branchClaimRootValidB 4 8 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 23).
@isnad1 id=eq.0h0v.s5.ed88cc68c9e1 from=translated src=- shape=e9e0773c vocab=f6f1ca7e
-/
theorem coverageBranchRoot_6_23 :
    branchClaimRootValidB 6 23 (.search branchClaims6Row23) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 23), starting at 0.
@isnad1 id=eq.0h0v.s3.2fc65265c4e1 from=translated src=- shape=6f582f20 vocab=157f450b
-/
theorem coverageBranchNodes_6_23_00000 :
    nodeClaimChunkValidB branchClaims6Row23 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 23), starting at 64.
@isnad1 id=eq.0h0v.s3.f051dc16abf8 from=translated src=- shape=6f582f20 vocab=157f450b
-/
theorem coverageBranchNodes_6_23_00064 :
    nodeClaimChunkValidB branchClaims6Row23 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 23), starting at 128.
@isnad1 id=eq.0h0v.s3.550545f963dc from=translated src=- shape=6f582f20 vocab=157f450b
-/
theorem coverageBranchNodes_6_23_00128 :
    nodeClaimChunkValidB branchClaims6Row23 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 23), starting at 192.
@isnad1 id=eq.0h0v.s3.a526e8bc8e63 from=translated src=- shape=6f582f20 vocab=157f450b
-/
theorem coverageBranchNodes_6_23_00192 :
    nodeClaimChunkValidB branchClaims6Row23 192 56 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
