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

/-- Root audit for fixed branch (4, 4).
@isnad1 id=eq.0h0v.s5.c8cd27cde96f from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_04 :
    branchClaimRootValidB 4 4 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 14).
@isnad1 id=eq.0h0v.s5.078c5aa83013 from=translated src=- shape=e9e0773c vocab=9555e47e
-/
theorem coverageBranchRoot_6_14 :
    branchClaimRootValidB 6 14 (.search branchClaims6Row14) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 15).
@isnad1 id=eq.0h0v.s5.556d68fad718 from=translated src=- shape=e9e0773c vocab=dd1f6afa
-/
theorem coverageBranchRoot_6_15 :
    branchClaimRootValidB 6 15 (.search branchClaims6Row15) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 14), starting at 0.
@isnad1 id=eq.0h0v.s3.f3c6a9da0db1 from=translated src=- shape=6f582f20 vocab=94437cfe
-/
theorem coverageBranchNodes_6_14_00000 :
    nodeClaimChunkValidB branchClaims6Row14 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 14), starting at 64.
@isnad1 id=eq.0h0v.s3.d285c4ea88d8 from=translated src=- shape=6f582f20 vocab=94437cfe
-/
theorem coverageBranchNodes_6_14_00064 :
    nodeClaimChunkValidB branchClaims6Row14 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 14), starting at 128.
@isnad1 id=eq.0h0v.s3.5156c788e531 from=translated src=- shape=6f582f20 vocab=94437cfe
-/
theorem coverageBranchNodes_6_14_00128 :
    nodeClaimChunkValidB branchClaims6Row14 128 50 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 15), starting at 0.
@isnad1 id=eq.0h0v.s3.8734d763b667 from=translated src=- shape=6f582f20 vocab=ef6c3d63
-/
theorem coverageBranchNodes_6_15_00000 :
    nodeClaimChunkValidB branchClaims6Row15 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
