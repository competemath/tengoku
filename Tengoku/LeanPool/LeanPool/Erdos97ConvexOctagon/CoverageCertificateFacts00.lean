/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 0).
@isnad1 id=eq.0h0v.s5.c90b6aa7db40 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_00 :
    branchClaimRootValidB 0 0 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 18).
@isnad1 id=eq.0h0v.s5.9c32ce96c583 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_18 :
    branchClaimRootValidB 4 18 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 4).
@isnad1 id=eq.0h0v.s5.7a293b377560 from=translated src=- shape=e9e0773c vocab=af8306d1
-/
theorem coverageBranchRoot_1_04 :
    branchClaimRootValidB 1 4 (.search branchClaims1Row4) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 5).
@isnad1 id=eq.0h0v.s5.e9846193bc28 from=translated src=- shape=e9e0773c vocab=d8406cf4
-/
theorem coverageBranchRoot_1_05 :
    branchClaimRootValidB 1 5 (.search branchClaims1Row5) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 4), starting at 0.
@isnad1 id=eq.0h0v.s3.68321250af3b from=translated src=- shape=6f582f20 vocab=27aacbb1
-/
theorem coverageBranchNodes_1_04_00000 :
    nodeClaimChunkValidB branchClaims1Row4 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 4), starting at 64.
@isnad1 id=eq.0h0v.s3.814148a399f1 from=translated src=- shape=6f582f20 vocab=27aacbb1
-/
theorem coverageBranchNodes_1_04_00064 :
    nodeClaimChunkValidB branchClaims1Row4 64 38 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 5), starting at 0.
@isnad1 id=eq.0h0v.s3.d7f148614ee7 from=translated src=- shape=6f582f20 vocab=23537ecc
-/
theorem coverageBranchNodes_1_05_00000 :
    nodeClaimChunkValidB branchClaims1Row5 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 5), starting at 64.
@isnad1 id=eq.0h0v.s3.f3f049dfb32a from=translated src=- shape=6f582f20 vocab=23537ecc
-/
theorem coverageBranchNodes_1_05_00064 :
    nodeClaimChunkValidB branchClaims1Row5 64 37 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
