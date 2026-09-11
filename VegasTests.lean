/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.Language
import VegasTests.CoreFinite
import VegasTests.PendingSource
import VegasTests.PendingExecution
import VegasTests.PendingOutcome
import VegasTests.PendingReplay
import VegasTests.PendingPolicies
import VegasTests.PendingSnapshots
import VegasTests.PendingRelease
import VegasTests.PendingReleaseExamples
import VegasTests.PendingChoiceLock
import VegasTests.PendingWithholding
import VegasTests.PendingWithholdingSource
import VegasTests.PendingTimeout
import VegasTests.PendingTimeoutPolicies
import VegasTests.PendingTimeoutSource
import VegasTests.PendingTimeoutHiding
import VegasTests.SealedCompiler

/-! # Regression tests for the active strict sealed-message tower

The executable test surface follows the same edge as the library: checked
source, event graph, one sealed rule per graph node, and explicit message
execution. Earlier fused application tests are archived outside the build
roots.
-/
