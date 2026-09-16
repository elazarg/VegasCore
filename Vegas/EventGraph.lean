/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Order
import Vegas.EventGraph.Code
import Vegas.EventGraph.Basic
import Vegas.EventGraph.Execution
import Vegas.EventGraph.Commutation
import Vegas.EventGraph.CommutationRecall
import Vegas.EventGraph.Information
import Vegas.EventGraph.Barriers
import Vegas.EventGraph.BarrierInformation
import Vegas.EventGraph.Recall
import Vegas.EventGraph.Semantics
import Vegas.EventGraph.Canonical

/-! # Dependency-driven typed events

Finite dependency cuts and failure-aware event code for asynchronous graph
execution. Source and pending-message strategic certificates are separate
obligations.
-/
