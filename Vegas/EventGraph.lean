/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.BarrierBlocks
import Vegas.EventGraph.BarrierInformation
import Vegas.EventGraph.Barriers
import Vegas.EventGraph.Basic
import Vegas.EventGraph.OwnedStep
import Vegas.EventGraph.BindingRefinement
import Vegas.EventGraph.Canonical
import Vegas.EventGraph.CanonicalNormalization
import Vegas.EventGraph.CanonicalStep
import Vegas.EventGraph.Code
import Vegas.EventGraph.CommitmentEvidence
import Vegas.EventGraph.Commutation
import Vegas.EventGraph.CommutationRecall
import Vegas.EventGraph.CompletedOutputAgreement
import Vegas.EventGraph.ConfigRestriction
import Vegas.EventGraph.Execution
import Vegas.EventGraph.Information
import Vegas.EventGraph.KernelCommutation
import Vegas.EventGraph.NormalizedPolicy
import Vegas.EventGraph.ObservationStep
import Vegas.EventGraph.Order
import Vegas.EventGraph.PolicyCommutation
import Vegas.EventGraph.PolicyCongruence
import Vegas.EventGraph.PrivateInputs
import Vegas.EventGraph.Recall
import Vegas.EventGraph.RelaxedRecall
import Vegas.EventGraph.ResolutionFields
import Vegas.EventGraph.ResolutionProvenance
import Vegas.EventGraph.RevealRelaxation
import Vegas.EventGraph.RevealRelaxedScheduling
import Vegas.EventGraph.SchedulerDeviation
import Vegas.EventGraph.SchedulerErasure
import Vegas.EventGraph.SchedulerMixture
import Vegas.EventGraph.SchedulerPredraw
import Vegas.EventGraph.SchedulerProtocol
import Vegas.EventGraph.SchedulerReplay
import Vegas.EventGraph.SchedulerReplayLaw
import Vegas.EventGraph.SchedulingLaw
import Vegas.EventGraph.Semantics
import Vegas.EventGraph.Sequential
import Vegas.EventGraph.SequentialLaw
import Vegas.EventGraph.StateCongruence
import Vegas.EventGraph.Validation

/-! # Dependency-driven typed events

Finite dependency cuts and failure-aware event code for asynchronous graph
execution. Source and pending-message strategic certificates are separate
obligations.
-/
