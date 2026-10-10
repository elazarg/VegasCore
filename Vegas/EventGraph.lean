/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.BindingRefinement
import Vegas.EventGraph.Order
import Vegas.EventGraph.ResolutionFields
import Vegas.EventGraph.Sequential
import Vegas.EventGraph.SequentialLaw
import Vegas.EventGraph.ExecutionMode
import Vegas.EventGraph.Code
import Vegas.EventGraph.Basic
import Vegas.EventGraph.Execution
import Vegas.EventGraph.ForeignCompletionSequence
import Vegas.EventGraph.Commutation
import Vegas.EventGraph.CommutationRecall
import Vegas.EventGraph.KernelCommutation
import Vegas.EventGraph.Information
import Vegas.EventGraph.CommitmentEvidence
import Vegas.EventGraph.PrivateInputs
import Vegas.EventGraph.ObservationStep
import Vegas.EventGraph.Validation
import Vegas.EventGraph.Barriers
import Vegas.EventGraph.BarrierInformation
import Vegas.EventGraph.BarrierBlocks
import Vegas.EventGraph.RevealRelaxation
import Vegas.EventGraph.RevealRelaxedScheduling
import Vegas.EventGraph.Recall
import Vegas.EventGraph.Semantics
import Vegas.EventGraph.NormalizedPolicy
import Vegas.EventGraph.PolicyCommutation
import Vegas.EventGraph.StateCongruence
import Vegas.EventGraph.SchedulingLaw
import Vegas.EventGraph.SchedulerErasure
import Vegas.EventGraph.SchedulerReplay
import Vegas.EventGraph.SchedulerReplayLaw
import Vegas.EventGraph.SchedulerProtocol
import Vegas.EventGraph.SchedulerPredraw
import Vegas.EventGraph.SchedulerDeviation
import Vegas.EventGraph.SchedulerMixture
import Vegas.EventGraph.Canonical
import Vegas.EventGraph.CanonicalNormalization
import Vegas.EventGraph.CanonicalStep
import Vegas.EventGraph.PolicyCongruence
import Vegas.EventGraph.ResolutionProvenance
import Vegas.EventGraph.PayoffTransport

import Vegas.EventGraph.ForeignCompletionEvaluation

import Vegas.EventGraph.CompletedOutputAgreement

/-! # Dependency-driven typed events

Finite dependency cuts and failure-aware event code for asynchronous graph
execution. Source and pending-message strategic certificates are separate
obligations.
-/
