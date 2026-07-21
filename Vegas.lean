/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

-- Foundation: expression interface, values, visibility contexts.
import Vegas.Foundation.Basic

-- Core: the VegasCore source language (incl. the simple expression instance
-- and the checked-program boundary).
import Vegas.Core.Basic
import Vegas.Core.FiniteDomain
import Vegas.Core.ExprSimple
import Vegas.Core.Obligations
import Vegas.Core.Scope
import Vegas.Core.Finite
import Vegas.Core.SmallStep
import Vegas.Core.Epistemic
import Vegas.Core.Strategic
import Vegas.Core.Schedule
import Vegas.Core.Noninterference
import Vegas.Core.StrategicNoninterference
import Vegas.Core.Trace
import Vegas.Core.WellFormed

-- Language: surface syntax and lowering to Core.
import Vegas.Language.Nullable
import Vegas.Language.ToCore

-- EventGraph: the source-free graph IR.
import Vegas.EventGraph.Basic
import Vegas.EventGraph.Build
import Vegas.EventGraph.Execution
import Vegas.EventGraph.Confluence
import Vegas.EventGraph.Linearization
import Vegas.EventGraph.VisibleOrder
import Vegas.EventGraph.Fence
import Vegas.EventGraph.FiniteState
import Vegas.EventGraph.Frontier
import Vegas.EventGraph.Batch
import Vegas.EventGraph.Validate

-- Machine: operational machine, adapters, round views, refinement.
import Vegas.Machine.Adapter.RoundView
import Vegas.Machine.KernelGame
import Vegas.Machine.Kuhn
import Vegas.Machine.Refinement
import Vegas.Machine.RefinementKernelGame
import Vegas.Machine.Audited
import Vegas.Machine.MessageInFlight
import Vegas.Machine.MessageSecurity

-- Compile + Frontier: graph compiler and canonical strategic semantics.
import Vegas.Frontier
import Vegas.Compile.SourceBridge
import Vegas.Compile.ValueBridge

-- Presentation + Export: game-theory presentations and export tables.
import Vegas.Presentation
import Vegas.Export

-- Runtime: backend-facing proof interfaces.
import Vegas.Runtime.Codec
import Vegas.Runtime.CodecMachine
import Vegas.Runtime.TraceAdequacy

-- Audit surface: curated definition and theorem indexes.
import Vegas.Spec
import Vegas.Theorems

-- Build-tested end-to-end examples.
import Vegas.Examples

-- Upstream game-theory analysis vocabulary this project reasons with.
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Mixed.MixedExtension

/-!
# Vegas

Build-all root: imports every module in dependency-layer order, plus the upstream
`GameTheory` vocabulary the development reasons with.
-/
