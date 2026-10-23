/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.SourceServiceDisclosure
import Vegas.Game.SourceServiceMenu
import Vegas.Pending.ReactiveUnusableBinding
import Vegas.Game.ServiceRoster
import Vegas.Game.SourceServiceBoundary
import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceStateKernel
import Vegas.Game.SourceServiceTimedPolicy
import Vegas.Pending.ReactiveBoundedValues
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Game.SourceServicePrefixSupport
import Interaction.ReactiveRoundReachability
import Vegas.Game.RevealServicePrefix
import Vegas.Pending.ReactiveOpeningSettlement
import Vegas.Game.SourceInformation
import Vegas.Pending.ReactiveResolutionEvidence
import Vegas.Game.RevealServiceRosterContinuation
import Vegas.Game.ServiceRosterEvaluation
import Interaction.ReactiveRestrictedContinuation
import GameTheoryExtensions.Math.Probability.Support
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning

/-! # Initialized source laws of the full native service

The actual service prefix is read into the existing source protocol. Its
transition law is derived on every supported prefix, including correlated
initial types, dynamic binding catalogues and retained private traffic.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
theorem decodeSourcePrefix?_terminal_readout
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : SourceProgram.History Player L) :
    (decodeSourcePrefix? program refs registry revelations outputs (eventCount program)
      store history).bind (ProtocolState.readout program) =
        decodeState? (terminalRefsWith program refs outputs) store := by
  induction program with
  | ret payoffs =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith]
      cases decodeState? refs store <;> rfl
  | sample name fresh distribution next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _
  | commit name owner fresh guard next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _
  | reveal published owner name fresh binding unresolved next ih =>
      simp only [eventCount, decodeSourcePrefix?, terminalRefsWith, Option.bind_map]
      exact ih _ _ _ _

omit [Fintype Player] in
theorem serviceSourcePrefix?_terminal_readout
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (config : (serviceGraph setup mode).Config) :
    setup.protocolReadout (serviceSourcePrefix? setup mode (eventCount setup.program) config) =
      decodeState? (terminalRefs setup.program) config.store :=
  decodeSourcePrefix?_terminal_readout setup.program _ _ _ _ _ _

omit [Fintype Player] in
theorem sourceServicePrefix?_terminal_readout
    (setup : Setup (Player := Player) (L := L)) (config : (graph setup).Config) :
    setup.protocolReadout (sourceServicePrefix? setup (eventCount setup.program) config) =
      decodeState? (terminalRefs setup.program) config.store :=
  serviceSourcePrefix?_terminal_readout setup .sequential config

end Vegas
