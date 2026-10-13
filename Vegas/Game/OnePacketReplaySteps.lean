/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketReplayWeight

/-! # Matching the initial draw of the intended replay

The native initial law and the intended initial step are both images of the
setup's initial law, through maps that the decoded point inverts: the decoded
point of the native initial state of a setup draw is the entry point of that
draw (`Vegas.decodedPoint_initial`). Both maps are therefore injective, and the
intended initial step gives the decoded initial point the mass the native
initial law gives the initial state (`Vegas.initialMass_eq`), so the initial
draw of every native history matches (`Vegas.replayStepMatches_start`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- The decoded point of the native initial state of a setup draw is the entry
point of that draw. -/
theorem decodedPoint_initial (initial : State L setup.context) :
    decodedPoint setup (EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs initial)).config =
      some (ProtocolState.entry setup.program (setup.initialConfig initial)) :=
  decodedPoint_eq (SourceResidual.initial setup (failureProfile setup.program) initial)

/-- Distinct setup draws have distinct entry points. -/
theorem entry_initialConfig_injective :
    Function.Injective fun initial : State L setup.context =>
      some (ProtocolState.entry setup.program (setup.initialConfig initial)) := by
  intro first second same
  have configs := ProtocolState.entry_injective setup.program (Option.some.inj same)
  exact congrArg Config.state configs

/-- Distinct setup draws have distinct native initial states. -/
theorem nativeInitial_injective :
    Function.Injective fun initial : State L setup.context =>
      EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial) := by
  intro first second same
  apply entry_initialConfig_injective (setup := setup)
  change some _ = some _
  rw [← decodedPoint_initial, ← decodedPoint_initial]
  exact congrArg (fun state : EventGraphRuntime.State (graph setup) =>
    decodedPoint setup state.config) same

/-- **The initial masses agree.** The intended initial step gives the decoded
initial point of a setup draw the mass the native initial law gives its native
initial state. -/
theorem initialMass_eq (initial : State L setup.context) :
    (setup.protocolStep none (fun _ => none)
        (decodedPoint setup (EventGraphRuntime.State.initial (graph := graph setup)
          (setup.eventInputs initial)).config)).toReal =
      (initialLaw setup (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial))).toReal := by
  rw [decodedPoint_initial]
  change ((setup.initialLaw.map fun initial =>
      some (ProtocolState.entry setup.program (setup.initialConfig initial)))
        (some (ProtocolState.entry setup.program (setup.initialConfig initial)))).toReal =
    ((setup.initialLaw.map fun initial => EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs initial)) (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial))).toReal
  rw [pmf_map_apply_of_injective _ entry_initialConfig_injective,
    pmf_map_apply_of_injective _ nativeInitial_injective]

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {horizon : Nat} {scheduler : (application setup leaks).Scheduler}

/-- **The initial draw matches** at every realized native initial
transition. -/
theorem replayStepMatches_start (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (realized : after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      none joint).support) :
    ReplayStepMatches setup leaks assessment who setup.intendedProtocol.initHistory 1 none joint
      after := by
  change after ∈ ((initialLaw setup).map fun state => some
    (⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks) state⟩ :
      (application setup leaks).Control)).support at realized
  obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ realized
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  exact replayStepMatches_initial assessment who _ joint (initialMass_eq initial)

end Vegas
