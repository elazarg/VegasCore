module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceClientPolicy
public import Vegas.Game.SourceServiceFirstTurnCompletion
public import Vegas.Compile.EventGraphCanonical
public import Interaction.ReactiveRestrictedContinuation

@[expose] public section

/-! # Ordinary correctness of the bounded message compiler

Actual first-turn clients preserve every observation of the complete typed
state and public default history for every source profile. Their bounded-menu
realization has the same execution law. Comparing with canonical graph execution
identifies the second compiler pass on its compiled graph and policy image.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (service : AsyncServiceSpec Player L)
  (admission : CommitmentInterface service.setup.program)

/-- The bounded clients realize the full canonical graph configuration distribution,
including recorded actions, for the disclosure-normalized compiled profile. -/
theorem firstTurnClientProfile_config_distribution (turns : Nat)
    (source : Profile (service.sourceModel admission).behavioralSignature) :
    (service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.setup.informationDependencies) source)).map
        (fun final => final.state.map (fun control => control.execution.application.config)) =
      ((service.setup.informationGraph.canonicalGame
          (service.setup.initialDistribution.map service.setup.eventInputs)).play
        (compileEventProfile service.setup.program (normalizeDisclosureProfile service.setup.program
          (service.setup.decodeBehavioralProfile admission source)))).map
            (fun terminal => some terminal.val) := by
  let setup := service.setup
  let app := application setup ⟨service.duration⟩ service.leaks
  let original := setup.decodeBehavioralProfile admission source
  let timing := firstTurnTiming setup turns setup.informationDependencies
  let clients := serviceClientPolicy setup setup.informationDependencies service.duration
    service.leaks service.bound turns timing (normalizeDisclosureProfile setup.program original)
  have states := service.rawMenu.run_restrict_eq_roundsFrom
    (initialDistribution setup) service.horizon service.scheduler clients
    (service.rawMenu_admits admission timing source)
  have bounded := congrArg (PMF.map (fun state : app.ProtocolState =>
    state.map fun control => control.execution.application.config)) states
  have physical := congrArg (PMF.map some)
    (sourceServiceClientPolicy_canonicalGraph_config_distribution_eq
    (turns := turns) ⟨service.duration⟩ service.leaks service.scheduler service.delay service.bound
    original service.contract service.timely)
  simp only [PMF.map_comp, Function.comp_def, ReactiveApplication.finished, Option.map_some]
    at bounded physical
  exact bounded.trans physical

/-- Every total observation of the typed terminal state and public defaults has
its exact source law under the actual bounded first-turn clients. -/
theorem firstTurnClientProfile_outcome_distribution {Outcome : Type*}
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature)
    (observe : State L service.setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    (service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.setup.informationDependencies) source)).map
        (fun final => (serviceSourceReadout service.setup service.setup.informationDependencies
          service.duration
          service.leaks final.state).map fun terminal =>
            observe (terminal.state, terminal.defaults)) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map
        (fun terminal => some (observe (terminal.state, terminal.defaults))) := by
  let app := serviceApplication service.setup service.setup.informationDependencies
    service.duration service.leaks
  let original := service.setup.decodeBehavioralProfile admission source
  let clients := serviceClientPolicy service.setup service.setup.informationDependencies
    service.duration service.leaks
    service.bound turns (firstTurnTiming service.setup turns service.setup.informationDependencies)
      (normalizeDisclosureProfile service.setup.program original)
  have states := service.rawMenu.run_restrict_eq_roundsFrom
    (serviceInitialDistribution service.setup service.setup.informationDependencies) service.horizon
    service.scheduler clients (service.rawMenu_admits admission
      (firstTurnTiming service.setup turns service.setup.informationDependencies) source)
  have projected := congrArg (PMF.map (fun final : app.ProtocolState =>
    (serviceSourceReadout service.setup service.setup.informationDependencies service.duration
      service.leaks final).map
      fun terminal => observe (terminal.state, terminal.defaults))) states
  simp only [PMF.map_comp, Function.comp_def] at projected
  exact projected.trans (sourceServiceClientPolicy_source_observation_distribution_eq
    (turns := turns)
    ⟨service.duration⟩ service.leaks service.scheduler service.delay service.bound
    original service.contract service.timely observe)

/-- The bounded ledger clients and the canonical compiled graph have the same
joint law of typed state and public defaults under its asynchronous scheduler. -/
theorem firstTurnClientProfile_graph_distribution {Outcome : Type*}
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature)
    (observe : State L service.setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    (service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.setup.informationDependencies) source)).map
        (fun final => (serviceSourceReadout service.setup service.setup.informationDependencies
          service.duration
          service.leaks final.state).map fun terminal =>
            observe (terminal.state, terminal.defaults)) =
      ((service.setup.informationGraph.canonicalGame
          (service.setup.initialDistribution.map service.setup.eventInputs)).play
        (compileEventProfile service.setup.program
          (service.setup.decodeBehavioralProfile admission source))).map (fun terminal =>
          let final := terminalConfig service.setup.program terminal
          some (observe (final.state, final.defaults))) := by
  rw [service.firstTurnClientProfile_outcome_distribution admission turns source observe]
  have law := congrArg (PMF.map (fun final : Config Player L service.setup.program.terminalCtx =>
    some (observe (final.state, final.defaults))))
      (canonical_setup_distribution service.setup (service.setup.decodeBehavioralProfile admission
        source))
  simpa only [PMF.map_comp, Function.comp_def] using law.symm

end Vegas.AsyncServiceSpec
