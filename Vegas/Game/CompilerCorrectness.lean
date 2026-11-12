/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceClientPolicy
import Vegas.Game.SourceServiceSiteBridge
import Vegas.Game.ServiceHonestLaw
import Vegas.Compile.EventGraphCanonical
import Interaction.ReactiveRestrictedContinuation

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

/-- Every total observation of the typed terminal state and public defaults has
its exact source law under the actual bounded first-turn clients. -/
theorem firstTurnClientProfile_outcome_law {Outcome : Type*}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature)
    (observe : State L service.setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    (service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)).map
        (fun final => (serviceSourceReadout service.setup service.mode service.duration
          service.leaks final.state).map fun terminal =>
            observe (terminal.state, terminal.defaults)) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map
        (fun terminal => some (observe (terminal.state, terminal.defaults))) := by
  let app := serviceApplication service.setup service.mode service.duration service.leaks
  let original := service.setup.decodeBehavioralProfile admission source
  let clients := serviceClientPolicy service.setup service.mode service.duration service.leaks
    service.bound turns (firstTurnTiming service.setup turns service.mode)
      (normalizeDisclosureProfile service.setup.program original)
  have physical := service.rawMenu.run_restrict_eq_finish
    (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler clients
    (service.rawMenu_admits admission (firstTurnTiming service.setup turns service.mode) source)
    (2 * service.horizon + 1)
    (service.rawMenu.protocol (serviceInitialLaw service.setup service.mode)
      service.horizon service.scheduler).initHistory le_rfl
  have initialized : (service.rawMenu.protocol (serviceInitialLaw service.setup service.mode)
      service.horizon service.scheduler).initHistory.state = none := rfl
  rw [initialized] at physical
  have states : (service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)).map (fun final => final.state) =
      (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler clients
        service.horizon).map app.finished := by
    change ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).runBehavioralFrom
      (fun who => service.rawMenu.restrictPolicy (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler who (clients who))
      (2 * service.horizon + 1)
      (service.rawMenu.protocol (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).initHistory).map ExecutionProtocol.History.state = _
    simpa only [ReactiveApplication.finish, ReactiveApplication.roundsFrom, PMF.map_bind]
      using physical
  have projected := congrArg (PMF.map (fun final : app.ProtocolState =>
    (serviceSourceReadout service.setup service.mode service.duration service.leaks final).map
      fun terminal => observe (terminal.state, terminal.defaults))) states
  simp only [PMF.map_comp, Function.comp_def] at projected
  apply projected.trans
  apply sourceServiceClientPolicy_outcome_law_of_firstTurn original ?_ observe
  exact firstTurn_readout_law service.setup service.leaks ordered service.contract service.timely
    turns (normalizeDisclosureProfile service.setup.program original)
      (fun who => BehavioralPolicy.normalizeDisclosures_authentic service.setup.program
        (original who))

/-- The bounded ledger clients and the canonical compiled graph have the same
joint law of typed state and public defaults, in every supported dependency mode. -/
theorem firstTurnClientProfile_graph_law {Outcome : Type*}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature)
    (observe : State L service.setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    (service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)).map
        (fun final => (serviceSourceReadout service.setup service.mode service.duration
          service.leaks final.state).map fun terminal =>
            observe (terminal.state, terminal.defaults)) =
      ((service.setup.eventGraph.canonicalGame
          (service.setup.initialLaw.map service.setup.eventInputs)).play
        (compileEventProfile service.setup.program
          (service.setup.decodeBehavioralProfile admission source))).map (fun terminal =>
          let final := terminalConfig service.setup.program terminal
          some (observe (final.state, final.defaults))) := by
  rw [service.firstTurnClientProfile_outcome_law admission ordered turns source observe]
  have law := congrArg (PMF.map (fun final : Config Player L service.setup.program.terminalCtx =>
    some (observe (final.state, final.defaults))))
      (canonical_setup_law service.setup (service.setup.decodeBehavioralProfile admission source))
  simpa only [PMF.map_comp, Function.comp_def] using law.symm

end Vegas.AsyncServiceSpec
