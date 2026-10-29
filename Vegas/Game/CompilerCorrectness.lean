/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncServiceRawNash
import Vegas.Compile.EventGraphCanonical

/-! # Ordinary correctness of the bounded message compiler

The actual first-opportunity clients preserve the complete typed source outcome
law without an equilibrium or audit premise. Comparing this law with canonical
graph execution exposes the second compiler pass on its supported graph and
policy image. Total readers retain initial cells, public results and executable
payouts jointly, without introducing a default for unfinished execution.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (service : AsyncServiceSpec Player L)
  (admission : CommitmentInterface service.setup.program)

private theorem firstTurnClientProfile_readout_law
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature) :
    ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).runBehavioral
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)
      (2 * service.horizon + 1)).map
        (fun final => serviceSourceReadout service.setup service.mode service.deadline
          service.leaks final.state) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map some := by
  have law := service.firstTurnClientProfile_settlement_law admission ordered
    (fun _ => ()) (fun _ _ => 0) (fun _ => PMF.pure [])
    (by
      intro actual observed supported
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst observed
      exact List.nil_subset _)
    (fun _ => 0) turns source
  have projected := congrArg (PMF.map Prod.fst) law
  have erase (law : PMF (Player → ℝ))
      (result : Option (State L service.setup.program.terminalCtx)) :
      law.map (fun _ => result) = PMF.pure result := PMF.map_const law result
  have mapPure {Input Output : Type} (law : PMF Input) (read : Input → Output) :
      law.bind (fun input => PMF.pure (read input)) = law.map read :=
    PMF.bind_pure_comp read law
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, erase,
    mapPure] using projected

/-- Every total observation of the typed terminal state has its exact source
law under the actual bounded first-opportunity clients. No equilibrium, audit,
utility bound or private-input independence premise is needed. -/
theorem firstTurnClientProfile_outcome_law {Outcome : Type*}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature)
    (observe : State L service.setup.program.terminalCtx → Outcome) :
    ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).runBehavioral
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)
      (2 * service.horizon + 1)).map
        (fun final => (serviceSourceReadout service.setup service.mode service.deadline
          service.leaks final.state).map observe) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map
        (fun terminal => some (observe terminal)) := by
  have law := congrArg (PMF.map (Option.map observe))
    (service.firstTurnClientProfile_readout_law admission ordered turns source)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using law

/-- The ledger clients and the canonical compiled graph have the same exact
law of every total typed-source readout. The graph and policies are the actual
source compiler's outputs; the runtime may use either supported dependency mode. -/
theorem firstTurnClientProfile_graph_law {Outcome : Type*}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature)
    (observe : State L service.setup.program.terminalCtx → Outcome) :
    ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).runBehavioral
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)
      (2 * service.horizon + 1)).map
        (fun final => (serviceSourceReadout service.setup service.mode service.deadline
          service.leaks final.state).map observe) =
      ((service.setup.eventGraph.canonicalGame
          (service.setup.initialLaw.map fun initial => service.setup.eventInputs initial)).play
        (compileEventProfile service.setup.program
          (service.setup.decodeBehavioralProfile admission source))).map
        (fun terminal => some (observe (terminalState service.setup.program terminal))) := by
  rw [service.firstTurnClientProfile_outcome_law admission ordered turns source observe]
  have law := congrArg (PMF.map (fun terminal => some (observe terminal)))
    (canonical_setup_law service.setup (service.setup.decodeBehavioralProfile admission source))
  simpa only [PMF.map_comp, Function.comp_def] using law.symm

end Vegas.AsyncServiceSpec
