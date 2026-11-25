module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.PaymentPreservation
public import Vegas.Examples.OddsEvensRawEquilibrium

@[expose] public section

/-! # The uniform semantic compiler under a checked two-player service

The instance supplies service and audit certificates. All player
strategies come from the generic compiler; there is no game-specific client
construction. The fair assessment specializes the same compiler and preserves
the exact joint source-configuration and settled-payoff law.
-/

noncomputable section

namespace VegasTests.ClientCompiler

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
  GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Vegas.Examples.OddsEvensService
open Vegas.Examples.OddsEvensRaw

def compiled (intended : Vegas.Examples.OddsEvens.setup.intendedModel.BehavioralAssessment)
    (equilibrium : Vegas.Examples.OddsEvens.setup.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended) :=
  specification.compile intended equilibrium

example (intended : Vegas.Examples.OddsEvens.setup.intendedModel.BehavioralAssessment)
    (equilibrium : Vegas.Examples.OddsEvens.setup.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended) (who : Bool) :
    ReactiveApplication.Policy.IgnoresLeakedFields app
      ((compiled intended equilibrium).ledgerClients who) :=
  (compiled intended equilibrium).ledgerClients_ignoreLeakedFields who

example (intended : Vegas.Examples.OddsEvens.setup.intendedModel.BehavioralAssessment)
    (equilibrium : Vegas.Examples.OddsEvens.setup.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended)
    (who : Bool) (past : List app.PlayerEntry) (view : app.PlayerView) :
    ((compiled intended equilibrium).ledgerClients who past view).support.Finite :=
  (compiled intended equilibrium).ledgerClients_support_finite who past view

example (intended : Vegas.Examples.OddsEvens.setup.intendedModel.BehavioralAssessment)
    (equilibrium : Vegas.Examples.OddsEvens.setup.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended)
    (state : app.ProtocolState)
    (supported : state ∈ (app.finish initial horizon scheduler
      (compiled intended equilibrium).clients none).support)
    (control : app.Control) (current : state = some control) :
    control.execution.application.config.defaulted = ∅ := by
  unfold initial at supported
  with_reducible
    exact (compiled intended equilibrium).clients_noDefaults state supported control current

example (intended : Vegas.Examples.OddsEvens.setup.intendedModel.BehavioralAssessment)
    (equilibrium : Vegas.Examples.OddsEvens.setup.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended)
    (state : app.ProtocolState)
    (supported : state ∈ (app.finish initial horizon scheduler
      (compiled intended equilibrium).clients none).support) (who : Bool) :
    GameTheory.Enforcement.TerminalAudit.charge app.stateTraffic
      ((countAudit timeouts) leaks specification.evidenceService.sample) state who = 0 := by
  unfold initial at supported
  with_reducible exact (compiled intended equilibrium).clients_noCharges state supported who

example (intended : Vegas.Examples.OddsEvens.setup.intendedModel.BehavioralAssessment)
    (equilibrium : Vegas.Examples.OddsEvens.setup.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended) :
    (app.finish initial horizon scheduler (compiled intended equilibrium).ledgerClients none).bind
      (specification.observation) =
    (Vegas.Examples.OddsEvens.setup.intendedModel.runBehavioral intended.strategy
      (instructionCount Vegas.Examples.OddsEvens.setup.program + 1)).map
      (Vegas.intendedReadoutExclusion Vegas.Examples.OddsEvens.setup (fun _ => ())
        Vegas.Examples.OddsEvens.sourceUtility (fun _ => 0)) :=
  (compiled intended equilibrium).ledgerClients_outcomeDistribution (by intro _ _; rfl)

def fairCompilation := compiled Vegas.Examples.OddsEvens.uniformAssessment
  Vegas.Examples.OddsEvens.uniformAssessment_equilibrium

example : (app.finish initial horizon scheduler fairCompilation.ledgerClients none).bind
    (specification.observation) =
      Vegas.Examples.OddsEvens.uniformJointDistribution := by
  exact (fairCompilation.ledgerClients_outcomeDistribution (by intro _ _; rfl)).trans
    Vegas.Examples.OddsEvens.uniform_source_joint_distribution


section MonetaryCompilation

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
  (exitValuation : Player → ℝ)
  (spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter
    (setup.parameterPaymentUtility valuation)
    (fun who => exitValuation who + (setup.exitTransfers who : ℝ)))
  (intended : setup.intendedModel.BehavioralAssessment)
  (equilibrium : setup.IntendedSequentialEquilibrium parameter
    (setup.parameterPaymentUtility valuation) intended)

example :
    ((application setup timeouts leaks).finish (initialDistribution setup) horizon scheduler
        (spec.compile intended equilibrium).clients none).bind spec.programPaymentObservation =
      setup.intendedPaymentDistribution intended :=
  (spec.compile intended equilibrium).clients_programPayments_preserved setup timeouts leaks bounds
    horizon scheduler parameter (setup.parameterPaymentUtility valuation)
      (fun who => exitValuation who + (setup.exitTransfers who : ℝ)) spec intended

end MonetaryCompilation

end VegasTests.ClientCompiler
