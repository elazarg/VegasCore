/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryClientCompiler
import Vegas.Examples.OddsEvensRecoveryRawEquilibrium

/-! # The uniform semantic compiler under a checked two-player service

The instance supplies service and audit certificates. All player
strategies come from the generic compiler; there is no game-specific client
construction. The fair assessment specializes the same compiler and preserves
the exact joint typed-store and settled-payoff law.
-/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
  GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Vegas.Examples.OddsEvensRecoveryService
open Vegas.Examples.OddsEvensRecoveryRaw

private def specification : Vegas.RecoveryClientSpec
    fixture runtime leaks Vegas.Examples.OddsEvens.bounds horizon scheduler
    (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility (fun _ => 0) where
  finiteNature := by change app.FiniteNature initial scheduler; infer_instance
  finiteSource := inferInstance
  Public := Unit
  signal := Vegas.Examples.OddsEvens.signal
  wellFormed := Vegas.Examples.OddsEvens.wellFormed
  independent := Vegas.Examples.OddsEvens.independent
  observable := Vegas.Examples.OddsEvens.observable
  delay := fun _ => 3
  bound := fun _ => 2
  opportunity := opportunity
  inclusion := protectedInclusion
  completes := completesPlay
  timely := timely
  lowerUtility := fun _ => 0
  upperUtility := fun _ => 200
  lower_le := fun result who => (Vegas.Examples.OddsEvens.sourceUtility_bounds result who).1
  le_upper := fun result who => (Vegas.Examples.OddsEvens.sourceUtility_bounds result who).2
  exitBelow := fun _ terminal _ who =>
    (Vegas.Examples.OddsEvens.sourceUtility_bounds
      (fixture.parameterOutcome (fun _ => ()) terminal) who).1
  outputValues := Vegas.Examples.OddsEvens.outputValues
  inputValues := Vegas.Examples.OddsEvens.inputValues
  capacity := Vegas.Examples.OddsEvens.candidateCapacity
  evidenceService := evidenceService
  observationRate := fun _ => halfRate.val
  deliveryRate := fun _ => halfRate.val
  delivery_nonnegative := fun _ => by norm_num [halfRate]
  coverage := thinnedCountEvidence_coverage halfRate halfRate
  deposit := fun _ => 800
  deposit_nonnegative := fun _ => by norm_num
  funded := fun _ => by norm_num [fixture, Vegas.Examples.OddsEvens.setup, halfRate]

private def compiled (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium : fixture.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended) :=
  specification.compile intended equilibrium

example (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium : fixture.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended) (who : Bool) :
    ReactiveApplication.Policy.UsesLedgerOnly app
      ((compiled intended equilibrium).ledgerClients who) :=
  (compiled intended equilibrium).ledgerClients_useLedgerOnly who

example (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium : fixture.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended)
    (who : Bool) (past : List app.PlayerEntry) (view : app.PlayerView) :
    ((compiled intended equilibrium).ledgerClients who past view).support.Finite :=
  (compiled intended equilibrium).ledgerClients_support_finite who past view

example (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium : fixture.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended)
    (state : app.ProtocolState)
    (supported : state ∈ (app.finish initial horizon scheduler
      (compiled intended equilibrium).clients none).support)
    (control : app.Control) (current : state = some control) :
    control.execution.application.excluded = ∅ :=
  (compiled intended equilibrium).clients_noExclusions state supported control current

example (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium : fixture.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended)
    (state : app.ProtocolState)
    (supported : state ∈ (app.finish initial horizon scheduler
      (compiled intended equilibrium).clients none).support) (who : Bool) :
    GameTheory.Enforcement.TerminalAudit.charge app.stateTraffic
      (Recovery.countAudit runtime leaks specification.evidenceService.sample) state who = 0 :=
  (compiled intended equilibrium).clients_noCharges state supported who

example (intended : fixture.intendedModel.BehavioralAssessment)
    (equilibrium : fixture.IntendedSequentialEquilibrium
      (fun _ => ()) Vegas.Examples.OddsEvens.sourceUtility intended) :
    (app.finish initial horizon scheduler (compiled intended equilibrium).ledgerClients none).bind
      (specification.observation) =
    (fixture.intendedModel.runBehavioral intended.strategy
      (instructionCount fixture.program + 1)).map
      (Vegas.intendedReadoutExclusion fixture (fun _ => ())
        Vegas.Examples.OddsEvens.sourceUtility (fun _ => 0)) :=
  (compiled intended equilibrium).ledgerClients_outcomeLaw (by intro _ _; rfl)

private def fairCompilation := compiled Vegas.Examples.OddsEvens.uniformAssessment
  Vegas.Examples.OddsEvens.uniformAssessment_equilibrium

example : (app.finish initial horizon scheduler fairCompilation.ledgerClients none).bind
    (specification.observation) =
      Vegas.Examples.OddsEvens.uniformJointLaw := by
  exact (fairCompilation.ledgerClients_outcomeLaw (by intro _ _; rfl)).trans
    Vegas.Examples.OddsEvens.uniform_source_joint_law

end VegasTests
