module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensConcurrentGraph
public import Vegas.Game.PrefixClientNash
public import Vegas.Pending.PeriodicServiceCompletion
public import Interaction.MessageNetworkObservation

@[expose] public section

noncomputable section

namespace Vegas.Examples.OddsEvensConcurrent

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability
open OddsEvens

/-- Select all pending identifiers at every activation. -/
abbrev leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
  MessageNetwork.ObservationRule.allPending

/-- Uniform six-tick relative deadlines for the concurrent application. -/
def serviceDuration : graph.EventId → Nat := fun _ => 6

abbrev serviceHorizon := PeriodicService.horizon

/-- The periodic builder drains traffic, activates both players, expires events and ticks. -/
def serviceScheduler : (serviceApplication setup dependencies serviceDuration leaks).Scheduler :=
  PeriodicService.scheduler graph (Equiv.refl Bool) leaks

private theorem serviceContract :
    AsyncContract (serviceTimeouts setup dependencies serviceDuration) leaks
      (serviceInitialDistribution setup dependencies) serviceHorizon serviceScheduler
      (fun _ => 3) (fun _ => 2) := by
  change AsyncContract (PeriodicService.timeouts graph) leaks
    (serviceInitialDistribution setup dependencies) PeriodicService.horizon
    (PeriodicService.scheduler graph (Equiv.refl Bool) leaks) (fun _ => 3) (fun _ => 2)
  have supplied := PeriodicService.contract (graph := graph) (roster := Equiv.refl Bool)
    (leaks := leaks) (inputLaw := setup.initialDistribution.map setup.eventInputs)
    (by rw [event_count]) (by
      intro event
      obtain ⟨who, owned⟩ := all_owned event
      rw [owned]
      rfl)
  simpa only [serviceDuration, serviceScheduler, serviceTimeouts, serviceHorizon,
    PeriodicService.timeouts, PeriodicService.initial, serviceInitialDistribution,
    PMF.map_comp, Function.comp_def] using supplied

private theorem serviceTimely :
    AsyncTimely (serviceTimeouts setup dependencies serviceDuration)
      (fun _ => 3) (fun _ => 2) := PeriodicService.timely (graph := graph)

/-- The compiled fair clients act at their first event opportunity. -/
def clients : Player → (serviceApplication setup dependencies serviceDuration leaks).Policy :=
  turnPolicy (serviceTimeouts setup dependencies serviceDuration) leaks (fun _ => 2) 0
    (firstTurnTiming setup 0 dependencies) (effectiveOpening graphClients)

/-- The compiled periodic application preserves the fair Nash equilibrium and its full law. -/
theorem native_equilibrium :
    let app := serviceApplication setup dependencies serviceDuration leaks
    let native := app.roundsFrom (serviceInitialDistribution setup dependencies) serviceScheduler
      clients serviceHorizon
    IsεNash (serviceGame setup dependencies serviceDuration leaks serviceScheduler serviceHorizon)
      (setup.graphForfeitConfigPayoff dependencies (fun _ => ()) sourceUtility 200) 0 clients ∧
    (∀ final ∈ native.support,
      final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
        ∃ terminal,
          serviceRankedReadout setup dependencies serviceDuration leaks (app.finished final) =
            some terminal ∧ ∀ who,
              failedReveals program who (publicOutcome program terminal) = 0) ∧
    native.map (fun final =>
      (serviceRankedReadout setup dependencies serviceDuration leaks (app.finished final),
        setup.graphForfeitConfigPayoff dependencies (fun _ => ()) sourceUtility 200
          final.application.config)) = uniformJointDistribution ∧
    ∀ who, expect native (fun final => setup.graphForfeitConfigPayoff dependencies (fun _ => ())
      sourceUtility 200 final.application.config who) = 100 := by
  intro app native
  obtain ⟨nash, clean, law⟩ := native_compileIntendedExtension_preserved (turns := 0)
    setup dependencies relaxed finiteBindingTypes wellFormed (fun _ => ()) sourceUtility 200
    utility_spread uniformAssessment.strategy target target_extends 0 uniform_isNash
    serviceDuration leaks serviceScheduler (fun _ => 2) serviceContract serviceTimely
  have exactLaw := law.trans uniform_joint_distribution
  refine ⟨nash, fun final reached => clean final ?_, exactLaw, ?_⟩
  · -- Compare the laws, not the memberships, which would evaluate the concrete game.
    refine Eq.mp (congrArg (fun law => final ∈ PMF.support law) ?_) reached
    rfl
  intro who
  have expected := congrArg (fun law => expect law (fun observed => observed.2 who)) exactLaw
  rw [expect_map] at expected
  exact expected.trans (uniformJointDistribution_expected_payoff who)

end Vegas.Examples.OddsEvensConcurrent
