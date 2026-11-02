/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveMessageReadout
import Vegas.Examples.PrivateValueAuction
import Vegas.Compile.EventGraphAssembly
import GameTheory.Math.Probability.Uniform

/-! # Pending observation samples remain private from scheduling

Alice sends an actual commitment packet. Bob's observation rule can either
learn that foreign pending packet or learn nothing, while every scheduler
receives the same public observation and command recall in both branches.
-/

noncomputable section

namespace VegasTests.PendingObservationPrivacy

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open Vegas.Examples.PrivateValueAuction
open Vegas.Examples.CommitRevealAuction (Player)

private abbrev graph := Vegas.toEventGraph program
private abbrev firstEvent : graph.EventId := ⟨0, by decide⟩
private def runtime : EventGraphRuntime graph := ⟨fun _ => 10⟩

private def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
  fun _ pending => (PMF.uniformOfFintype Bool).map fun seen =>
    if seen then (pending.map Message.id).toFinset else ∅

private abbrev app := runtime.reactiveApplication leaks

private def initialExecution : app.Execution :=
  ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (Vegas.encodeInputs (initial fun _ => 0)))

private def commitment : app.Action :=
  ⟨some ⟨⟨.commitment firstEvent (.alice, .prepared 0), some ⟨.int, 7⟩⟩, .none⟩⟩

private def sent : app.Execution := initialExecution.respond app .alice commitment

private def missed : app.Execution := sent.sampledActivation app .bob ∅
private def observed : app.Execution := sent.sampledActivation app .bob {(.alice, 0)}

/-- The fixture contains a real foreign pending commitment before sampling. -/
theorem pending_nonempty :
    sent.network.pending.map Message.id = [(.alice, 0)] := rfl

private theorem missed_supported :
    missed ∈ (sent.environmentStep app (.activate .bob)).support := by
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
  refine ⟨∅, ?_, rfl⟩
  change ∅ ∈ ((PMF.uniformOfFintype Bool).map fun seen =>
    if seen then (sent.network.pending.map Message.id).toFinset else ∅).support
  rw [PMF.support_map]
  exact ⟨false, PMF.mem_support_uniformOfFintype false, rfl⟩

private theorem observed_supported :
    observed ∈ (sent.environmentStep app (.activate .bob)).support := by
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
  refine ⟨{(.alice, 0)}, ?_, rfl⟩
  change {(.alice, 0)} ∈ ((PMF.uniformOfFintype Bool).map fun seen =>
    if seen then (sent.network.pending.map Message.id).toFinset else ∅).support
  rw [PMF.support_map]
  refine ⟨true, PMF.mem_support_uniformOfFintype true, ?_⟩
  simp [pending_nonempty]

/-- The supported branches give Bob different private knowledge. -/
theorem different_private_observations :
    (missed.observe app .bob).messages.leaked = [] ∧
      (observed.observe app .bob).messages.leaked = sent.network.pending := by
  constructor <;> rfl

theorem activation_has_distinct_branches : missed ≠ observed := by
  intro same
  have knowledge := congrArg (fun execution : app.Execution =>
    (execution.observe app .bob).messages.leaked.map Message.id) same
  change ([] : List (MessageId Player)) = [(.alice, 0)] at knowledge
  cases knowledge

/-- Both branches are actual supported outcomes of the same activation. -/
theorem observation_rule_branches :
    missed ∈ (sent.environmentStep app (.activate .bob)).support ∧
      observed ∈ (sent.environmentStep app (.activate .bob)).support ∧ missed ≠ observed :=
  ⟨missed_supported, observed_supported, activation_has_distinct_branches⟩

/-- The scheduler's entire input agrees after the two different private samples. -/
theorem same_scheduler_input :
    (missed.environmentRecall, missed.observeEnvironment app) =
      (observed.environmentRecall, observed.observeEnvironment app) :=
  (reactiveApplication_activation_schedulerInput runtime leaks sent missed .bob
    missed_supported).trans
      (reactiveApplication_activation_schedulerInput runtime leaks sent observed .bob
        observed_supported).symm

theorem every_scheduler_same_law (scheduler : app.Scheduler) :
    scheduler missed.environmentRecall (missed.observeEnvironment app) =
      scheduler observed.environmentRecall (observed.observeEnvironment app) :=
  reactiveApplication_activation_scheduler runtime leaks scheduler sent missed observed .bob
    missed_supported observed_supported

end VegasTests.PendingObservationPrivacy
