module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveRuntime
public import Interaction.ReactiveMessageReadout
public import Interaction.ReactiveLedgerPolicy
public import Vegas.Examples.PrivateValueAuction
public import Vegas.Compile.EventGraphAssembly
public import GameTheory.Math.Probability.Uniform
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

open GameTheory.Math.Probability

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

abbrev graph := Vegas.toEventGraph program
abbrev firstEvent : graph.EventId := ⟨0, by decide⟩
def timeouts : EventTimeouts graph := ⟨fun _ => 10⟩

def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
  fun _ pending => (uniformLaw Bool).map fun seen =>
    if seen then (pending.map Message.id).toFinset else ∅

abbrev app := (reactiveApplication timeouts) leaks

def initialExecution : app.Execution :=
  ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (Vegas.encodeInputs (initial fun _ => 0)))

def commitment : app.Action :=
  ⟨some ⟨⟨.commitment firstEvent (.alice, .prepared 0), some ⟨.int, 7⟩⟩, .none⟩⟩

def sent : app.Execution := initialExecution.respond app .alice commitment

def missed : app.Execution := sent.sampledActivation app .bob ∅
def observed : app.Execution := sent.sampledActivation app .bob {(.alice, 0)}

/-- The fixture contains a real foreign pending commitment before sampling. -/
theorem pending_nonempty :
    sent.network.pending.map Message.id = [(.alice, 0)] := rfl

private theorem missed_supported :
    missed ∈ (sent.environmentStep app (.activate .bob)).support := by
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
  refine ⟨∅, ?_, rfl⟩
  change ∅ ∈ ((uniformLaw Bool).map fun seen =>
    if seen then (sent.network.pending.map Message.id).toFinset else ∅).support
  rw [PMF.support_map]
  exact ⟨false, mem_support_uniformLaw false, rfl⟩

private theorem observed_supported :
    observed ∈ (sent.environmentStep app (.activate .bob)).support := by
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
  refine ⟨{(.alice, 0)}, ?_, rfl⟩
  change {(.alice, 0)} ∈ ((uniformLaw Bool).map fun seen =>
    if seen then (sent.network.pending.map Message.id).toFinset else ∅).support
  rw [PMF.support_map]
  refine ⟨true, mem_support_uniformLaw true, ?_⟩
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
  (reactiveApplication_activation_schedulerInput timeouts leaks sent missed .bob
    missed_supported).trans
      (reactiveApplication_activation_schedulerInput timeouts leaks sent observed .bob
        observed_supported).symm

theorem every_scheduler_same_law (scheduler : app.Scheduler) :
    scheduler missed.environmentRecall (missed.observeEnvironment app) =
      scheduler observed.environmentRecall (observed.observeEnvironment app) :=
  reactiveApplication_activation_scheduler timeouts leaks scheduler sent missed observed .bob
    missed_supported observed_supported

def certificate : OpeningFact graph := ⟨(.alice, .prepared 0), ⟨.int, 7⟩⟩

def certifiedCommitment : app.Action :=
  ⟨some ⟨⟨.commitment firstEvent certificate.handle, some certificate.raw⟩, .owned certificate⟩⟩

def certifiedSent : app.Execution :=
  initialExecution.respond app .alice certifiedCommitment

def certifiedBranch (seen : Bool) : app.Execution :=
  certifiedSent.sampledActivation app .bob (if seen then {(.alice, 0)} else ∅)

theorem certified_branch_supported (seen : Bool) :
    certifiedBranch seen ∈ (certifiedSent.environmentStep app (.activate .bob)).support := by
  unfold certifiedBranch
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
  apply Set.mem_image_of_mem
  change _ ∈ ((uniformLaw Bool).map fun selected =>
    if selected then (certifiedSent.network.pending.map Message.id).toFinset else ∅).support
  rw [PMF.support_map]
  refine ⟨seen, mem_support_uniformLaw seen, ?_⟩
  have ids : certifiedSent.network.pending.map Message.id = [(.alice, 0)] := rfl
  cases seen <;> simp [ids]

def guessedForward : app.Action :=
  ⟨some ⟨⟨.malformed ⟨.int, 0⟩, none⟩, .forward (.alice, 0)⟩⟩

def forwarded (seen : Bool) : app.Execution :=
  (certifiedBranch seen).respond app .bob guessedForward

def recalledEvidence (past : List app.PlayerEntry) : List (OpeningFact graph) :=
  past.filterMap fun entry => entry.emitted.bind fun message => message.payload.evidence

/-- A fixed request for a guessed identifier materializes evidence only after
private delivery. Neither branch has included a packet. -/
theorem guessed_forward_materializes_private_evidence :
    recalledEvidence ((forwarded false).logs .bob) = [] ∧
      recalledEvidence ((forwarded true).logs .bob) = [certificate] ∧
      (forwarded false).network.ledger = [] ∧ (forwarded true).network.ledger = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Erasing explicit leaked fields retains the authentic packet Bob emitted. -/
theorem ledger_projection_retains_emitted_evidence :
    recalledEvidence (((forwarded false).logs .bob).map
      (ReactiveApplication.PlayerEntry.ledgerOnly app)) = [] ∧
    recalledEvidence (((forwarded true).logs .bob).map
      (ReactiveApplication.PlayerEntry.ledgerOnly app)) = [certificate] ∧
    ((forwarded false).observe app .bob).ledgerOnly app =
      ((forwarded true).observe app .bob).ledgerOnly app := ⟨rfl, rfl, rfl⟩

def rememberEvidence : app.Policy := fun past _ =>
  PMF.pure (if (recalledEvidence past).isEmpty then ⟨none⟩ else guessedForward)

/-- Ignoring leaked fields erases their direct use, while legitimate own-output
recall can still distinguish earlier private deliveries. -/
theorem ledger_policy_can_recall_private_evidence :
    ReactiveApplication.Policy.IgnoresLeakedFields app (app.ledgerPolicy rememberEvidence) ∧
      app.ledgerPolicy rememberEvidence ((forwarded false).logs .bob)
        ((forwarded false).observe app .bob) = PMF.pure ⟨none⟩ ∧
      app.ledgerPolicy rememberEvidence ((forwarded true).logs .bob)
        ((forwarded true).observe app .bob) = PMF.pure guessedForward :=
  ⟨app.ledgerPolicy_ignoresLeakedFields rememberEvidence, rfl, rfl⟩

end VegasTests.PendingObservationPrivacy
