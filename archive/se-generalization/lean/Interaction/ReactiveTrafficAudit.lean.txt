/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory
import Interaction.MessageNetworkInvariant
import GameTheory.Protocol.StateKernel

/-! # Settlement evidence from the public traffic history

An audit record contains a submitted envelope, the public application
observation, and the ledger before that submission. It retains the phase and
prior publication evidence even when the envelope later becomes acceptable or
appears on the ledger.

The readout uses only successive public environment views. It is not added to
player observations. An implementation supplying this readout must authenticate
its traffic and phase records; ordinary envelope signatures alone do not
authenticate observation times. Partial observation and
collection are separate probabilistic contracts.

All results allow arbitrary raw responses and arbitrary schedulers. They do not
assume reserved reporting opportunities or a single pending envelope.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

structure TrafficRecord where
  observation : app.PublicObservation
  ledger : List (Message Principal app.Payload)
  envelope : Message Principal app.Payload

/-- Append-only network inputs identify successful transmissions. The record
carries the public phase preceding the transmission. -/
def trafficStep (before after : app.ProtocolState) : List app.TrafficRecord :=
  match before, after with
  | some previous, some next =>
      (next.execution.network.inputs.drop previous.execution.network.inputs.length).map
        fun input => ⟨app.observePublic previous.execution.application,
          previous.execution.network.ledger, input⟩
  | _, _ => []

omit [DecidableEq Principal] in
/-- The audit reads no private candidate state, response representation, or
recipient knowledge. Equal public service views give identical records. -/
theorem trafficStep_public (firstBefore firstAfter secondBefore secondAfter : app.Control)
    (before : firstBefore.execution.observeEnvironment app =
      secondBefore.execution.observeEnvironment app)
    (after : firstAfter.execution.observeEnvironment app =
      secondAfter.execution.observeEnvironment app) :
    app.trafficStep (some firstBefore) (some firstAfter) =
      app.trafficStep (some secondBefore) (some secondAfter) := by
  change
    ((firstAfter.execution.observeEnvironment app).network.inputs.drop
      (firstBefore.execution.observeEnvironment app).network.inputs.length).map
        (fun input => (⟨(firstBefore.execution.observeEnvironment app).application,
          (firstBefore.execution.observeEnvironment app).network.ledger, input⟩ :
          app.TrafficRecord)) =
      ((secondAfter.execution.observeEnvironment app).network.inputs.drop
        (secondBefore.execution.observeEnvironment app).network.inputs.length).map
          (fun input => (⟨(secondBefore.execution.observeEnvironment app).application,
            (secondBefore.execution.observeEnvironment app).network.ledger, input⟩ :
            app.TrafficRecord))
  rw [before, after]

/-- A settlement readout of the existing protocol history, not another
interpreter or a new observation available to players during execution. -/
def trafficAudit (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    {state : app.ProtocolState} → (app.protocol initial horizon scheduler).Trace state →
      List app.TrafficRecord
  | _, .start => []
  | state, .extend (source := before) prior _ _ _ =>
      trafficAudit initial horizon scheduler prior ++ app.trafficStep before state

theorem trafficStep_silent (execution : app.Execution) (remaining : Nat) (who : Principal) :
    app.trafficStep (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond app who ⟨none⟩⟩) = [] := by
  simp [trafficStep, Execution.respond]

theorem trafficStep_submit (execution : app.Execution) (remaining : Nat) (who : Principal)
    (submission : app.Submission) :
    app.trafficStep (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond app who ⟨some submission⟩⟩) =
        [⟨app.observePublic execution.application, execution.network.ledger,
          ⟨(who, execution.network.nextSerial who),
            app.packet (app.submit execution.application who submission) who
              (execution.network.known who) submission⟩⟩] := by
  simp [trafficStep, Execution.respond, MessageNetwork.submit]

/-- Checking the actual emitted traffic extends any envelope invariant to the
post-response network, including all private pending-message observations. -/
theorem trafficStep_network (execution : app.Execution) (remaining : Nat)
    (who : Principal) (response : app.Action)
    (safe : Message Principal app.Payload → Prop)
    (prior : execution.network.Satisfies safe)
    (issued : ∀ record ∈ app.trafficStep (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond app who response⟩), safe record.envelope) :
    (execution.respond app who response).network.Satisfies safe := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact prior
  | some submission =>
      apply prior.submit who
      rw [app.trafficStep_submit] at issued
      exact issued _ (List.mem_singleton_self _)

/-- Environment operations never invent a transmission record. -/
theorem trafficStep_environment (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) (remaining : Nat) :
    app.trafficStep (some ⟨remaining + 1, none, execution⟩)
      (some ⟨remaining, command.actor? app, next⟩) = [] := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simp [trafficStep]
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      simp [trafficStep, MessageNetwork.learn]
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      cases found : execution.network.lookup id <;>
        simp [trafficStep, Execution.includePending, MessageNetwork.includePending, found]
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      simp [trafficStep]

/-- A per-transmission check can use the observation phase and the packet,
whose sender is its author. The checker itself must be proved sound for the compiler. -/
def trafficViolation (permitted : app.TrafficRecord → Bool) (who : Principal)
    (records : List app.TrafficRecord) : Bool :=
  records.any fun record => decide (record.envelope.sender = who) && !permitted record

theorem trafficViolation_iff (permitted : app.TrafficRecord → Bool) (who : Principal)
    (records : List app.TrafficRecord) :
    app.trafficViolation permitted who records = true ↔
      ∃ record ∈ records, record.envelope.sender = who ∧ permitted record = false := by
  simp [trafficViolation, List.any_eq_true]

theorem trafficViolation_clear (permitted : app.TrafficRecord → Bool) (who : Principal)
    (records : List app.TrafficRecord)
    (compliant : ∀ record ∈ records, record.envelope.sender = who → permitted record = true) :
    app.trafficViolation permitted who records = false := by
  cases alarm : app.trafficViolation permitted who records with
  | false => rfl
  | true =>
      obtain ⟨record, member, owner, forbidden⟩ :=
        (app.trafficViolation_iff permitted who records).mp alarm
      have allowed := compliant record member owner
      rw [allowed] at forbidden
      contradiction

theorem trafficViolation_mono (permitted : app.TrafficRecord → Bool) (who : Principal)
    {before after : List app.TrafficRecord} (retained : before ⊆ after)
    (detected : app.trafficViolation permitted who before = true) :
    app.trafficViolation permitted who after = true := by
  obtain ⟨record, member, owner, forbidden⟩ :=
    (app.trafficViolation_iff permitted who before).mp detected
  exact (app.trafficViolation_iff permitted who after).mpr
    ⟨record, retained member, owner, forbidden⟩

/-- Once a transmission is recorded, no subsequent player or scheduler choice
can erase its phase or authorship from the settlement readout. -/
theorem trafficAudit_reaches (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last) :
    app.trafficAudit initial horizon scheduler first.trace <+:
      app.trafficAudit initial horizon scheduler last.trace := by
  induction path with
  | refl => rfl
  | step _ _ _ _ ih =>
      change _ ++ _ <+: _ at ih
      exact (List.prefix_append ..).trans ih

theorem trafficViolation_reaches (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (permitted : app.TrafficRecord → Bool) (who : Principal)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (detected : app.trafficViolation permitted who
      (app.trafficAudit initial horizon scheduler first.trace) = true) :
    app.trafficViolation permitted who (app.trafficAudit initial horizon scheduler last.trace) =
      true :=
  app.trafficViolation_mono permitted who (app.trafficAudit_reaches initial horizon scheduler
    path).subset detected

/-- A complete audit detects recorded misconduct with probability one under
every later behavioral or randomized continuation. Collecting a monetary
penalty still requires the settlement service to honor this verdict. -/
theorem trafficViolation_continuation (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (permitted : app.TrafficRecord → Bool) (who : Principal)
    (chooser : (app.protocol initial horizon scheduler).RandomizedChooser)
    (fuel : Nat) (history : (app.protocol initial horizon scheduler).History)
    (detected : app.trafficViolation permitted who
      (app.trafficAudit initial horizon scheduler history.trace) = true) :
    (((app.protocol initial horizon scheduler).runRandomizedFor chooser fuel history).toOuterMeasure
      {final | app.trafficViolation permitted who
        (app.trafficAudit initial horizon scheduler final.trace) = true}).toReal = 1 := by
  classical
  rw [← expect_indicator]
  calc
    _ = expect ((app.protocol initial horizon scheduler).runRandomizedFor chooser fuel history)
        (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro final supported
      have retained := app.trafficViolation_reaches initial horizon scheduler permitted who
        ((app.protocol initial horizon scheduler).runRandomizedFor_reachesWithin chooser
          fuel history final supported) detected
      simp [retained]
    _ = 1 := expect_constant _ _

/-- A partial audit cannot falsely accuse a player if every reported record
is genuine and this player's actual transmissions conform. Missing records
are never interpreted as proof that an action did not occur. -/
theorem trafficViolation_partial_sound (permitted : app.TrafficRecord → Bool)
    (who : Principal) (actual observed : List app.TrafficRecord)
    (authentic : observed ⊆ actual)
    (compliant : ∀ record ∈ actual,
      record.envelope.sender = who → permitted record = true) :
    app.trafficViolation permitted who observed = false :=
  app.trafficViolation_clear permitted who observed
    (fun record member => compliant record (authentic member))

/-- Recording any particular attributable violation suffices for detection.
The audit may sample correlated subsets and need not observe every message. -/
theorem trafficViolation_sampling_lower (permitted : app.TrafficRecord → Bool)
    (who : Principal) (observations : PMF (List app.TrafficRecord))
    (record : app.TrafficRecord) (owner : record.envelope.sender = who)
    (forbidden : permitted record = false) :
    (observations.toOuterMeasure {observed | record ∈ observed}).toReal ≤
      (observations.toOuterMeasure
        {observed | app.trafficViolation permitted who observed = true}).toReal := by
  apply ENNReal.toReal_mono (outerMeasure_ne_top _ _)
  apply PMF.toOuterMeasure_mono
  intro observed ⟨included, _⟩
  exact (app.trafficViolation_iff permitted who observed).mpr
    ⟨record, included, owner, forbidden⟩

end Interaction.ReactiveApplication
