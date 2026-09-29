/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Native
import Vegas.Examples.MonitoredGuessing.NativeResponses
import Interaction.ReactiveQuiescent
import Interaction.ReactiveTrafficAudit

/-! # A canonical opening can communicate through its submission time

The existing runtime, graph, initialized commitments and raw opening response
are unchanged. The observation service lets a foreign player read pending
traffic at two visits. The owner emits exactly the same canonical opening at
either the first or second owner visit. There is no inclusion, tick, expiry or
grant change between them. Both executions end with the same current public
and receiver views, but the receiver remembers which first view it saw.

This is an operational timing-channel witness, not an equilibrium theorem.
-/

noncomputable section

namespace Vegas.Examples.OpeningTimingChannel

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open MonitoredGuessing

private def pendingObservation : MessageNetwork.ObservationRule Player
    (WitnessedPacket nativeGraph) := fun _ pending => PMF.pure (pendingIds pending)

private abbrev app := nativeRuntime.reactiveApplication pendingObservation

private def initial : app.Execution :=
  ReactiveApplication.Execution.initial app
    { nativeInitial false with serviceGrant := some bobPublication }

private def silent : app.Action := ⟨none⟩

private def opening : app.Action :=
  ⟨some (.submit ⟨⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none⟩,
    .owned ⟨bobHandle, ⟨.bool, true⟩⟩⟩)⟩

private def packet : Message Player app.Payload :=
  ⟨(bob, 0), ⟨.opening bobPublication bobHandle ⟨.bool, true⟩,
    some ⟨bobHandle, ⟨.bool, true⟩⟩⟩⟩

/-- This is exactly the ordinary activation transition's sampled execution. -/
private def activated (execution : app.Execution) (who : Player) : app.Execution :=
  { execution with
    network := execution.network.learn who (pendingIds execution.network.pending)
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate who⟩] }

theorem activation_law (execution : app.Execution) (who : Player) :
    execution.environmentStep app (.activate who) = PMF.pure (activated execution who) := by
  simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
    pendingObservation, PMF.pure_map]
  rfl

private def firstOwner (early : Bool) : app.Execution :=
  (activated initial bob).respond app bob (if early then opening else silent)

private def firstObserver (early : Bool) : app.Execution :=
  (activated (firstOwner early) alice).respond app alice silent

private def secondOwner (early : Bool) : app.Execution :=
  (activated (firstObserver early) bob).respond app bob (if early then silent else opening)

private def final (early : Bool) : app.Execution := activated (secondOwner early) alice

/-- The extra visit never changes the currently granted event or its readiness;
the same initialized value is openable at both possible emission points. -/
theorem both_openings_ready :
    (activated initial bob).application.config.cut.Ready bobPublication ∧
      (activated (firstObserver false) bob).application.config.cut.Ready bobPublication ∧
      (activated initial bob).application.serviceGrant = some bobPublication ∧
      (activated (firstObserver false) bob).application.serviceGrant = some bobPublication ∧
      (activated initial bob).application.candidates.lookup bobHandle =
        .openable ⟨.bool, true⟩ ∧
      (activated (firstObserver false) bob).application.candidates.lookup bobHandle =
        .openable ⟨.bool, true⟩ := by
  exact ⟨initial_bob_ready false, initial_bob_ready false, rfl, rfl,
    initial_bob_candidate false, initial_bob_candidate false⟩

theorem both_openings_compiled :
    nativeRuntime.reactiveDecision pendingObservation bob bobPublication true
      ((activated initial bob).observe app bob).application = opening ∧
      nativeRuntime.reactiveDecision pendingObservation bob bobPublication true
        ((activated (firstObserver false) bob).observe app bob).application = opening := by
  have first : nativeRuntime.reactiveDecision pendingObservation bob bobPublication true
      ((activated initial bob).observe app bob).application = opening := by
    unfold reactiveDecision
    rw [bob_node]
    change (⟨some (.submit ((disclosureSubmission
      (.opening bobPublication bobHandle ⟨.bool, true⟩)).normalizeReactive bob _ []))⟩ :
      app.Action) = opening
    rw [disclosureSubmission_normalize_opening bob _ bobPublication bobHandle
      ⟨.bool, true⟩ rfl (initial_bob_candidate false)]
    rfl
  exact ⟨first, first⟩

theorem same_opening_packet :
    (firstOwner true).network.pending = [packet] ∧
      (secondOwner false).network.pending = [packet] := by
  constructor <;> rfl

theorem first_observation_distinguishes :
    ((activated (firstOwner true) alice).observe app alice).messages.leaked = [packet] ∧
      ((activated (firstOwner false) alice).observe app alice).messages.leaked = [] := by
  constructor <;> rfl

/-- No message has been included. Delaying ledger visibility does not erase
the information learned earlier from pending traffic. -/
theorem same_final_current_view :
    (final true).observe app alice = (final false).observe app alice ∧
      (final true).observeEnvironment app = (final false).observeEnvironment app ∧
      (final true).network.ledger = [] := by
  constructor
  · rfl
  constructor <;> rfl

private def rememberedFirstLeak (execution : app.Execution) : Nat :=
  match (execution.recall alice).head? with
  | none => 0
  | some entry => entry.beforeView.messages.leaked.length

theorem remembered_first_leak (early : Bool) :
    rememberedFirstLeak (final early) = if early then 1 else 0 := by
  cases early <;> rfl

/-- The receiver can recover the timing bit from its actual own-action recall,
although the opening body, final current observation and public clock agree. -/
theorem final_recall_distinguishes :
    (final true).recall alice ≠ (final false).recall alice := by
  intro same
  have readout := congrArg (fun history =>
    (history.head?.map (fun entry : app.PlayerEntry =>
      entry.beforeView.messages.leaked.length)).getD 0) same
  change (1 : Nat) = 0 at readout
  omega

theorem final_information_distinguishes :
    app.observe alice (some ⟨1, some alice, final true⟩) ≠
      app.observe alice (some ⟨1, some alice, final false⟩) := by
  intro same
  have recall := congrArg (fun observed => observed.map Prod.fst) same
  simp only [ReactiveApplication.observe, ↓reduceIte, Option.map_some,
    Option.some.injEq] at recall
  exact final_recall_distinguishes recall

theorem same_final_application :
    (final true).application = (final false).application ∧
      (final true).application.clock = 0 := by
  constructor <;> rfl

/-- These are the actual traffic readouts of the two owner responses. Every
intervening environment step and the receiver's silent response contributes
no record by `trafficStep_environment` and `trafficStep_silent`. -/
private def records (early : Bool) : List app.TrafficRecord :=
  app.trafficStep (some ⟨3, some bob, activated initial bob⟩)
      (some ⟨3, none, firstOwner early⟩) ++
    app.trafficStep (some ⟨1, some bob, activated (firstObserver early) bob⟩)
      (some ⟨1, none, secondOwner early⟩)

/-- Phase, prior ledger, broadcaster and envelope all agree. The current
terminal traffic readout does not record silent activation boundaries. -/
theorem same_traffic_records : records true = records false := rfl

theorem every_traffic_audit_agrees {Verdict : Type}
    (audit : List app.TrafficRecord → PMF Verdict) :
    audit (records true) = audit (records false) := congrArg audit same_traffic_records

end Vegas.Examples.OpeningTimingChannel
