/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrefixSymmetry
import VegasTests.SelectiveAssociationRestrictedGuessSegment
import Interaction.ReactiveSubmissionAudit

/-! # Carol's actual inclusion under a hidden Alice candidate change

Authenticated submission provenance ties a selected pending occurrence to the
envelope returned by identifier lookup. The service therefore calls Carol's
binding handler, whose success and rejection cases both commute with changing
Alice's unrelated hidden candidate.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def publicProjection (view : app.LocalObservation) : app.PublicObservation := view.publicView

theorem responded_audit (control : app.Control) (trace : arena.Trace (some control))
    (who : Player) (active : control.actor = some who) (action : app.Action) :
    (control.execution.respond app who action).SubmissionAudit app publicProjection := by
  let raw := menu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon scheduler trace
  have audit := app.submissionAudit_history publicProjection (by intros; rfl)
    (FinDist.pure nativeInitial) nativeHorizon scheduler raw
  exact app.submissionAudit_respond publicProjection (by intros; rfl) control.execution who action
    audit.1 (app.submissionOrigin_next_none_history (FinDist.pure nativeInitial) nativeHorizon
      scheduler control raw who) (audit.2 who active)

theorem latest_lookup_addressed (execution : app.Execution)
    (audit : execution.SubmissionAudit app publicProjection)
    (event : nativeGraph.EventId) (who : Player) (id : MessageId Player)
    (selection : nativeRuntime.reactiveLatest leaks event who
      (execution.observeEnvironment app) = .include id)
    (sent : Message Player app.Payload) (found : execution.network.lookup id = some sent) :
    (show WitnessedPacket nativeGraph from sent.payload).call.event? nativeGraph = some event := by
  unfold reactiveLatest at selection
  split at selection
  · cases selection
  · rename_i chosen selected
    have pending : chosen ∈ execution.network.pending :=
      List.mem_reverse.mp (List.mem_of_find?_eq_some selected)
    have identity : chosen.id = id := by cases selection; rfl
    have recovered := ReactiveApplication.Execution.SubmissionAudit.lookup_of_mem app
      publicProjection execution audit chosen pending
    rw [identity, found] at recovered
    have same : sent = chosen := Option.some.inj recovered
    subst sent
    have accepted := List.find?_some selected
    simp only [decide_eq_true_eq] at accepted
    exact accepted.2.1

theorem related_carol_inclusion (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (first second : app.Execution) (related : Related selected first second)
    (audit : first.SubmissionAudit app publicProjection) :
    Related selected (Prefix.includeLatest first carolBinding carol)
      (Prefix.includeLatest second carolBinding carol) := by
  apply related_includeLatest selected first second related carolBinding carol
  intro id chosen sent found
  have addressed := latest_lookup_addressed first audit carolBinding carol id chosen sent found
  change handle nativeRuntime second.application
      ⟨(CandidateFlip.message selected sent).id,
        (CandidateFlip.message selected sent).payload.call⟩ =
    (handle nativeRuntime first.application ⟨sent.id, sent.payload.call⟩).map
      (StoreFlip.state selected)
  rw [related.application]
  exact StoreFlip.handle_other_binding selected owner first.application carolBinding (by decide)
    carol (by decide) (native_binding_output carol) (native_binding_code carol)
      (native_binding_node carol) ⟨sent.id, sent.payload.call⟩ addressed

theorem environment_accepted (execution : app.Execution)
    (command : EnvironmentCommand nativeGraph) :
    (Prefix.environmentResult execution (.application command)).application.accepted =
      execution.application.accepted := by
  have reached : (Prefix.environmentResult execution (.application command)).application ∈
      (app.environment execution.application command).support :=
    (Prefix.environmentResult_application_law execution command).symm ▸
      FinDist.mem_support_pure.mpr rfl
  exact (environmentStep_tables nativeRuntime execution.application _ command reached).1

theorem inclusion_accepted_of_present (execution : app.Execution) (event : nativeGraph.EventId)
    (who : Player) (field : nativeGraph.Field)
    (present : (execution.application.config.store field).isSome = true) :
    (Prefix.includeLatest execution event who).application.accepted field =
      execution.application.accepted field := by
  unfold Prefix.includeLatest
  have reached : Prefix.environmentResult execution
      (nativeRuntime.reactiveLatest leaks event who (execution.observeEnvironment app)) ∈
        (execution.environmentStep app
          (nativeRuntime.reactiveLatest leaks event who
            (execution.observeEnvironment app))).support := by
    rw [Prefix.environmentResult_law]
    exact FinDist.mem_support_pure.mpr rfl
  cases command : nativeRuntime.reactiveLatest leaks event who (execution.observeEnvironment app)
      with
  | wait =>
      rw [command] at reached
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        FinDist.mem_support_pure] at reached
      rw [reached]
  | «include» id =>
      rw [command] at reached
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        FinDist.mem_support_pure] at reached
      rw [reached]
      change (execution.includePending app id).application.accepted field = _
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some sent =>
          change ((handle nativeRuntime execution.application ⟨sent.id, sent.payload.call⟩).getD
            execution.application).accepted field = _
          cases handled : handle nativeRuntime execution.application ⟨sent.id, sent.payload.call⟩
              with
          | none => rfl
          | some next =>
              exact handle_accepted_of_present nativeRuntime execution.application next field
                present _ handled
  | activate | application =>
      unfold reactiveLatest at command
      split at command <;> cases command

theorem afterCarol_accepted (execution : app.Execution) (action : app.Action)
    (present : (execution.application.config.store aliceBindingRef.field).isSome = true) :
    (afterCarol execution action).application.accepted aliceBindingRef.field =
      execution.application.accepted aliceBindingRef.field := by
  unfold afterCarol
  change (Prefix.environmentResult _ (.application (.grant bobBinding))).application.accepted
    aliceBindingRef.field = _
  rw [environment_accepted, environment_accepted, environment_accepted, environment_accepted]
  rw [inclusion_accepted_of_present _ carolBinding carol aliceBindingRef.field (by
    rw [(nativeRuntime.reactive_respond_application leaks execution carol action).1]
    exact present)]
  exact congrFun (congrArg PublicView.accepted
    (nativeRuntime.reactive_respond_application leaks execution carol action).2)
      aliceBindingRef.field

theorem bobInput_accepted (responses : Prefix.BobResponses)
    (present : ((Prefix.carolInput responses.beforeCarol).application.config.store
      aliceBindingRef.field).isSome = true) :
    (Prefix.bobInput responses).application.accepted aliceBindingRef.field =
      (Prefix.carolInput responses.beforeCarol).application.accepted aliceBindingRef.field :=
  afterCarol_accepted _ _ present

end VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry
