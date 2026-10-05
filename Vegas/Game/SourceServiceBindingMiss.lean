/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalSerial
import Vegas.Game.SourceServiceProtectedBinding

/-! # Binding omission facts for actual owner calls

A protected conforming unique owner call prevents a binding omission in every
legal continuation. A newly created omission must come from explicit due expiry.
These facts concern actual recall and public state, independently of any policy.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem acceptable_binding_commitment
    {event : (graph setup).EventId} {who : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (view : PublicView (graph setup))
    (message : Message Player (WitnessedPacket (graph setup)))
    (addressed : message.payload.call.event? (graph setup) = some event)
    (acceptable : (runtime setup).freshServiceAcceptable view message) :
    ∃ candidate, message.payload.call = .commitment event candidate := by
  rcases message with ⟨id, ⟨packet, evidence, token⟩⟩
  cases packet with
  | commitment other candidate =>
      cases Option.some.inj addressed
      exact ⟨candidate, rfl⟩
  | opening other candidate raw =>
      cases Option.some.inj addressed
      simp only [freshServiceAcceptable, freshServiceEnvelope, node] at acceptable
      exact acceptable.2.2.2.2.elim
  | withhold other => exact acceptable.elim
  | malformed raw => exact acceptable.elim

/-- An actually recorded conforming protected binding call with a unique own
identifier cannot become a public omission. Foreign responses are unrestricted. -/
theorem owner_recorded_binding_no_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {bound : (graph setup).EventId → Nat}
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player)
    (calls : OwnFreshCalls setup leaks bound control.execution who)
    (conforming : FreshCallsConform setup leaks control.execution who)
    (once : OneCallPerEvent setup leaks control.execution who)
    (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event = true) :
    control.execution.application.publicView.missedBinding event = false := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler control trace
  obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
  have named : (runtime setup).submittedEvent? leaks entry.action = some event :=
    of_decide_eq_true submitted
  obtain ⟨material, transmission⟩ : ∃ material, entry.action.transmission = some material := by
    cases sent : entry.action.transmission with
    | none => simp only [EventGraphRuntime.submittedEvent?, sent] at named; cases named
    | some material => exact ⟨material, rfl⟩
  obtain ⟨other, message, emitted, authored, addressed, submittedOther, fits⟩ :=
    calls entry member material transmission
  cases Option.some.inj (named.symm.trans submittedOther)
  have conform := conforming entry member material message transmission emitted
  have call : FreshCall setup leaks who event bound entry message := {
    fresh := ⟨material, transmission⟩
    emitted := emitted
    authored := authored
    addressed := addressed
    ready := (PublicView.ownTurn?_spec _ who event (atTurn entry member event named)).1
    fits := fits
    conforming := EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup) conform }
  obtain ⟨candidate, commitment⟩ := acceptable_binding_commitment node
    entry.beforeView.application.publicView message addressed call.conforming
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id := by
    intro other inside ⟨packet, emittedOther, authorOther, addressedOther, different⟩
    have otherMember : other ∈ control.execution.recall who := by
      rw [split]
      rcases List.mem_append.mp inside with before | after
      · exact List.mem_append_left _ before
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
    have output : packet ∈ app.outputs (control.execution.recall who) :=
      List.mem_filterMap.mpr ⟨other, otherMember, emittedOther⟩
    rw [← facts.inputs who] at output
    obtain ⟨issuer, issuerMember, issuerMaterial, issuerTransmission, issuerEmitted,
      issuerState, issuerKnown, issuerPacket⟩ :=
      facts.provenance.inputs packet (List.mem_filter.mp output).1
    have author : packet.sender = who := authorOther.trans authored
    rw [author] at issuerMember
    have issuerEvent : (runtime setup).submittedEvent? leaks issuer.action = some event := by
      unfold EventGraphRuntime.submittedEvent?
      rw [issuerTransmission]
      change (app.packet issuerState packet.sender issuerKnown issuerMaterial).call.event?
        (graph setup) = some event
      rw [issuerPacket]
      exact addressedOther
    exact different (once issuer issuerMember entry member event packet message issuerEvent
      named issuerEmitted emitted)
  exact (protected_binding_no_miss setup leaks inclusion trace event who candidate
    (nodeView_bind_actor outputEq codeEq) earlier later entry message split call commitment sole).2

private theorem newly_completed_event
    {before after : EventGraphRuntime.State (graph setup)}
    {event addressed : (graph setup).EventId}
    (unfinished : event ∉ before.config.cut.completed)
    (finished : event ∈ after.config.cut.completed)
    (ready : before.config.cut.Ready addressed) (action : (graph setup).Action addressed)
    (stepped : after.config ∈ (before.config.step addressed ready action).support) :
    event = addressed := by
  rw [before.config.step_cut addressed ready action after.config stepped] at finished
  exact ((EventOrder.Cut.mem_complete _ _ _ _).mp finished).resolve_right unfinished

/-- A new binding omission can only be created by a due explicit expiry. -/
theorem new_binding_miss_expiry
    {before after : (application setup leaks).Execution}
    (command : (application setup leaks).Command)
    (binding : before.application.BindingInvariant)
    (reached : after ∈ (before.environmentStep (application setup leaks) command).support)
    (event : (graph setup).EventId) (who : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (clear : before.application.publicView.missedBinding event = false)
    (missing : after.application.publicView.missedBinding event = true) :
    command = .application (.expire event) ∧ before.application.config.cut.Ready event ∧
      ∃ entered, before.application.activatedAt event = some entered ∧
        (runtime setup).deadline event ≤ before.application.clock - entered := by
  obtain ⟨completed, absent⟩ :=
    (after.application.publicView_missedBinding event who payload outputEq).mp missing
  have unfinished : event ∉ before.application.config.cut.completed := by
    intro earlier
    have recorded : before.application.accepted (.inr event) ≠ none := by
      intro unaccepted
      have prior := (before.application.publicView_missedBinding event who payload outputEq).mpr
        ⟨earlier, unaccepted⟩
      rw [clear] at prior
      cases prior
    cases selected : before.application.accepted (.inr event) with
    | none => exact recorded selected
    | some candidate =>
        have kept := (runtime setup).reactiveAssociationInvariant leaks (.inr event) candidate
        have associated := (kept.environmentStep before after command ⟨binding, selected⟩ reached).2
        rw [absent] at associated
        cases associated
  unfold ReactiveApplication.Execution.environmentStep at reached
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  cases command with
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact (unfinished completed).elim
  | activate player =>
      obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact (unfinished completed).elim
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
        at completed absent
      cases found : before.network.lookup id with
      | none => simp only [found] at completed; exact (unfinished completed).elim
      | some message =>
          simp only [found] at completed absent
          cases accepted : (application setup leaks).handle before.application message with
          | none =>
              simp only [accepted, Option.getD_none] at completed
              exact (unfinished completed).elim
          | some next =>
              simp only [accepted, Option.getD_some] at completed absent
              have handled := reactiveHandle_call accepted
              obtain ⟨addressed, named, ready, action, stepped⟩ :=
                handle_config_mem_step (runtime setup) before.application next _ handled
              have same := newly_completed_event unfinished completed ready action stepped
              subst addressed
              rcases message with ⟨identifier, ⟨packet, evidence, token⟩⟩
              cases packet with
              | commitment addressed candidate =>
                  cases Option.some.inj named
                  have installed := (handle_commitment_tables (runtime setup) before.application
                    next identifier event candidate handled).2.1
                  rw [installed, Function.update_self] at absent
                  cases absent
              | opening addressed candidate raw =>
                  cases Option.some.inj named
                  simp only [handle, node] at handled
                  split at handled <;> simp_all
              | withhold addressed =>
                  cases Option.some.inj named
                  simp only [handle, node] at handled
                  split at handled <;> simp_all
              | malformed raw => simp only [Payload.event?, reduceCtorEq] at named
  | application command =>
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (EventGraphRuntime.environmentStep (runtime setup)
        before.application command).support at changed
      cases command with
      | advanceClock =>
          cases (PMF.mem_support_pure_iff _ _).mp changed
          exact (unfinished completed).elim
      | executeSample addressed =>
          rcases (environmentStep_executeSample_config_activated (runtime setup)
              before.application state addressed changed).2 with
            unchanged | ⟨ready, action, stepped, _⟩
          · rw [unchanged.1] at completed
            exact (unfinished completed).elim
          · have same := newly_completed_event unfinished completed ready action stepped
            subst addressed
            have silent := environmentStep_executeSample_of_nonsample (runtime setup)
              before.application event ready (fun _ _ _ _ impossible => by
                rw [node] at impossible
                cases impossible)
            rw [silent, PMF.mem_support_pure_iff] at changed
            subst state
            exact (unfinished completed).elim
      | expire addressed =>
          rcases environmentStep_expire_config_eq_or_mem_step (runtime setup)
              before.application state addressed changed with unchanged | ⟨ready, action, stepped⟩
          · rw [unchanged] at completed
            exact (unfinished completed).elim
          · have same := newly_completed_event unfinished completed ready action stepped
            subst addressed
            refine ⟨rfl, ready, ?_⟩
            cases activated : before.application.activatedAt event with
            | none =>
                rw [environmentStep_expire_of_not_activated (runtime setup)
                  before.application event ready activated, PMF.mem_support_pure_iff] at changed
                subst state
                exact (unfinished completed).elim
            | some entered =>
                refine ⟨entered, rfl, ?_⟩
                by_contra notDue
                rw [environmentStep_expire_of_not_due (runtime setup) before.application
                  event ready entered activated notDue, PMF.mem_support_pure_iff] at changed
                subst state
                exact (unfinished completed).elim

end Vegas
