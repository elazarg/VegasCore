/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalSerial
import Vegas.Game.SourceServiceProtectedBinding
import Vegas.Game.SourceServiceFirstTurnRisk

/-! # Owner-local exclusion of public binding omissions

A recorded protected commitment of an owner following the turn-counted source
policy cannot become a public omission, whatever the other players do. Under
the asynchronous opportunity and timing requirements, exact first-turn play
keeps every owned binding omission flag clear. Silent deferrals remain distinct
from recorded binding calls.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

variable {setup leaks}

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

/-- An event actually recorded by the owner's turn-counted source policy cannot
become a public binding omission. The other players' raw policies are arbitrary. -/
theorem sourceServiceTurnPolicy_recorded_binding_no_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall who) event = true) :
    execution.application.publicView.missedBinding event = false := by
  let app := application setup leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    count within execution reached
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨calls, once, _⟩ := serialFacts_roundsFrom contract players who timing profile follows
    count within execution reached
  have atTurn := (canonicalSlots_roundsFrom scheduler players who timing profile follows
    count execution reached).1
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
  have conform := sourceServiceTurnPolicy_freshServiceEnvelope scheduler players who timing profile
    follows count execution reached entry member material transmission message emitted
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
    have otherMember : other ∈ execution.recall who := by
      rw [split]
      rcases List.mem_append.mp inside with before | after
      · exact List.mem_append_left _ before
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
    have output : packet ∈ app.outputs (execution.recall who) :=
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
  exact (protected_binding_no_miss setup leaks contract.inclusion trace event who candidate
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

private theorem new_binding_miss_expiry
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

/-- Exact first-turn source play keeps this owner's binding event clear on every
supported scheduler round, with arbitrary raw policies of the other players. -/
theorem sourceServiceFirstTurn_binding_no_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    execution.application.publicView.missedBinding event = false := by
  let app := application setup leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, initial, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ initial
      simp only [PublicView.missedBinding, outputEq, ReactiveApplication.Execution.initial,
        State.initial, State.publicView, EventGraph.publicObserve, EventGraph.Config.initial,
        List.map_nil, List.not_mem_nil, decide_false, Bool.false_and]
  | succ count ih =>
      have reachedNext := reached
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have clear := ih (by omega) prior priorMem
      apply Bool.eq_false_of_not_eq_true
      intro missing
      by_cases recorded : (runtime setup).eventRecorded leaks (execution.recall who) event = true
      · have good := sourceServiceTurnPolicy_recorded_binding_no_miss contract players who
          (firstTurnTiming setup turns) profile follows (count + 1) within execution reachedNext
          event payload outputEq codeEq node recorded
        rw [good] at missing
        cases missing
      · obtain ⟨command, _, middle, dispatched, effect⟩ := round_cases setup leaks moved
        have middleMissing : middle.application.publicView.missedBinding event = true := by
          rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
          · exact missing
          · have same := (runtime setup).reactive_respond_application leaks middle actor response
            exact (congrArg (fun view : PublicView (graph setup) => view.missedBinding event)
              same.2).symm.trans missing
        obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
          count (by omega) prior priorMem
        have facts := legalFacts setup leaks horizon scheduler _ trace
        obtain ⟨_, ready, entered, activated, due⟩ := new_binding_miss_expiry command facts.binding
          dispatched event who payload outputEq codeEq node clear middleMissing
        change (runtime setup).deadline event ≤ prior.application.clock - entered at due
        have owned := nodeView_bind_actor outputEq codeEq
        have delayFits := timely event (by rw [owned]; rfl)
        obtain ⟨entry, recalled, turn⟩ := opportunity_turn contract trace
          (roundsFrom_activationsAnswered count prior priorMem) owned ready entered activated
          (by change entered + delay event < prior.application.clock; omega)
        have turned := (sourceServiceFirstTurn_recallFacts contract timely players who turns
          profile follows count (by omega) prior priorMem).1
        have recordedPrior := turned entry recalled event who payload turn outputEq
        have grows : prior.recall who ⊆ execution.recall who := by
          have same := app.environmentStep_recall prior middle command dispatched
          rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
          · rw [same]
          · rw [← same]
            exact app.respond_recall_mono middle actor who response
        obtain ⟨call, member, named⟩ := List.any_eq_true.mp recordedPrior
        exact recorded (List.any_eq_true.mpr ⟨call, grows member, named⟩)

/-- The owner's entire public omission detector is clear under exact first-turn
play. No restrictions are placed on the other players' raw responses. -/
theorem sourceServiceFirstTurn_no_public_miss {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    execution.application.publicView.missedBindingBy who = false := by
  classical
  apply decide_eq_false
  rintro ⟨event, owned, missing⟩
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst owner
      have clear := sourceServiceFirstTurn_binding_no_miss contract timely players who turns
        profile follows count within execution reached event payload outputEq codeEq node
      rw [clear] at missing
      cases missing

/-- Covers the actual public record at a pending activation as well as completed
scheduler rounds. An activation changes only the activated player's message sample. -/
theorem sourceServiceFirstTurn_no_public_miss_roundSupported {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some control)) :
    control.execution.application.publicView.missedBindingBy who = false := by
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      have within : execution.environmentRecall.length ≤ horizon := by
        have lengths := reached.1
        change execution.environmentRecall.length + remaining = horizon at lengths
        omega
      exact sourceServiceFirstTurn_no_public_miss contract timely players who turns profile follows
        _ within execution reached.2
  | some responder =>
      obtain ⟨lengthEq, count, prior, command, _, priorMem, _, active, moved⟩ := reached
      have clear := sourceServiceFirstTurn_no_public_miss contract timely players who turns
        profile follows count (by omega) prior priorMem
      cases command with
      | activate actor =>
          rw [activation_application setup leaks prior execution actor moved]
          exact clear
      | wait | «include» id | application command => cases active

end Vegas
