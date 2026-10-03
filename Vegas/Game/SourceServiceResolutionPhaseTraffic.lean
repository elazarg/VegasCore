/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion
import Vegas.Game.SourceServiceCanonicalConformance
import Vegas.Pending.ReactiveBindingAsyncLikelihood
import Vegas.Pending.ReactiveDecisionWindowLikelihood
import Vegas.Pending.ReactiveHiddenInclusion
import GameTheory.Math.Probability.ConditionalObservation

/-! # Actual traffic while a resolution decision waits for inclusion

Actual owner conformance identifies pending resolution packets. Authenticated
evidence and initialized trace invariants determine their inclusion results on
both sides of a focal traffic coupling. An arbitrary
public scheduler's silent round therefore preserves the complete traffic law.
Clock advancement and expiry are included in this equality; protected completion
and the matching source successor are separate semantic conclusions.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem conforming_pending_opening
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {execution : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (conform : FreshCallsConform setup leaks execution owner)
    (ready : execution.application.config.cut.Ready event)
    (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (id : MessageId Player) (candidate : Handle (graph setup)) (raw : Raw L)
    (evidence : Option (OpeningFact (graph setup)))
    (token : Option (ReadinessToken (graph setup))) (sender : id.1 = owner)
    (found : execution.network.lookup id =
      some ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩) :
    ∃ value : L.Val payload, ∃ result : PublicationResult (L.Val payload),
      raw = ⟨payload, value⟩ ∧ candidate.1 = owner ∧
      execution.application.accepted binding.field = some candidate ∧
      execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      binding.get? execution.application.config.store = some (.success value) ∧
      EventGraph.EventCode.resolveOutput? binding checks true execution.application.config.store =
        some result ∧ evidence = some ⟨candidate, ⟨payload, value⟩⟩ := by
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨entry, member, material, transmission, emitted, state, known, packet⟩ :=
    facts.provenance.pending message (List.mem_of_find?_eq_some found)
  have authored : message.sender = owner := sender
  rw [authored] at member
  have conforming := conform entry member material message transmission emitted
  obtain ⟨seenReady, _, certified, guards, _, owned, associatedThen, _, _⟩ :=
    ((runtime setup).freshServiceEnvelope_opening_iff entry.beforeView.application.publicView
      id event owner payload binding checks outputEq codeEq node candidate raw evidence
      token).mp conforming
  obtain ⟨value, rawEq, publicChecks⟩ :=
    (entry.beforeView.application.publicView.openingGuardsAccepted_iff owner event payload
      binding checks outputEq codeEq node candidate raw evidence).mp guards
  have current := entry_view_current setup leaks execution facts.stable owner entry member
    event seenReady ready.1
  have associated : execution.application.accepted binding.field = some candidate := by
    rw [← current.2.1]
    exact associatedThen
  have certificate : evidence = some ⟨candidate, raw⟩ := by
    cases evidence with
    | none => simp only [certifiedOpening, Bool.false_eq_true] at certified
    | some fact =>
        simp only [certifiedOpening, decide_eq_true_eq] at certified
        exact congrArg some certified
  have fixed : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ := by
    apply facts.evidence.pending message (List.mem_of_find?_eq_some found)
      ⟨candidate, ⟨payload, value⟩⟩
    change ⟨candidate, ⟨payload, value⟩⟩ ∈ evidence.toList
    simp only [certificate, rawEq, Option.toList_some, List.mem_singleton]
  have stored := facts.binding.opening_stored binding candidate value associated fixed
  have acceptedChecks : EventGraph.GuardCheck.allAccepted? checks execution.application.config.store
      (.success value) = some true := by
    rw [current.1] at publicChecks
    change EventGraph.GuardCheck.allAccepted? checks
      ((graph setup).publicStore execution.application.config.store) (.success value) = some true
      at publicChecks
    rwa [EventGraph.GuardCheck.allAccepted?_publicStore] at publicChecks
  refine ⟨value, .success value, rawEq, owned, associated, fixed, stored, ?_, ?_⟩
  · simp only [EventGraph.EventCode.resolveOutput?, stored, Option.bind_eq_bind,
      Option.bind_some, ↓reduceIte, acceptedChecks, Option.pure_def]
  · rw [certificate, rawEq]

private theorem conforming_resolution_include_traffic
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {left right : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId}
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, none, left⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, none, right⟩))
    (conform : FreshCallsConform setup leaks left owner)
    (ready : left.application.config.cut.Ready event)
    (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) (id : MessageId Player) :
    (runtime setup).bindingTraffic leaks focal (left.includePending (application setup leaks) id) =
      (runtime setup).bindingTraffic leaks focal
        (right.includePending (application setup leaks) id) := by
  have networks := congrArg Prod.fst same
  have views := congrArg (fun read => read.2.2.2.2.1) same
  have publics := congrArg (fun read => read.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks views publics
  have sole := soleReady_of_ready setup left.application ready
  have readyEq (target : (graph setup).EventId) :
      left.application.config.cut.Ready target ↔ right.application.config.cut.Ready target := by
    rw [← State.publicView_eventReady, ← State.publicView_eventReady, publics]
  have timelyEq (target : (graph setup).EventId) :
      left.application.WithinDeadline (runtime setup) target ↔
        right.application.WithinDeadline (runtime setup) target := by
    change left.application.publicView.WithinDeadline (runtime setup) target ↔
      right.application.publicView.WithinDeadline (runtime setup) target
    rw [publics]
  cases found : left.network.lookup id with
  | none =>
      have rightFound : right.network.lookup id = none := networks ▸ found
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, rightFound] using same
  | some message =>
      have identified : message.id = id :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
      rcases message with ⟨messageId, ⟨packet, evidence, token⟩⟩
      dsimp only at identified
      subst messageId
      apply (runtime setup).bindingTraffic_include_of_handler leaks left right focal same id
        ⟨id, ⟨packet, evidence, token⟩⟩ found
      simp only [reactiveApplication_handle]
      split
      swap
      · rfl
      cases packet with
      | commitment target candidate =>
          exact handle_commitment_playerView_congr (runtime setup) left.application
            right.application focal id target candidate views
      | malformed raw => simp only [handle, Option.map_none]
      | withhold target =>
          by_cases own : id.1 = focal
          · exact handle_playerView_congr_of_sender (runtime setup) left.application
              right.application focal ⟨id, .withhold target⟩ views own
          · exact handle_withhold_playerView_congr_of_sender_ne (runtime setup) left.application
              right.application focal id target views own
      | opening target candidate raw =>
          by_cases currentReady : left.application.config.cut.Ready target
          · have current : target = event := sole.2 target
              ((left.application.publicView_eventReady target).mpr currentReady)
            subst target
            have rightReady := (readyEq event).mp ready
            by_cases timely : left.application.WithinDeadline (runtime setup) event
            · have rightTimely := (timelyEq event).mp timely
              by_cases sender : id.1 = owner
              · obtain ⟨value, result, rawEq, owned, associated, fixed, stored,
                    resolved, certificate⟩ :=
                  conforming_pending_opening setup leaks leftTrace conform ready payload
                    binding checks outputEq codeEq node id candidate raw evidence token sender found
                have rightFound : right.network.lookup id =
                    some ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩ := networks ▸ found
                have rightFacts := legalFacts setup leaks horizon scheduler _ rightTrace
                have rightFixed : right.application.candidates.lookup candidate =
                    .openable ⟨payload, value⟩ := by
                  apply rightFacts.evidence.pending
                    ⟨id, ⟨.opening event candidate raw, evidence, token⟩⟩
                    (List.mem_of_find?_eq_some rightFound) ⟨candidate, ⟨payload, value⟩⟩
                  change ⟨candidate, ⟨payload, value⟩⟩ ∈ evidence.toList
                  simp only [certificate, Option.toList_some, List.mem_singleton]
                have rightAssociated : right.application.accepted binding.field =
                    some candidate := by
                  have accepted := congrArg PublicView.accepted publics
                  change left.application.accepted = right.application.accepted at accepted
                  rw [← accepted]
                  exact associated
                have rightStored := rightFacts.binding.opening_stored binding candidate value
                  rightAssociated rightFixed
                rw [rawEq]
                exact (runtime setup).handle_opening_unrepaired_congr left.application
                  right.application focal views id event candidate owner payload binding checks
                  outputEq codeEq node ready timely sender owned associated value fixed rightFixed
                  stored rightStored result resolved
              · simp only [handle, dite_eq_left ready, dite_eq_left rightReady,
                  dite_eq_left timely, dite_eq_left rightTimely, node, Message.sender,
                  dite_eq_right sender, Option.map_none]
            · have rightLate : ¬right.application.WithinDeadline (runtime setup) event :=
                fun within => timely ((timelyEq event).mpr within)
              simp only [handle, dite_eq_left ready, dite_eq_left rightReady,
                dite_eq_right timely, dite_eq_right rightLate, Option.map_none]
          · have rightNotReady : ¬right.application.config.cut.Ready target :=
              fun ready => currentReady ((readyEq target).mpr ready)
            simp only [handle, dite_eq_right currentReady, dite_eq_right rightNotReady,
              Option.map_none]

/-- The actual public scheduler's next command preserves focal traffic at a
resolution when all responses are silent. Actual owner conformance identifies
relevant openings; trace evidence authenticates their private values on both sides. -/
theorem source_resolution_conforming_silent_round
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {left right : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId}
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, none, left⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, none, right⟩))
    (conform : FreshCallsConform setup leaks left owner)
    (ready : left.application.config.cut.Ready event)
    (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ((application setup leaks).round scheduler
        (fun _ => (application setup leaks).silentPolicy) left).map
          ((runtime setup).bindingTraffic leaks focal) =
      ((application setup leaks).round scheduler
        (fun _ => (application setup leaks).silentPolicy) right).map
          ((runtime setup).bindingTraffic leaks focal) := by
  let app := application setup leaks
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun read => read.2.1) same
  have environments := congrArg (fun read => read.2.2.1) same
  have publics := congrArg (fun read => read.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts environments publics
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts =
        ReactiveApplication.EnvironmentView.mk right.network.publicView
          right.application.publicView right.receipts
    rw [networks, publics, receipts]
  have sole := soleReady_of_ready setup left.application ready
  have rightSole : right.application.publicView.SoleReady event := publics ▸ sole
  have sampleLaw (state : EventGraphRuntime.State (graph setup))
      (only : state.publicView.SoleReady event) (target : (graph setup).EventId) :
      environmentStep (runtime setup) state (.executeSample target) = PMF.pure state := by
    by_cases sampleReady : state.config.cut.Ready target
    · have current : target = event := only.2 target
        ((state.publicView_eventReady target).mpr sampleReady)
      subst target
      apply environmentStep_executeSample_of_nonsample (runtime setup) state event sampleReady
      intro ty law output code sample
      rw [node] at sample
      cases sample
    · exact environmentStep_executeSample_of_not_ready (runtime setup) state target sampleReady
  have waiting : app.resume (fun _ => app.silentPolicy) none = PMF.pure := rfl
  dsimp only [app] at waiting
  simp only [ReactiveApplication.round, PMF.map_bind, environments]
  rw [environment]
  apply bind_congr_on_support _
  intro command _
  cases command with
  | activate actor =>
      exact (runtime setup).bindingTraffic_silent_activation leaks focal actor left right same
  | «include» id =>
      have coupled := conforming_resolution_include_traffic setup leaks leftTrace rightTrace conform
        ready payload binding checks outputEq codeEq node focal same id
      simpa only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
        PMF.pure_bind, PMF.map_comp, bindingTraffic, Function.comp_apply, environments,
        environment, app] using
        congrArg (fun traffic => PMF.pure (traffic.1, traffic.2.1,
          right.environmentRecall ++ [⟨right.observeEnvironment app, .include id⟩],
            traffic.2.2.2)) coupled
  | wait =>
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
        PMF.pure_bind]
      simpa only [bindingTraffic, Function.comp_apply, environments, environment, app] using
        congrArg (fun traffic => PMF.pure (traffic.1, traffic.2.1,
          right.environmentRecall ++ [⟨right.observeEnvironment app, .wait⟩],
            traffic.2.2.2)) same
  | application command =>
      cases command with
      | advanceClock =>
          simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure, app] using
            (runtime setup).bindingTraffic_maintenance leaks left right focal same .advanceClock
              (by intro query impossible; cases impossible)
      | expire target =>
          simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure, app] using
            (runtime setup).bindingTraffic_maintenance leaks left right focal same (.expire target)
              (by intro query impossible; cases impossible)
      | executeSample target =>
          have leftLaw : app.environment left.application (.executeSample target) =
              PMF.pure left.application := sampleLaw left.application sole target
          have rightLaw : app.environment right.application (.executeSample target) =
              PMF.pure right.application := sampleLaw right.application rightSole target
          dsimp only [app] at leftLaw rightLaw
          simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure, ReactiveApplication.Execution.environmentStep,
            leftLaw, rightLaw, PMF.pure_map]
          simpa only [bindingTraffic, Function.comp_apply, environments, environment, app] using
            congrArg (fun traffic => PMF.pure (traffic.1, traffic.2.1,
              right.environmentRecall ++ [⟨right.observeEnvironment app,
                .application (.executeSample target)⟩], traffic.2.2.2)) same

/-- Silent rounds preserve the actual owner's prior packet conformance,
including any earlier deferral entries. -/
theorem freshCallsConform_silent_round
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (owner : Player)
    {execution next : (application setup leaks).Execution}
    (conform : FreshCallsConform setup leaks execution owner)
    (reached : next ∈ ((application setup leaks).round scheduler
      (fun _ => (application setup leaks).silentPolicy) execution).support) :
    FreshCallsConform setup leaks next owner := by
  let app := application setup leaks
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have recalled := app.environmentStep_recall execution middle command moved
  have conformMiddle : FreshCallsConform setup leaks middle owner := by
    unfold FreshCallsConform
    rw [recalled]
    exact conform
  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, chosen, rfl⟩
  · exact conformMiddle
  · have responseEq : response = ⟨none⟩ := app.mem_silentPolicy_support.mp chosen
    subst response
    by_cases own : responder = owner
    · subst responder
      obtain ⟨emitted, recallEq, _⟩ := respond_recall_self setup leaks middle owner ⟨none⟩
      intro entry member material message transmission issued
      rw [recallEq] at member
      rcases List.mem_append.mp member with old | recent
      · exact conformMiddle entry old material message transmission issued
      · rw [List.mem_singleton] at recent
        subst entry
        cases transmission
    · unfold FreshCallsConform
      rw [app.respond_recall_other middle responder owner (Ne.symm own) ⟨none⟩]
      exact conformMiddle

/-- Recording a decision makes its fixed first-turn policy silent at every
subsequent actual scheduler activation. The complete physical round law agrees,
including passive samples and all players' recall. -/
theorem decidedProfile_round_of_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bound : (graph setup).EventId → Nat) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event)
    (scheduler : (application setup leaks).Scheduler)
    (execution : (application setup leaks).Execution)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true) :
    (application setup leaks).round scheduler
        (decidedProfile (leaks := leaks) bound owner event action) execution =
      (application setup leaks).round scheduler
        (fun _ => (application setup leaks).silentPolicy) execution := by
  let app := application setup leaks
  simp only [ReactiveApplication.round]
  apply bind_congr_on_support _
  intro command _
  simp only [ReactiveApplication.dispatch]
  apply bind_congr_on_support _
  intro middle moved
  have recalled := app.environmentStep_recall execution middle command moved
  cases actor : command.actor? app with
  | none => rfl
  | some who =>
      have policy : decidedProfile (leaks := leaks) bound owner event action who
          (middle.recall who) (middle.observe app who) =
        app.silentPolicy (middle.recall who) (middle.observe app who) := by
        by_cases own : who = owner
        · subst who
          simp only [decidedProfile, Function.update_self, decidedTurnPolicy,
            ReactiveApplication.turnScheduledPolicy]
          split
          · simp only [decidedOpportunity, recalled, recorded, ite_true]
            rfl
          · rfl
        · simp only [decidedProfile, Function.update_of_ne own]
          rfl
      simp only [ReactiveApplication.resume, ReactiveApplication.invoke]
      exact congrArg (fun law => law.map (middle.respond app who)) policy

/-- Actual recorded conforming decisions preserve an existing joint channel for
carried source data. This does not identify the carrier with an expired runtime
configuration; the protected completion theorem supplies that semantic step. -/
theorem source_async_resolution_phase_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (focal : Player) (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (execution : Seed → (application setup leaks).Execution)
    (remaining : Seed → Nat) (bound : (graph setup).EventId → Nat)
    (event : (graph setup).EventId) (owner : Player) (action : Seed → (graph setup).Action event)
    (trace : ∀ seed ∈ prior.support,
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining seed, none, execution seed⟩))
    (conform : ∀ seed ∈ prior.support, FreshCallsConform setup leaks (execution seed) owner)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (recorded : ∀ seed ∈ prior.support,
      (runtime setup).eventRecorded leaks ((execution seed).recall owner) event = true)
    (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (observe config)).map fun extra => (config, extra)) :
    ∃ nextNoise : View → PMF _,
      (prior.bind fun seed =>
        ((application setup leaks).round scheduler
          (decidedProfile (leaks := leaks) bound owner event (action seed))
            (execution seed)).map fun final =>
              (source seed, (runtime setup).bindingTraffic leaks focal final)) =
      (prior.map source).bind fun config =>
        (nextNoise (observe config)).map fun extra => (config, extra) := by
  have silent seed (supported : seed ∈ prior.support) :=
    decidedProfile_round_of_recorded setup leaks bound owner event (action seed) scheduler
      (execution seed) (recorded seed supported)
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    observe noise factor (fun _ => PMF.pure Unit.unit) (fun config _ => config) observe
    (fun seed _ => ((application setup leaks).round scheduler
      (decidedProfile (leaks := leaks) bound owner event (action seed)) (execution seed)).map
        ((runtime setup).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (by
      intro left leftSupport _ _ right rightSupport _ _ _ same
      rw [silent left leftSupport, silent right rightSupport]
      exact source_resolution_conforming_silent_round setup leaks (trace left leftSupport)
        (trace right rightSupport) (conform left leftSupport)
        (ready left leftSupport) payload binding checks outputEq codeEq node focal same)
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, PMF.map_id,
    PMF.map_comp, Function.comp_def] using law

end Vegas
