/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingResponseFactorization
import Vegas.Game.SourceServiceStoppedBindingTraffic
import Interaction.ReactiveSupportedMenuPolicy

/-! # Typed binding responses through protected completion

The transmitting branch of the actual geometric response law initializes an
actual protected packet. Completion stopping accepts this same packet and
records its drawn typed source value. The conditional traffic law retains the
whole source pair and full runtime traffic; waiting remains a separate branch.

Packet completion permits arbitrary foreign policies. The traffic result uses
prescribed foreign continuations, whose responses are silent while the binding
is recorded. Neither result asserts a native posterior or an equilibrium.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A source-supported transmitting draw at an actual protected input is a
supported physical response. Earlier protected waits are permitted. -/
theorem sourceServiceDecision_clear_binding_supported {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (value : PublicationResult (L.Val site.payload))
    (sampled : value ∈ (commitKernel site.residual (site.source.view site.owner)).support) :
    (runtime setup).reactiveBinding leaks site.owner event site.payload value
        (execution.application.publicView.bindingCount site.owner) ∈
      (sourceServiceTurnPolicy setup leaks bound horizon
        (geometricTiming setup horizon weight positive.le below.le) profile site.owner
        (execution.recall site.owner) (execution.observe (application setup leaks) site.owner)
      ).support := by
  rw [sourceServiceDecision_clear_binding_response bounds bound profile execution event site
    trace clear unrecorded turn fits weight positive below]
  exact mem_support_mix_right weight positive.le below.le below
    (by rw [PMF.support_map]; exact ⟨value, sampled, rfl⟩)

omit [Fintype Player] in
/-- A supported actual owner response finishes the pending activation into a
supported initialized round boundary. The remaining horizon is derived from
that same physical activation. -/
theorem sourceService_binding_response_initialized {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (execution : (application setup leaks).Execution)
    (initialized : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some owner, execution⟩))
    (response : (application setup leaks).Action)
    (chosen : response ∈ (players owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)).support) :
    let next := execution.respond (application setup leaks) owner response
    next.environmentRecall.length ≤ horizon ∧
      next ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler players
        next.environmentRecall.length).support := by
  have reached : some ⟨remaining, none,
      execution.respond (application setup leaks) owner response⟩ ∈
      ((application setup leaks).controlStep (initialLaw setup) horizon scheduler players
        (some ⟨remaining, some owner, execution⟩)).support := by
    simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
      ReactiveApplication.transition, ↓reduceIte, Option.getD_some, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨response, chosen, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  have supported := (application setup leaks).roundSupported_controlStep (initialLaw setup)
    horizon scheduler players _ _ initialized reached
  exact ⟨by have budget := supported.1; dsimp only at budget; omega, supported.2⟩

/-- The actual newly submitted packet, rather than an independently supplied
source endpoint, fixes every protected stopped successor to the drawn value.
Only the binding owner follows the prescribed policy. -/
theorem sourceServiceDecision_clear_binding_completion {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (bounds : MessageBounds (graph setup))
    (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (initialized : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (follows : players site.owner = sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight positive.le below.le) profile site.owner)
    (value : PublicationResult (L.Val site.payload))
    (sampled : value ∈ (commitKernel site.residual (site.source.view site.owner)).support) :
    let response := (runtime setup).reactiveBinding leaks site.owner event site.payload value
      (execution.application.publicView.bindingCount site.owner)
    let next := execution.respond (application setup leaks) site.owner response
    ∃ entry ∈ next.recall site.owner, ∃ message,
      entry.action = response ∧ FreshCall setup leaks site.owner event bound entry message ∧
      ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon next).support,
        entry ∈ stopped.recall site.owner ∧ (message.id, true) ∈ stopped.receipts ∧
        event ∉ stopped.application.missedEvents ∧
        stopped.application.config = execution.application.config.complete event
          ((execution.application.publicView_eventReady event).mp
            (PublicView.ownTurn?_spec _ site.owner event turn).1)
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value) ∧
        (site.refs.cons (name := site.name) ⟨.inr event, site.outputEq⟩).Agrees
          (commitSuccessor site.name site.guard site.source value).state
          stopped.application.config.store ∧
        decodeHistory setup.program (stopped.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) =
            (commitSuccessor site.name site.guard site.source value).history := by
  let app := application setup leaks
  let timing := geometricTiming setup horizon weight positive.le below.le
  let serial := execution.application.publicView.bindingCount site.owner
  let response := (runtime setup).reactiveBinding leaks site.owner event site.payload value serial
  let next := execution.respond app site.owner response
  have chosen : response ∈ (players site.owner (execution.recall site.owner)
      (execution.observe app site.owner)).support := by
    rw [follows]
    exact sourceServiceDecision_clear_binding_supported bounds bound profile execution event
      site trace clear unrecorded turn fits weight positive below value sampled
  obtain ⟨within, reached⟩ := sourceService_binding_response_initialized players site.owner
    execution initialized response chosen
  have configEq : next.application.config = execution.application.config :=
    ((runtime setup).reactive_respond_application leaks execution site.owner response).1
  have ready : next.application.config.cut.Ready event := by
    rw [configEq]
    exact ((execution.application.publicView_eventReady event).mp
            (PublicView.ownTurn?_spec _ site.owner event turn).1)
  have submitted : (runtime setup).submittedEvent? leaks response = some event := rfl
  have recorded := (runtime setup).eventRecorded_respond leaks execution site.owner response
    event submitted
  obtain ⟨entry, member, message, named, call, completion⟩ :=
    sourceServiceTurnPolicy_recorded_decision_completion contract players site.owner timing
      profile follows next.environmentRecall.length within next reached event site.owned recorded
  let material : app.Submission :=
    ⟨⟨.commitment event (site.owner, .prepared serial),
      (PublicationResult.equivOption value).map (fun val => ⟨site.payload, val⟩)⟩, .none⟩
  have responseEq : response = ⟨some material⟩ := by cases value <;> rfl
  have recallEq := respond_submit_recall execution site.owner material
  rw [← responseEq] at recallEq
  have originalMember := member
  rw [recallEq, List.mem_append] at member
  have entryEq : entry = ⟨execution.observe (application setup leaks) site.owner, response,
      some ⟨(site.owner, execution.network.nextSerial site.owner), app.packet
        (app.submit execution.application site.owner material) site.owner
          (execution.network.known site.owner) material⟩⟩ := by
    rcases member with earlier | last
    · have impossible := (runtime setup).eventRecorded_iff leaks _ event |>.mpr
        ⟨entry, earlier, named⟩
      rw [unrecorded] at impossible
      cases impossible
    · exact List.mem_singleton.mp last
  have actual : entry.action = response := congrArg ReactiveApplication.PlayerEntry.action entryEq
  have actualMessage : message.payload.call = .commitment event (site.owner, .prepared serial) := by
    have emittedEq := congrArg ReactiveApplication.PlayerEntry.emitted entryEq
    rw [call.emitted] at emittedEq
    cases Option.some.inj emittedEq
    rw [reactiveApplication_packet_none]
  have fresh := sourceService_clear_counted_candidate_fresh bounds bound site.owner execution
    trace clear event unrecorded turn
  have realized : RealizesAt leaks next.application.config next.application event
      (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value) entry message := by
    unfold RealizesAt
    rw [nodeView_eq_bind site.outputEq site.code]
    refine ⟨(site.owner, .prepared serial), actualMessage, ?_, ?_⟩
    · change (submitStep _ site.owner (.commitment event (site.owner, .prepared serial)
        )).candidates.lookup (site.owner, .prepared serial) ≠ .fresh
      exact submitStep_commitment_fixed _ site.owner event (.prepared serial)
    · simpa only [cast_cast, cast_eq] using (runtime setup).reactiveBinding_result leaks
        site.owner event site.payload value serial execution fresh
  refine ⟨entry, originalMember, message, actual, call, ?_⟩
  intro stopped stoppedSupported
  obtain ⟨retained, _, accepted, noMiss⟩ := completion stopped stoppedSupported
  have native := sourceServiceTurnPolicy_recorded_realization_completion contract players
    site.owner timing profile follows next.environmentRecall.length within next reached event
    site.owned ready (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
    entry originalMember message named call realized stopped stoppedSupported
  rw [commit_step next.application.config event ready site.outputEq site.code value,
    PMF.mem_support_pure_iff] at native
  have exactConfig : stopped.application.config = execution.application.config.complete event
      ((execution.application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ site.owner event turn).1)
      (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
      (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value) := by
    simpa only [configEq] using native
  refine ⟨retained, accepted, noMiss, exactConfig, ?_, ?_⟩
  · rw [exactConfig]
    intro name cell ref
    exact complete_commit_agrees (graph := graph setup) site.name site.guard site.source site.refs
      execution.application.config site.agree event
      ((execution.application.publicView_eventReady event).mp
            (PublicView.ownTurn?_spec _ site.owner event turn).1) site.outputEq (by
        intro name cell ref
        have ordered := site.refsBefore ref ⟨0, by simp [eventCount]⟩
        rw [site.head] at ordered
        exact ordered) value ref
  · rw [exactConfig]
    change decodeHistory setup.program ((execution.application.config.history ++
      [(⟨event, cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value⟩ :
        EventGraph.Completion (graph setup))]).map
        (setup.eventGraph.fromModeCompletion .sequential)) = _
    rw [List.map_append, List.map_singleton]
    have decoded := decodeHistory_append_completion setup.program
      (execution.application.config.history.map (setup.eventGraph.fromModeCompletion .sequential))
      event (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
    rw [site.action value, site.history] at decoded
    exact decoded

/-- The actual response draw either waits, retaining its current traffic, or
completes its selected typed binding before stopping. Its realized completion
and full traffic are read jointly. The transmitting branch has mass `1-weight`.
-/
theorem sourceServiceDecision_clear_binding_stopped_joint {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (bounds : MessageBounds (graph setup))
    (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (initialized : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (follows : players site.owner = sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight positive.le below.le) profile site.owner)
    (focal : Player) :
    (players site.owner (execution.recall site.owner)
        (execution.observe (application setup leaks) site.owner)).bind (fun response =>
      if response.transmission.isSome then
        ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution.respond (application setup leaks) site.owner response)).map fun final =>
            (bindingResponseResult? site.owner site.payload execution response,
              final.application.config, (runtime setup).bindingTraffic leaks focal final)
      else PMF.pure (none, execution.application.config,
        (runtime setup).bindingTraffic leaks focal
          (execution.respond (application setup leaks) site.owner response))) =
      mix weight positive.le below.le
        (PMF.pure (none, execution.application.config,
          (runtime setup).bindingTraffic leaks focal
            (execution.respond (application setup leaks) site.owner ⟨none⟩)))
        ((commitKernel site.residual (site.source.view site.owner)).bind fun value =>
          ((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution.respond (application setup leaks) site.owner
              ((runtime setup).reactiveBinding leaks site.owner event site.payload value
                (execution.application.publicView.bindingCount site.owner)))).map fun final =>
              (some value, execution.application.config.complete event
                ((execution.application.publicView_eventReady event).mp
                  (PublicView.ownTurn?_spec _ site.owner event turn).1)
                (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
                (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value),
                (runtime setup).bindingTraffic leaks focal final)) := by
  rw [follows, sourceServiceDecision_clear_binding_response bounds bound profile execution event
    site trace clear unrecorded turn fits weight positive below, mix_bind, PMF.pure_bind]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, PMF.bind_map]
  congr 1
  apply bind_congr_on_support _
  intro value sampled
  have resultEq : bindingResponseResult? site.owner site.payload execution
      ((runtime setup).reactiveBinding leaks site.owner event site.payload value
        (execution.application.publicView.bindingCount site.owner)) = some value := by
    change some ((execution.respond (application setup leaks) site.owner
      ((runtime setup).reactiveBinding leaks site.owner event site.payload value
        (execution.application.publicView.bindingCount site.owner))).application.bindingResult
          (site.owner, .prepared (execution.application.publicView.bindingCount site.owner))
          site.payload) = some value
    exact congrArg some ((runtime setup).reactiveBinding_result leaks site.owner event site.payload
      value (execution.application.publicView.bindingCount site.owner) execution
      (sourceService_clear_counted_candidate_fresh bounds bound site.owner execution trace clear
        event unrecorded turn))
  obtain ⟨entry, _, message, _, _, completion⟩ := sourceServiceDecision_clear_binding_completion
    contract bounds profile players execution event site trace initialized clear unrecorded
      turn fits weight positive below follows value sampled
  apply map_congr_on_support _
  intro stopped supported
  obtain ⟨_, _, _, native, _, _⟩ := completion stopped supported
  exact Prod.ext resultEq (Prod.ext native rfl)

omit [Fintype Player] in
private theorem binding_transmission_response_factorization
    {Seed : Type} {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (focal : Player) (event : (graph setup).EventId)
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (choice : (Config Player L Γ × Config Player L Γ) →
      PMF (PublicationResult (L.Val payload)))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (source seed, original seed)).map fun value =>
        ((commitSuccessor name guard (source seed) value,
          commitSuccessor name guard (original seed) value),
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              (bindingChoiceResponse owner event payload (execution seed) (some value))))) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (choice pair).map fun value => (commitSuccessor name guard pair.1 value,
          commitSuccessor name guard pair.2 value)).bind fun next =>
            (nextNoise (next.1.view focal)).map fun extra => (next, extra) := by
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor choice
    (fun pair value => (commitSuccessor name guard pair.1 value,
      commitSuccessor name guard pair.2 value)) (fun pair => pair.1.view focal)
    (fun seed value => PMF.pure ((runtime setup).bindingTraffic leaks focal
      ((execution seed).respond (application setup leaks) owner
        (bindingChoiceResponse owner event payload (execution seed) (some value)))))
    (by
      intro left _ first _ right _ second _ same
      have earlier := congrArg (DecisionView.back (decide (owner = focal))) same
      simpa only [back_commit_view] using earlier)
    (by
      intro left _ first _ right _ second _ same traffic
      have visible : focal = owner → first = second := by
        intro equal
        subst focal
        have cell := congrArg
          (fun view : DecisionView owner ((name, .commitment owner payload) :: Γ) =>
            view.1.cells.get .here) same
        simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons,
          ite_true] at cell
        exact Option.some.inj cell
      have publics := congrArg (fun read => read.2.2.2.2.2) traffic
      dsimp only [bindingTraffic] at publics
      have serialEq := congrArg (fun view => view.bindingCount owner) publics
      exact congrArg PMF.pure (by
        simpa only [bindingChoiceResponse, serialEq] using
          (runtime setup).bindingTraffic_binding_response leaks (execution left)
            (execution right) owner focal event payload first second visible
            ((execution left).application.publicView.bindingCount owner) traffic))
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_map, ← PMF.bind_pure_comp, PMF.pure_bind, Function.comp_def] using law

omit [Fintype Player] in
/-- The complete transmitting branch has the aligned source-successor law and
its full actual traffic channel through delayed stopping. This channel lemma
is paired below with actual initialized packet and typed endpoint realization;
it does not presume those operational facts in the probability calculation. -/
theorem source_binding_transmission_stopped_factorization
    {Seed : Type} {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    {names : Finset VarId} (name : VarId) (freshName : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names))
    (profile : BehavioralProfile setup.program)
    (residual : BehavioralProfile (.commit name owner freshName guard next))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (bound : (graph setup).EventId → Nat) {turns : Nat} (timing : TurnTiming setup turns)
    (focal : Player) (event : (graph setup).EventId)
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → PMF _,
      (prior.bind fun seed => (commitKernel residual ((source seed).view owner)).bind fun value =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns timing profile)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          ((execution seed).respond (application setup leaks) owner
            (bindingChoiceResponse owner event payload (execution seed) (some value)))).map
            fun final => ((commitSuccessor name guard (source seed) value,
              commitSuccessor name guard (original seed) value),
              (runtime setup).bindingTraffic leaks focal final)) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        ((commitKernel residual (pair.1.view owner)).map fun value =>
          (commitSuccessor name guard pair.1 value,
            commitSuccessor name guard pair.2 value))).bind fun next =>
              (nextNoise (next.1.view focal)).map fun extra => (next, extra) := by
  let decisions := prior.bind fun seed =>
    (commitKernel residual ((source seed).view owner)).map fun value => (seed, value)
  let successor := fun draw : Seed × PublicationResult (L.Val payload) =>
    (commitSuccessor name guard (source draw.1) draw.2,
      commitSuccessor name guard (original draw.1) draw.2)
  let submitted := fun draw : Seed × PublicationResult (L.Val payload) =>
    (execution draw.1).respond (application setup leaks) owner
      (bindingChoiceResponse owner event payload (execution draw.1) (some draw.2))
  obtain ⟨afterNoise, afterFactor⟩ := binding_transmission_response_factorization name guard
    focal event prior source original execution (fun pair => commitKernel residual
      (pair.1.view owner)) noise factor
  have actualFactor : decisions.map (fun draw => (successor draw,
        (runtime setup).bindingTraffic leaks focal (submitted draw))) =
      (decisions.map successor).bind fun pair =>
        (afterNoise (pair.1.view focal)).map fun extra => (pair, extra) := by
    simpa only [decisions, successor, submitted, PMF.map_bind, PMF.map_comp,
      PMF.bind_map, Function.comp_def] using afterFactor
  have support : ∀ draw ∈ decisions.support, draw.1 ∈ prior.support := by
    intro draw reached
    change draw ∈ (prior.bind fun seed =>
      (commitKernel residual ((source seed).view owner)).map fun value => (seed, value)).support
        at reached
    rw [PMF.support_bind] at reached
    obtain ⟨seed, supported, chosen⟩ := Set.mem_iUnion₂.mp reached
    rw [PMF.support_map] at chosen
    obtain ⟨value, _, same⟩ := chosen
    cases same
    exact supported
  obtain ⟨nextNoise, stopped⟩ := sourceServiceTurnPolicy_recorded_binding_factorization setup
    leaks scheduler horizon bound turns timing profile focal decisions successor
    (fun pair => pair.1.view focal) submitted event owner payload
    (by
      intro draw reached
      rw [((runtime setup).reactive_respond_application leaks (execution draw.1) owner
        (bindingChoiceResponse owner event payload (execution draw.1) (some draw.2))).1]
      exact ready draw.1 (support draw reached))
    (by
      intro draw _reached
      exact (runtime setup).eventRecorded_respond leaks (execution draw.1) owner
        (bindingChoiceResponse owner event payload (execution draw.1) (some draw.2)) event rfl)
    outputEq codeEq (nodeView_eq_bind outputEq codeEq) afterNoise actualFactor
  refine ⟨nextNoise, ?_⟩
  simpa only [decisions, successor, submitted, PMF.bind_bind, PMF.bind_map,
    PMF.map_bind, PMF.map_comp, Function.comp_def] using stopped

/-- A collection of actually initialized clear protected binding inputs has
both the complete transmitting source-pair/traffic law and its actual typed
realization. Initialization is supplied by physical control-step support;
source support, packet protection and successor agreement are then derived.

The original private source history travels with the same sampled value. This
lemma transports a supplied prior traffic channel, rather than identifying the
source marginal with a particular source assessment or proving native Bayes.
-/
theorem source_async_binding_transmission_completion
    {Seed : Type} {Γ : SourceCtx Player L} {names : Finset VarId}
    {owner : Player} {payload : L.Ty} (name : VarId) (freshName : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names))
    (profile : BehavioralProfile setup.program)
    (residual : BehavioralProfile (.commit name owner freshName guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner freshName guard next))
    (refsBefore : ContextRefsBefore refs embedding)
    (event : (graph setup).EventId) (head : embedding.event ⟨0, by simp [eventCount]⟩ = event)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (bounds : MessageBounds (graph setup))
    (focal : Player) (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution) (remaining : Seed → Nat)
    (aligned : ∀ seed ∈ prior.support,
      CompiledPolicySuffix setup.program profile (.commit name owner freshName guard next)
        residual refs (source seed).revelations (source seed).registry embedding refsBefore
          event.val)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (history : ∀ seed ∈ prior.support, decodeHistory setup.program
      ((execution seed).application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = (source seed).history)
    (trace : ∀ seed ∈ prior.support,
      ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
        scheduler).Trace (some ⟨remaining seed, some owner, execution seed⟩))
    (clear : ∀ seed ∈ prior.support, ∀ player,
      (runtime setup).persistentServiceRisk leaks bound player ((execution seed).recall player)
        ((execution seed).observe (application setup leaks) player) = false)
    (unrecorded : ∀ seed ∈ prior.support,
      (runtime setup).eventRecorded leaks ((execution seed).recall owner) event = false)
    (turn : ∀ seed ∈ prior.support,
      (execution seed).application.publicView.ownTurn? owner = some event)
    (fits : ∀ seed ∈ prior.support,
      (execution seed).application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (fuel : Nat)
    (initialized : ∀ seed ∈ prior.support,
      some ⟨remaining seed, some owner, execution seed⟩ ∈
        ((fun law => law.bind ((application setup leaks).controlStep (initialLaw setup) horizon
          scheduler (sourceServiceTurnPolicy setup leaks bound horizon
            (geometricTiming setup horizon weight positive.le below.le) profile)))^[fuel]
              (PMF.pure none)).support)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → PMF _,
      ((prior.bind fun seed => (commitKernel residual ((source seed).view owner)).bind fun value =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound horizon
            (geometricTiming setup horizon weight positive.le below.le) profile)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          ((execution seed).respond (application setup leaks) owner
            (bindingChoiceResponse owner event payload (execution seed) (some value)))).map
            fun final => ((commitSuccessor name guard (source seed) value,
              commitSuccessor name guard (original seed) value),
              (runtime setup).bindingTraffic leaks focal final)) =
        ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
          ((commitKernel residual (pair.1.view owner)).map fun value =>
            (commitSuccessor name guard pair.1 value,
              commitSuccessor name guard pair.2 value))).bind fun successor =>
                (nextNoise (successor.1.view focal)).map fun extra => (successor, extra)) ∧
      ∀ seed ∈ prior.support,
        ∀ value ∈ (commitKernel residual ((source seed).view owner)).support,
          ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler
              (sourceServiceTurnPolicy setup leaks bound horizon
                (geometricTiming setup horizon weight positive.le below.le) profile)
              (fun final => event ∈ final.application.config.cut.completed) horizon
              ((execution seed).respond (application setup leaks) owner
                (bindingChoiceResponse owner event payload (execution seed) (some value)))).support,
            ∃ message : Message Player (WitnessedPacket (graph setup)),
              message.sender = owner ∧ message.payload.call.event? (graph setup) = some event ∧
              (message.id, true) ∈ stopped.receipts ∧ event ∉ stopped.application.missedEvents ∧
              ∃ ref : EventGraph.FieldRef (graphLayout setup.program) (.binding owner payload),
                ref.field = .inr event ∧ (refs.cons (name := name) ref).Agrees
                  (commitSuccessor name guard (source seed) value).state
                  stopped.application.config.store ∧
                decodeHistory setup.program (stopped.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential)) =
                    (commitSuccessor name guard (source seed) value).history := by
  let timing := geometricTiming setup horizon weight positive.le below.le
  let players := sourceServiceTurnPolicy setup leaks bound horizon timing profile
  let site := fun seed (supported : seed ∈ prior.support) =>
    (⟨Γ, names, name, owner, payload, freshName, guard, next, residual, refs, source seed,
      embedding, refsBefore, aligned seed supported, agree seed supported,
      history seed supported, head⟩ : BindingSource setup profile event
        (execution seed).application.config)
  obtain ⟨first, supported⟩ := prior.support_nonempty
  obtain ⟨nextNoise, law⟩ := source_binding_transmission_stopped_factorization name freshName
    guard next profile residual bound timing focal event prior source original execution
    (by
      intro seed reached
      exact ((execution seed).application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ owner event (turn seed reached)).1)
    (site first supported).outputEq (site first supported).code noise factor
  refine ⟨nextNoise, law, ?_⟩
  intro seed reached value sampled stopped stoppedSupported
  have origin := (application setup leaks).roundSupported_iterate_controlStep (initialLaw setup)
    horizon scheduler players fuel _ (initialized seed reached)
  obtain ⟨entry, _, message, _, call, completion⟩ :=
    sourceServiceDecision_clear_binding_completion contract bounds profile players (execution seed)
      event (site seed reached) (trace seed reached) origin (clear seed reached)
      (unrecorded seed reached) (turn seed reached) (fits seed reached)
      weight positive below rfl value sampled
  obtain ⟨_, accepted, noMiss, _, successorAgree, successorHistory⟩ :=
    completion stopped stoppedSupported
  exact ⟨message, call.authored, call.addressed, accepted, noMiss,
    ⟨.inr event, (site seed reached).outputEq⟩, rfl, successorAgree, successorHistory⟩

end Vegas
