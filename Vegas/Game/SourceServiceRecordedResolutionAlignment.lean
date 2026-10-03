/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRecordedSourceChoice
import Vegas.Game.SourceServiceResolutionInclusionFactorization
import Vegas.Game.SourceServiceRecordedResolutionTraffic
import Vegas.Game.SourceServiceRecordedDecisionRealization

/-! # The source meaning of an actually recorded resolution

The actual recalled transmission identifies a supported effective source
disclosure. Its packet realizes that choice in the aligned typed configuration.
The original authenticated entry and packet are retained through completion;
source support is derived from the prescribed owner's actual recall.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Compiler alignment identifies the actual resolution code and its binding
reference at this source disclosure. -/
theorem RevealSource.code
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    {config : (graph setup).Config} (site : RevealSource setup profile event config) :
    cast (congrArg (EventGraph.EventCode (graph setup).layout) site.outputEq)
        ((graph setup).nodes event) =
      .resolve site.owner site.payload (site.refs.get site.binding)
        (compileChecks (published := site.published) site.refs site.source.registry
          site.source.revelations site.binding) := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _, _⟩ := site
  dsimp only at *
  subst head
  change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
    ((toEventGraph setup.program).nodes _) = _
  simpa [eventCount, compileRankedNodes] using
    aligned.graphSuffix.nodeEq ⟨0, by simp [eventCount]⟩

private theorem canonical_resolution_call
    (owner : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    {actor : Player} (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding actor payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve actor payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve actor payload binding checks outputEq codeEq)
    (disclose : Bool) (material : (application setup leaks).Submission)
    (transmission : ((runtime setup).canonicalServiceDecision leaks owner past view event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)).transmission =
        some material) :
    material.call.packet = reactiveResolutionPacket owner event payload binding checks outputEq
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) view.application := by
  simp only [canonicalServiceDecision, canonicalReactiveDecision, node,
    reactiveNormalization, ReactiveApplication.SubmissionNormalization.action] at transmission
  cases Option.some.inj transmission
  rfl

private theorem revealSource_action
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    {config : (graph setup).Config} (site : RevealSource setup profile event config)
    (disclose : Bool) :
    decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) =
      some (.reveal site.owner site.name disclose) := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _, _⟩ := site
  dsimp only at *
  subst head
  let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  have inverse : (cast (congrArg EventGraph.EventField.Action (embedding.layout_eq index))
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) : Bool) =
        disclose := by
    change cast (congrArg EventGraph.EventField.Action outputEq)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) = disclose
    simp only [cast_cast, cast_eq]
  have lookup := aligned.actionEq index
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
  change decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
    some (.reveal owner name (cast (congrArg EventGraph.EventField.Action
      (embedding.layout_eq index))
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose))) at lookup
  rw [inverse] at lookup
  exact lookup

omit [DecidableEq Player] in
private theorem transported_store {who other : Player} {graph : Vegas.EventGraph Player L}
    (identity : who = other) (observation : graph.PlayerObservation who) :
    (identity ▸ observation).store = observation.store := by
  subst identity
  rfl

/-- The exact original packet of a recorded resolution realizes a supported
effective source disclosure in the current aligned configuration. Only its
owner follows the source policy; all foreign policies remain arbitrary. -/
theorem sourceServiceTurnPolicy_recorded_resolution_realizes {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (count : Nat) (within : count ≤ horizon) (start : (application setup leaks).Execution)
    (reached : start ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId)
    (site : RevealSource setup profile event start.application.config)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (ready : start.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (start.recall site.owner) event = true) :
    ∃ disclose ∈ (revealKernel site.residual (site.source.view site.owner)).support,
      ∃ entry ∈ start.recall site.owner, ∃ message,
        (runtime setup).submittedEvent? leaks entry.action = some event ∧
        FreshCall setup leaks site.owner event bound entry message ∧
        RealizesAt leaks start.application.config start.application event
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) entry message ∧
        ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon start).support,
          entry ∈ stopped.recall site.owner ∧
          event ∈ stopped.application.config.cut.completed ∧
          (message.id, true) ∈ stopped.receipts ∧ event ∉ stopped.application.missedEvents := by
  let app := application setup leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    count within start reached
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨entry, member, message, named, call, completion⟩ :=
    sourceServiceTurnPolicy_recorded_decision_completion contract players site.owner timing
      profile follows count within start reached event site.owned recorded
  have input : message ∈ start.network.inputs := by
    have output : message ∈ app.outputs (start.recall site.owner) :=
      List.mem_filterMap.mpr ⟨entry, member, call.emitted⟩
    rw [← facts.inputs site.owner] at output
    exact (List.mem_filter.mp output).1
  obtain ⟨issuer, issuerMember, material, transmission, emitted, state, known, issued⟩ :=
    facts.provenance.inputs message input
  rw [call.authored] at issuerMember
  have issuerNamed : (runtime setup).submittedEvent? leaks issuer.action = some event := by
    unfold EventGraphRuntime.submittedEvent?
    rw [transmission]
    change (app.packet state message.sender known material).call.event? (graph setup) = some event
    rw [issued]
    exact call.addressed
  obtain ⟨disclose, supported, before, after, split, response⟩ :=
    sourceServiceTurnPolicy_recalled_resolution_choice timing profile players count within start
      reached event site follows ready issuer issuerMember issuerNamed material transmission
  refine ⟨disclose, supported, entry, member, message, named, call, ?_, completion⟩
  have codeEq := RevealSource.code site
  have node := nodeView_eq_resolve site.outputEq codeEq
  have packet : material.call.packet = reactiveResolutionPacket site.owner event site.payload
      (site.refs.get site.binding)
      (compileChecks (published := site.published) site.refs site.source.registry
        site.source.revelations site.binding) site.outputEq
      (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
      issuer.beforeView.application := by
    rw [response] at transmission
    exact canonical_resolution_call site.owner before issuer.beforeView event site.payload
      (site.refs.get site.binding) _ site.outputEq codeEq node disclose material transmission
  have messageCall : message.payload.call = material.call.packet := by
    rw [← issued]
    rfl
  have atTurn := (canonicalSlots_roundsFrom scheduler players site.owner timing profile follows
    count start reached).1
  have issuerTurn := atTurn issuer issuerMember event issuerNamed
  have current := ownTurn?_of_ready setup start.application ready site.owned
  have identity := (recalled_ownTurn_observation setup leaks trace site.owner issuer issuerMember
    event issuerTurn current).1
  have observed := recalled_ownTurn_observation_cast setup leaks trace site.owner issuer
    issuerMember event issuerTurn current identity
  have storeEq : issuer.beforeView.application.observation.store =
      (graph setup).playerStore site.owner start.application.config.store := by
    have stores := congrArg (fun view => view.store) observed
    rw [transported_store identity issuer.beforeView.application.observation] at stores
    exact stores
  have associatedEq := (entry_view_current setup leaks start facts.stable site.owner issuer
    issuerMember event (PublicView.ownTurn?_spec _ _ _ issuerTurn).1 ready.1).2.1
  unfold RealizesAt
  rw [node]
  rcases effective_reveal_supported site.fresh site.binding site.unresolved site.next
      site.residual site.source (site.inherits effective site.owner) disclose supported with
    rfl | ⟨value, rfl, success⟩
  · refine Or.inl ⟨by simp, ?_⟩
    rw [messageCall, packet]
    simp only [reactiveResolutionPacket, cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨handle, associated, handleOwner, fixed, _⟩ := guarded_rosterOpening_success setup
      leaks site.published site.binding site.source site.refs start site.agree facts.binding
      event site.outputEq codeEq node value success
    have resolved := compiled_disclosure_result (graph := graph setup) site.published site.binding
      site.source site.refs start.application.config.store site.agree true
    rw [success] at resolved
    have visibleResolved := resolved
    rw [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
    have stored := facts.binding.opening_stored _ _ _ associated fixed
    refine Or.inr ⟨by simp, handle, value, ?_, handleOwner, ?_, fixed, stored, ⟨_, resolved⟩⟩
    · rw [messageCall, packet]
      simp only [reactiveResolutionPacket, cast_cast, cast_eq, ↓reduceIte,
        storeEq, associatedEq, associated, visibleResolved, handleOwner]
    · have entryEq := (entry_view_current setup leaks start facts.stable site.owner entry member
        event call.ready ready.1).2.1
      rw [entryEq]
      exact associated

/-- Every supported stopped endpoint is the exact aligned source successor of
the original recalled disclosure, with its accepting receipt and full typed
store agreement. No source choice or endpoint alignment is assumed. -/
theorem sourceServiceTurnPolicy_recorded_resolution_completion {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (count : Nat) (within : count ≤ horizon) (start : (application setup leaks).Execution)
    (reached : start ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId)
    (site : RevealSource setup profile event start.application.config)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (ready : start.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (start.recall site.owner) event = true) :
    ∃ disclose ∈ (revealKernel site.residual (site.source.view site.owner)).support,
      ∃ entry ∈ start.recall site.owner, ∃ message,
        (runtime setup).submittedEvent? leaks entry.action = some event ∧
        FreshCall setup leaks site.owner event bound entry message ∧
        (∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon start).support,
          entry ∈ stopped.recall site.owner ∧ (message.id, true) ∈ stopped.receipts ∧
          event ∉ stopped.application.missedEvents ∧
          stopped.application.config = start.application.config.complete event ready
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
            (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
              (disclosureResult site.published site.binding site.source disclose)) ∧
          (site.refs.cons (name := site.published) ⟨.inr event, site.outputEq⟩).Agrees
            (revealSuccessor site.published site.binding site.source disclose).state
            stopped.application.config.store ∧
          decodeHistory setup.program (stopped.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential)) =
              (revealSuccessor site.published site.binding site.source disclose).history) ∧
        ∀ focal,
          (((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon start).map
              (fun final => (final.application.config,
                (runtime setup).bindingTraffic leaks focal final))) =
          ((((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon start).map
              ((runtime setup).bindingTraffic leaks focal)).map fun extra =>
                (start.application.config.complete event ready
                  (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
                  (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
                    (disclosureResult site.published site.binding site.source disclose)),
                  extra)) := by
  obtain ⟨disclose, supported, entry, member, message, named, call, realized, completion⟩ :=
    sourceServiceTurnPolicy_recorded_resolution_realizes contract players timing profile effective
      count within start reached event site follows ready recorded
  have native (stopped : (application setup leaks).Execution)
      (stoppedSupported : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
      stopped.application.config = start.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
          (disclosureResult site.published site.binding site.source disclose)) := by
    have actual := sourceServiceTurnPolicy_recorded_realization_completion contract players
      site.owner timing profile follows count within start reached event site.owned ready
      (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) entry member
      message named call realized stopped stoppedSupported
    have codeEq := RevealSource.code site
    rw [start.application.config.step_eq_map_of_code event ready site.outputEq _ codeEq disclose
      (PMF.pure (disclosureResult site.published site.binding site.source disclose))
      (compileResolve_eval? site.refs site.source.registry site.source.revelations site.source.state
        start.application.config.store site.agree site.binding disclose),
      PMF.pure_map, PMF.mem_support_pure_iff] at actual
    exact actual
  refine ⟨disclose, supported, entry, member, message, named, call, ?_, ?_⟩
  · intro stopped stoppedSupported
    obtain ⟨retained, _, accepted, clear⟩ := completion stopped stoppedSupported
    have same := native stopped stoppedSupported
    refine ⟨retained, accepted, clear, same, ?_, ?_⟩
    · have before : ∀ {name cell} (ref : HasVar site.Γ name cell),
        FieldBefore event (site.refs.get ref).field := by
        intro name cell ref
        have ordered := site.refsBefore ref ⟨0, by simp [eventCount]⟩
        rw [site.head] at ordered
        exact ordered
      rw [same]
      intro name cell ref
      exact complete_guarded_reveal_agrees (graph := graph setup) site.published site.binding
        site.source site.refs start.application site.agree event ready site.outputEq before
        disclose ref
    · rw [same]
      change decodeHistory setup.program ((start.application.config.history ++
        [(⟨event, cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose⟩ :
          (graph setup).Completion)]).map
          (setup.eventGraph.fromModeCompletion .sequential)) = _
      rw [List.map_append, List.map_singleton]
      have decoded := decodeHistory_append_completion setup.program
        (start.application.config.history.map (setup.eventGraph.fromModeCompletion .sequential))
        event (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
      rw [revealSource_action site disclose, site.history] at decoded
      exact decoded
  · intro focal
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final supported
    exact Prod.ext (native final supported) rfl

end Vegas
