/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedDisclosure
import Vegas.Game.SourceServiceTimedSample
import Vegas.Game.SourceServiceTimedBindingCheckpoint
import Vegas.Game.SourceServiceBoundary
import Vegas.Game.SourceServicePrefix
import Vegas.Pending.ReactiveDecisionWindowExpiry
import GameTheoryExtensions.Math.Probability.Support

/-! # Source successors in conditional timed executions

Each branch of the actual timed response law retains its own source successor
and native traffic together. These support facts justify the joint decoder
used by the information-likelihood induction.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every conditional disclosure window completes the corresponding guarded
source branch. The equality concerns the actual final configuration, for each
supported execution, rather than just its marginal distribution. -/
theorem guardedDisclosureWindow_config
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (valid : execution.application.BindingInvariant)
    (unremembered : execution.application.remembered = fun _ => none)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (ticks : Nat)
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    (slot : Fin (roster.count owner)) (disclose : Bool)
    (effective : disclose = false ∨ ∃ value : L.Val payload,
      disclose = true ∧ disclosureResult published binding source true = .success value)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      ((runtime setup).decisionWindowPlayers leaks owner event
        (rosterOpening? setup leaks owner event (execution.observe (application setup leaks) owner))
        (execution.recall owner).length (slot, disclose)) network
      ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate ticks .tick ++ [.expire event]) execution).support) :
    final.application.config = execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding source disclose)) := by
  let app := application setup leaks
  rcases effective with rfl | ⟨value, rfl, success⟩
  · change final ∈ ((runtime setup).runInteractionPlan leaks
      ((runtime setup).decisionWindowPlayers leaks owner event none
        (execution.recall owner).length (slot, false)) network
      ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate ticks .tick ++ [.expire event]) execution).support at reached
    let after := execution.application.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))
    have baseHandled := (runtime setup).handle_withhold_unremembered_eq execution.application
      (owner, execution.network.nextSerial owner) event owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq node ready timely rfl (by rw [unremembered])
    have accepted : app.handle execution.application
        ((runtime setup).decisionEnvelope leaks owner event none false execution) = some after := by
      rw [reactiveApplication_handle_of_current_token (runtime setup) leaks _ _ rfl]
      exact baseHandled
    have settled : ¬after.config.cut.Ready event := by
      intro active
      exact active.1 (by simp [after, State.complete, EventOrder.Cut.complete])
    obtain ⟨completed, _⟩ := (runtime setup).decisionWindow_expiry leaks owner event none
      execution serials packets (fun _ _ impossible => by cases impossible) roster (slot, false)
      (by intro impossible; cases impossible) after accepted settled ticks network final
      (by simpa only [List.append_assoc] using reached)
    rw [completed]
    simp only [after, State.complete, disclosureResult_false]
  · obtain ⟨candidate, associated, owned, fixed, opening⟩ := guarded_rosterOpening_success
      setup leaks published binding source refs execution agree valid event outputEq codeEq node
      value success
    rw [opening] at reached
    have resolved := compiled_disclosure_result published binding source refs
      execution.application.config.store agree true
    rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
    have stored := EventGraph.EventCode.binding_success_of_resolve_success (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true execution.application.config.store value resolved
    let after := execution.application.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) (.success value))
    have accepted : app.handle execution.application
        ((runtime setup).decisionEnvelope leaks owner event (some (candidate, ⟨payload, value⟩))
          true execution) = some after := by
      exact (reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
        ((runtime setup).windowEnvelope_tokenValid leaks owner event candidate _ execution
          ready)).trans
        (handle_opening_eq (runtime setup) execution.application _ event candidate owner payload
          (refs.get binding) _ outputEq codeEq node ready timely rfl owned associated value fixed
          stored (.success value) resolved)
    have settled : ¬after.config.cut.Ready event := by
      intro active
      exact active.1 (by simp [after, State.complete, EventOrder.Cut.complete])
    obtain ⟨completed, _⟩ := (runtime setup).decisionWindow_expiry leaks owner event
      (some (candidate, ⟨payload, value⟩)) execution serials packets
      (by intro selected raw same; cases Option.some.inj same; exact owned) roster (slot, true)
      (by intro _ selected raw same; cases Option.some.inj same; exact fixed)
      after accepted settled ticks network final
      (by simpa only [List.append_assoc] using reached)
    rw [completed]
    simp only [after, State.complete, success]

/-- The native decoder's typed source checkpoint is the same successor that
indexes the conditional traffic branch. -/
theorem SourceCheckpoint.guardedDisclosureWindow
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (valid : execution.application.BindingInvariant)
    (unremembered : execution.application.remembered = fun _ => none)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (ticks : Nat)
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    (slot : Fin (roster.count owner)) (disclose : Bool)
    (effective : disclose = false ∨ ∃ value : L.Val payload,
      disclose = true ∧ disclosureResult published binding source true = .success value)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose))
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      ((runtime setup).decisionWindowPlayers leaks owner event
        (rosterOpening? setup leaks owner event (execution.observe (application setup leaks) owner))
        (execution.recall owner).length (slot, disclose)) network
      ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate ticks .tick ++ [.expire event]) execution).support) :
    SourceCheckpoint setup (revealSuccessor published binding source disclose)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1)
      final.application.config := by
  rw [guardedDisclosureWindow_config setup leaks published binding source refs execution
    checkpoint.agrees valid unremembered event outputEq codeEq node ready timely ticks
    packets serials network roster slot disclose effective final reached]
  exact checkpoint.reveal published binding event eventRank ready outputEq before disclose decoded

/-- The timed compiler's actual decoder and auxiliary traffic have the joint
source-successor law. This is stronger than separate source-state and traffic
marginals and supplies the disclosure constructor of prefix factorization. -/
theorem sourceServiceTimedPolicy_reveal_joint_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations source.registry embedding refsBefore rank)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config)
    (valid : execution.application.BindingInvariant)
    (unremembered : execution.application.remembered = fun _ => none)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations)
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) (focal : Player) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (owned : (graph setup).actor? event = some owner)
      (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final =>
        (decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
          refs source.registry source.revelations embedding.ref 1 final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential))),
          (runtime setup).bindingTraffic leaks focal final)) =
      (revealKernel profile (source.view owner)).bind fun disclose =>
        (guardedDisclosureTranscript setup leaks network (rosters event) owner focal event ticks
          (timing event owner owned) execution disclose).map fun traffic =>
            (some (Sum.inr (ProtocolState.entry next
              (revealSuccessor published binding source disclose))), traffic) := by
  intro index event owned ready timely unsent counted
  let app := application setup leaks
  let phase := (rosters event).map ServiceInstruction.player ++
    (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
  let read (final : app.Execution) :=
    decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
      refs source.registry source.revelations embedding.ref 1 final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry
          source.revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have decoded (disclose : Bool) : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose) := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    simpa [event, index, outputEq, decodeEventAction] using action
  rw [sourceServiceTimedPolicy_reveal_phase_law setup leaks rosters timing fresh binding
    unresolved next wholeProfile profile refs source embedding refsBefore rank aligned execution
    checkpoint.agrees checkpoint.history valid recalled origins effective network ticks owned
    ready unsent counted, PMF.map_bind]
  apply bind_congr_on_support _
  intro disclose supported
  let target : Option
      (ProtocolState (.reveal published owner name fresh binding unresolved next)) :=
    some (Sum.inr (ProtocolState.entry next (revealSuccessor published binding source disclose)))
  let players := fun slot : Fin ((rosters event).count owner) =>
    (runtime setup).decisionWindowPlayers leaks owner event
      (rosterOpening? setup leaks owner event (execution.observe app owner))
      (execution.recall owner).length (slot, disclose)
  trans ((timing event owner owned).bind fun slot =>
    ((runtime setup).runInteractionPlan leaks (players slot) network phase execution).map
      ((runtime setup).bindingTraffic leaks focal)).map (fun traffic => (target, traffic))
  · rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro slot _
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    have completed := checkpoint.guardedDisclosureWindow published binding event eventRank
      outputEq codeEq node (fun ref => refsBefore ref index) valid unremembered ready timely ticks
      packets serials network (rosters event) slot disclose
      (effective_reveal_supported fresh binding unresolved next profile source effective
        disclose supported) (decoded disclose) final
      (by
        convert reached using 1
        simp only [event, index, List.append_assoc, List.singleton_append])
    have recovered := completed.decode next (fun tail => embedding.ref tail.succ)
    apply Prod.ext
    · change read final = target
      dsimp only [read]
      rw [decodeSourcePrefix?_reveal]
      exact congrArg (Option.map Sum.inr) recovered
    · rfl
  · apply congrArg (PMF.map (fun traffic => (target, traffic)))
    simp only [guardedDisclosureTranscript, players, phase, List.append_assoc,
      List.cons_append, List.nil_append]
    rfl

/-- The actual timed chance phase retains its source draw jointly with all
native traffic. The public draw is followed by the existing settlement
interpreter; its source checkpoint is reconstructed from the real endpoint. -/
theorem sourceServiceTimedPolicy_sample_joint_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) openNames)
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.sample name fresh distribution next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh distribution next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.sample name fresh distribution next) profile refs source.revelations source.registry
        embedding refsBefore rank)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) (focal : Player) :
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publicData payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (ready : execution.application.config.cut.Ready event),
    let app := application setup leaks
    let silentPlayers := fun _ => app.silentPolicy
    let completed := fun (current : app.Execution) value =>
      { current with
        application := execution.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)
        environmentRecall := current.environmentRecall ++
          [⟨current.observeEnvironment app, .application (.executeSample event)⟩] }
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++
        (.sample event :: List.replicate ticks .tick ++ [.expire event])) execution).map
          (fun final =>
            (decodeSourcePrefix? (.sample name fresh distribution next) refs source.registry
              source.revelations embedding.ref 1 final.application.config.store
                (decodeHistory setup.program (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))),
              (runtime setup).bindingTraffic leaks focal final)) =
      ((runtime setup).runInteractionPlan leaks silentPlayers network
        ((rosters event).map ServiceInstruction.player) execution).bind fun current =>
          (L.evalDist distribution (sourcePublicEnv source.state)).bind fun value =>
            ((runtime setup).runInteractionPlan leaks silentPlayers network
              (List.replicate ticks .tick ++ [.expire event]) (completed current value)).map
                fun final =>
                  (some (Sum.inr (ProtocolState.entry next (sampleSuccessor name source value))),
                    (runtime setup).bindingTraffic leaks focal final) := by
  intro index event outputEq ready app silentPlayers completed
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs distribution) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs distribution) outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_sample _ _
  have chance : (graph setup).actor? event = none := by
    change (toEventGraph setup.program).actor? event = none
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
    simpa [event, index, outputEq, decodeEventAction] using action
  rw [sourceServiceTimedPolicy_sample_phase_law setup leaks rosters timing wholeProfile
    source refs execution checkpoint.agrees event ready outputEq distribution codeEq node
    chance network ticks, PMF.map_bind]
  apply bind_congr_on_support _
  intro current _
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro value _
  apply map_congr_on_support _
  intro final reached
  have settled : ¬(completed current value).application.config.cut.Ready event := by
    intro active
    exact active.1 (by simp [completed, EventGraphRuntime.State.complete, EventOrder.Cut.complete])
  obtain ⟨after, exactLaw, afterState, _⟩ := (runtime setup).settled_reveal_expiry leaks
    silentPlayers network (completed current value) event settled ticks
  rw [exactLaw] at reached
  have finalEq := (PMF.mem_support_pure_iff _ _).mp reached
  subst final
  have result := checkpoint.sample name event eventRank ready outputEq
    (fun ref => refsBefore ref index) decoded value
  have recovered := result.decode next (fun tail => embedding.ref tail.succ)
  apply Prod.ext
  · rw [afterState]
    change (decodeSourcePrefix? (.sample name fresh distribution next) refs source.registry
      source.revelations embedding.ref 1
        (execution.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)).config.store
        (decodeHistory setup.program
          ((execution.application.complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)).config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)))) = _
    rw [decodeSourcePrefix?_sample]
    exact congrArg (Option.map Sum.inr) recovered
  · rfl

/-- Binding at any selected visit has the actual source successor jointly
with its full settlement traffic. Dynamic fresh-slot resources follow from
the operational boundary; no fixed initial-catalogue hypothesis is used. -/
theorem sourceServiceTimedPolicy_binding_joint_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile (.commit name owner fresh guard next)
      profile refs source.revelations source.registry embedding refsBefore rank)
    (initial : State L setup.context) (execution : (application setup leaks).Execution)
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) (focal : Player) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (owned : (graph setup).actor? event = some owner),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final =>
        (decodeSourcePrefix? (.commit name owner fresh guard next) refs source.registry
          source.revelations embedding.ref 1 final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential))),
          (runtime setup).bindingTraffic leaks focal final)) =
      (commitKernel profile (source.view owner)).bind fun choice =>
        (bindingPhaseTranscript setup leaks network (rosters event) owner focal event payload
          (rosterOffset setup rosters owner event) ticks ((timing event owner owned).map some)
          execution choice).map fun traffic =>
            (some (Sum.inr (ProtocolState.entry next
              (commitSuccessor name guard source choice))), traffic) := by
  intro index event owned
  let app := application setup leaks
  let phase := (rosters event).map ServiceInstruction.player ++
    (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
  let serial := execution.application.publicView.bindingCount owner
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_bind _ _
  obtain ⟨freshSlot, candidate, unused, vacant⟩ := boundary.binding_resources event eventRank owner
  have ready := boundary.ready event eventRank
  have timely := boundary.timely event eventRank (by simp only [owned, Option.isSome_some])
  have counted := boundary.response_offset event eventRank owner
  have decoded (choice : PublicationResult (L.Val payload)) :
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
          some (.commit owner name payload choice) := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
    simpa [event, index, outputEq, decodeEventAction] using action
  rw [sourceServiceTimedPolicy_binding_phase_law setup leaks rosters timing fresh guard next
    wholeProfile profile refs source embedding refsBefore rank aligned execution boundary.agrees
    boundary.history serial freshSlot candidate network ticks owned ready
    (boundary.unsent owner event eventRank.ge) counted, PMF.map_bind]
  apply bind_congr_on_support _
  intro choice _
  let family := fun selected : Option (Fin ((rosters event).count owner)) =>
    app.scheduledPolicy (rosterOffset setup rosters owner event) selected
      (fun _ _ => PMF.pure ((runtime setup).reactiveBinding leaks owner event payload
        choice serial)) app.silentPolicy
  let target : Option (ProtocolState (.commit name owner fresh guard next)) :=
    some (Sum.inr (ProtocolState.entry next (commitSuccessor name guard source choice)))
  have dormant := app.policyMixture_posterior_dormant ((timing event owner owned).map some)
    family app.silentPolicy (rosterOffset setup rosters owner event)
    (fun selected past view earlier => app.scheduledPolicy_before _ _ _ _ past view earlier)
    (execution.recall owner) counted.le
  have mixture := (runtime setup).runInteractionPlan_policyMixture leaks
    ((timing event owner owned).map some) family owner (fun _ => app.silentPolicy)
    network phase execution
  dsimp only at mixture
  rw [dormant, PMF.bind_map] at mixture
  simp only [Function.comp_def] at mixture
  have transcript : bindingPhaseTranscript setup leaks network (rosters event) owner focal event
      payload (rosterOffset setup rosters owner event) ticks ((timing event owner owned).map some)
      execution choice =
      ((timing event owner owned).bind fun slot =>
        (runtime setup).runInteractionPlan leaks
          (Function.update (fun _ => app.silentPolicy) owner (family (some slot))) network
          phase execution).map ((runtime setup).bindingTraffic leaks focal) := by
    rw [mixture]
    simp only [bindingPhaseTranscript, phase, List.append_assoc, List.singleton_append]
    rfl
  rw [transcript, PMF.map_comp, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro slot _
  apply map_congr_on_support _
  intro final reached
  have config := scheduledBindingPhase_config setup leaks bounds network owner event payload
    outputEq codeEq node owned execution ready timely serial candidate vacant unused
    boundary.serials boundary.published (rosters event) slot
    (rosterOffset setup rosters owner event) (by rw [counted]; omega)
    (by rw [counted]; exact Nat.add_lt_add_left slot.isLt _) choice ticks final (by
      convert reached using 1
      simp only [List.append_assoc, List.singleton_append]
      rfl)
  have result := boundary.toSourceCheckpoint.commit name guard event eventRank ready outputEq
    (fun ref => refsBefore ref index) choice (decoded choice)
  have recovered := result.decode next (fun tail => embedding.ref tail.succ)
  apply Prod.ext
  · rw [config, decodeSourcePrefix?_commit]
    exact congrArg (Option.map Sum.inr) recovered
  · rfl

end Vegas
