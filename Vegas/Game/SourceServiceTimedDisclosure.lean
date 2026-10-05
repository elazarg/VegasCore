/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedBinding
import Vegas.Game.SourceServiceEvidence
import Vegas.Game.SourceServiceDisclosureFactorization

/-! # Guarded source disclosures at arbitrary scheduled visits

The compiler's normalized response has the exact owned-evidence form at
every fresh retained source resolution. Certificate origins are preserved
through the actual preceding silent and observation window.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem origins_sampled
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution)
    (origin : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (who : Player) (sample : Finset (MessageId Player)) :
    (runtime setup).ResolutionEvidenceOrigins leaks
      (execution.sampledActivation (application setup leaks) who sample) :=
  origin.learn who sample

theorem origins_silent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution)
    (origin : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (who : Player) (response : (application setup leaks).Action)
    (transport : response = ⟨none⟩) :
    (runtime setup).ResolutionEvidenceOrigins leaks
      (execution.respond (application setup leaks) who response) := by
  have prior := origin.mono fun _ carried fact issued =>
    (carried fact issued).respond (runtime setup) leaks who response
  rcases transport with rfl
  exact prior

/-- The real silent window cannot create a certificate for an unresolved
source binding. This preserves the provenance fact without a new trace or
an assumed source observation correspondence at each visit. -/
theorem resolutionOrigins_silent_window
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (origin : (runtime setup).ResolutionEvidenceOrigins leaks initial)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).silentPolicy) network
      (visits.map ServiceInstruction.player) initial).support) :
    (runtime setup).ResolutionEvidenceOrigins leaks final := by
  let app := application setup leaks
  induction visits generalizing initial with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; exact origin
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      apply ih _ ?_ reached
      exact origins_silent setup leaks _ (origins_sampled setup leaks initial origin actor sample)
        actor response (app.silentPolicy_cases _ _ response supported)

private theorem successful_opening_of_origins
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (who : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (candidate : Handle (graph setup)) (value : L.Val payload)
    (associated : execution.application.accepted binding.field = some candidate)
    (resolved : EventCode.resolveOutput? binding checks true
      execution.application.config.store = some (.success value))
    (unsent : (runtime setup).eventRecorded leaks (execution.recall who) event = false) :
    (runtime setup).serviceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event
        (cast (congrArg EventField.Action outputEq.symm) true) =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩ := by
  let app := application setup leaks
  have stored := EventCode.binding_success_of_resolve_success binding checks true
    execution.application.config.store value resolved
  obtain ⟨actual, accepted, owned, fixed⟩ := valid.success_provenance binding value stored
  cases Option.some.inj (accepted.symm.trans associated)
  have resolves : ((graph setup).nodes event).resolutionField? = some binding.field := by
    have field := congrArg EventCode.resolutionField? codeEq
    rw [EventCode.resolutionField?_cast outputEq] at field
    exact field
  have normal := origins.opening_normal (runtime setup) leaks
    (resolution_field_injective setup.program) execution valid recalled who event binding.field
      resolves candidate ⟨payload, value⟩ associated owned fixed unsent
  have canonical := (runtime setup).serviceDecision_successful_opening leaks execution
    recalled who event payload binding checks outputEq codeEq node candidate value associated
      owned fixed resolved
  have known : ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
      (execution.observe app who) = execution.network.known who :=
    (app.known_from_recall execution who recalled).symm
  calc
    _ = ((runtime setup).reactiveNormalization leaks).action who
        (execution.recall who) (execution.observe app who)
          ((runtime setup).windowOpening leaks event candidate ⟨payload, value⟩) := by
      rw [canonical]
      change (⟨some ((disclosureSubmission (.opening event candidate
          ⟨payload, value⟩)).normalizeReactive
          who _ (execution.network.known who))⟩ : app.Action) = _
      rw [← known]
      rfl
    _ = _ := normal

/-- The scheduled opportunity draws the effective source Boolean and uses
the exact authentic opening or the actual silent lottery. Dynamic candidate
tables and failed deferred guards are covered by the source checkpoint and
the derived certificate-origin invariant. -/
theorem sourceServiceOpportunity_reveal
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
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
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false),
    sourceServiceOpportunity setup leaks wholeProfile owner event
      (execution.recall owner) (execution.observe (application setup leaks) owner) =
      (revealKernel profile (source.view owner)).bind fun disclose =>
        match (if disclose then rosterOpening? setup leaks owner event
          (execution.observe (application setup leaks) owner) else none) with
        | none => (application setup leaks).silentPolicy (execution.recall owner)
            (execution.observe (application setup leaks) owner)
        | some (candidate, raw) =>
            PMF.pure ((runtime setup).windowOpening leaks event candidate raw) := by
  intro index event ready unsent
  let app := application setup leaks
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change Vegas.outputLayout setup.program (embedding.event index) = _
    simpa [index, Vegas.outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry
          source.revelations binding) := by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  simp only [sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte]
  rw [sourceServicePolicy_reveal setup leaks fresh binding unresolved next wholeProfile profile
    refs source embedding refsBefore rank aligned execution agree history ready, PMF.bind_map]
  apply bind_congr_on_support _
  intro disclose supported
  rcases effective_reveal_supported fresh binding unresolved next profile source effective
    disclose supported with rfl | ⟨value, rfl, success⟩
  · have silent : (runtime setup).serviceDecision leaks owner (execution.recall owner)
        (execution.observe app owner) event
          (cast (congrArg EventField.Action outputEq.symm) false) =
          ⟨none⟩ := by
      simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
        cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
        disclosureSubmission_normalize_withhold]
      rfl
    rw [Function.comp_apply, silent]
    rfl
  · obtain ⟨candidate, associated, _, _, opening⟩ := guarded_rosterOpening_success setup leaks
      published binding source refs execution agree valid event outputEq codeEq node value success
    have resolved := compiled_disclosure_result (graph := graph setup) published binding source refs
      execution.application.config.store agree true
    rw [success, EventCode.resolveOutput?_playerStore] at resolved
    rw [Function.comp_apply, successful_opening_of_origins setup leaks execution valid recalled
      origins owner event payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq node candidate value associated resolved unsent]
    simp only [↓reduceIte, opening, windowOpening, reduceCtorEq]

/-- At a chosen visit the source lottery can be drawn before the real silent
window. The equality keeps the complete execution, including all observations,
response recall, and envelope copies. -/
theorem sourceServiceTimedFamily_reveal_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
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
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations)
    (network : (runtime setup).NetworkPolicy leaks) (visits visited remaining : List Player) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (slot : Fin ((rosters event).count owner))
      (_position : visits = visited ++ owner :: remaining)
      (_selected : rosterOffset setup rosters owner event + slot.val =
        (execution.recall owner).length + visited.count owner)
      (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false),
    (runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).silentPolicy) owner
        (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event slot)) network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution =
      (revealKernel profile (source.view owner)).bind fun disclose =>
        (runtime setup).runInteractionPlan leaks
          (Function.update (fun _ => (application setup leaks).silentPolicy) owner
            ((application setup leaks).scheduledPolicy
              (rosterOffset setup rosters owner event) (some slot)
              (fun past view => match (if disclose then rosterOpening? setup leaks owner event
                (execution.observe (application setup leaks) owner) else none) with
                | none => (application setup leaks).silentPolicy past view
                | some (candidate, raw) =>
                    PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
              (application setup leaks).silentPolicy)) network
          (visits.map ServiceInstruction.player ++ [.includeLatest event owner])
          execution := by
  intro index event slot position selected ready unsent
  let app := application setup leaks
  let offset := rosterOffset setup rosters owner event
  let opening := sourceServiceOpportunity setup leaks wholeProfile owner event
  let sourcePlayers := Function.update (fun _ => app.silentPolicy) owner
    (app.scheduledPolicy offset (some slot) opening app.silentPolicy)
  let branch : Bool → app.Policy := fun disclose past view =>
    match (if disclose then rosterOpening? setup leaks owner event
      (execution.observe app owner) else none) with
    | none => app.silentPolicy past view
    | some (candidate, raw) =>
        PMF.pure ((runtime setup).windowOpening leaks event candidate raw)
  let branchPlayers := fun disclose => Function.update (fun _ => app.silentPolicy) owner
    (app.scheduledPolicy offset (some slot) (branch disclose) app.silentPolicy)
  let transport : Player → app.Policy := fun _ => app.silentPolicy
  have before : (execution.recall owner).length + visited.count owner ≤ offset + slot.val := by
    exact selected.ge
  have sourcePrefix := scheduled_window_waiting setup leaks network owner offset slot opening
    visited execution (Or.inl before)
  have branchPrefix := fun disclose => scheduled_window_waiting setup leaks network owner offset
    slot (branch disclose) visited execution (Or.inl before)
  change (runtime setup).runInteractionPlan leaks sourcePlayers network
    (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution =
    (revealKernel profile (source.view owner)).bind fun disclose =>
      (runtime setup).runInteractionPlan leaks (branchPlayers disclose) network
        (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution
  simp only [position, List.map_append, List.map_cons, List.append_assoc,
    (runtime setup).runInteractionPlan_append]
  rw [sourcePrefix]
  dsimp only [branchPlayers, app]
  conv_rhs =>
    arg 2
    ext disclose
    rw [branchPrefix disclose]
  conv_rhs => rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro current reached
  have preserved := (runtime setup).silent_window_preserves leaks transport network owner execution
    (fun current who response _ _ member => app.silentPolicy_cases _ _ response member)
    (fun _ => True) ⟨by simp, by simp, by simp, by simp⟩ visited current reached
  have same := preserved.1
  have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
  have currentAgree : refs.Agrees source.state current.application.config.store := by
    rw [same]; exact agree
  have currentHistory : decodeHistory setup.program (current.application.config.history.map
      (setup.eventGraph.fromModeCompletion .sequential)) = source.history := by
    rw [same]; exact history
  have currentValid : current.application.BindingInvariant := by rw [same]; exact valid
  have currentRecall := (runtime setup).runInteractionPlan_inputRecall leaks transport network
    (visited.map ServiceInstruction.player) execution current recalled reached
  have currentOrigins := resolutionOrigins_silent_window setup leaks network visited execution
    current origins reached
  have currentUnsent := (silent_window_eventRecorded setup leaks network visited execution current
    reached owner event).trans unsent
  have currentCount := fixed_plan_response_counts setup leaks network transport
    (visited.map ServiceInstruction.player) (by simp) execution current reached owner
  simp only [List.filterMap_map, Function.comp_def, instructionActor,
    List.filterMap_some] at currentCount
  have atSlot : (current.recall owner).length = offset + slot.val := by
    rw [currentCount]
    exact selected.symm
  simp only [List.cons_append, runInteractionPlan, interactionStep, interactionInstruction,
    PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.invoke,
    ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
    Function.comp_def]
  conv_rhs => rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro sample _
  let activated := current.sampledActivation app owner sample
  have activatedUnsent : (runtime setup).eventRecorded leaks (activated.recall owner) event =
      false := currentUnsent
  have sourceLaw := sourceServiceOpportunity_reveal setup leaks fresh binding unresolved next
    wholeProfile profile refs source embedding refsBefore rank aligned activated currentAgree
    currentHistory currentValid currentRecall
    (origins_sampled setup leaks current currentOrigins owner sample) effective currentReady
    activatedUnsent
  have openingEq := rosterOpening?_application_eq setup leaks owner event activated execution same
  have actionLaw : opening (activated.recall owner) (activated.observe app owner) =
      (revealKernel profile (source.view owner)).bind fun disclose =>
        branch disclose (activated.recall owner) (activated.observe app owner) := by
    refine sourceLaw.trans ?_
    apply bind_congr_on_support _
    intro disclose _
    change (match (if disclose then rosterOpening? setup leaks owner event
      (activated.observe app owner) else none) with
      | none => app.silentPolicy (activated.recall owner) (activated.observe app owner)
      | some (candidate, raw) =>
          PMF.pure ((runtime setup).windowOpening leaks event candidate raw)) = _
    rw [openingEq]
  have scheduled : (some slot).map (fun selected => offset + selected.val) =
      some (activated.recall owner).length := by
    change some (offset + slot.val) = some (current.recall owner).length
    exact congrArg some atSlot.symm
  change (sourcePlayers owner (activated.recall owner) (activated.observe app owner)).bind _ = _
  simp only [sourcePlayers, Function.update_self, ReactiveApplication.scheduledPolicy,
    ite_eq_left scheduled]
  rw [actionLaw, PMF.bind_bind]
  apply bind_congr_on_support _
  intro disclose _
  change _ = (if (some slot).map (fun selected => offset + selected.val) =
      some (activated.recall owner).length then
        branch disclose (activated.recall owner) (activated.observe app owner)
    else app.silentPolicy (activated.recall owner) (activated.observe app owner)).bind _
  rw [ite_eq_left scheduled]
  apply bind_congr_on_support _
  intro response _
  have after : offset + slot.val <
      ((activated.respond app owner response).recall owner).length := by
    rw [app.respond_recall_length]
    simp only [↓reduceIte]
    change offset + slot.val < (current.recall owner).length + 1
    omega
  exact (scheduled_tail_waiting setup leaks network owner event offset slot opening remaining
    (activated.respond app owner response) after).trans
      (scheduled_tail_waiting setup leaks network owner event offset slot (branch disclose)
        remaining (activated.respond app owner response) after).symm

private theorem scheduled_optional_opening
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId) (offset : Nat)
    {slots : Nat} (slot : Fin slots) (selected : Option (Handle (graph setup) × Raw L)) :
    Function.update (fun _ => (application setup leaks).silentPolicy) owner
      ((application setup leaks).scheduledPolicy offset (some slot)
        (fun past view => match selected with
          | none => (application setup leaks).silentPolicy past view
          | some (candidate, raw) =>
              PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
        (application setup leaks).silentPolicy) =
      match selected with
      | none => fun _ => (application setup leaks).silentPolicy
      | some (candidate, raw) =>
          (runtime setup).openingWindowPlayers leaks owner event candidate raw offset
            (some slot) := by
  funext who past view
  cases selected with
  | none =>
      by_cases same : who = owner
      · subst who
        simp only [Function.update_self, ReactiveApplication.scheduledPolicy, ite_self]
      · rw [Function.update_of_ne same]
  | some selected =>
      rcases selected with ⟨candidate, raw⟩
      by_cases same : who = owner
      · subst who
        simp only [Function.update_self, openingWindowPlayers, ↓reduceIte]
      · simp only [Function.update_of_ne same, openingWindowPlayers, same, ↓reduceIte]

/-- The actual timed source compiler's complete disclosure phase is a joint
source-choice and native-execution law. The source draw is independent of the
shared timing draw, while observations remain intact. -/
theorem sourceServiceTimedPolicy_reveal_phase_law
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
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (owned : (graph setup).actor? event = some owner)
      (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event),
    let phase := (rosters event).map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    (runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network phase execution =
      (revealKernel profile (source.view owner)).bind fun disclose =>
        (timing event owner owned).bind fun slot =>
          (runtime setup).runInteractionPlan leaks
            (match (if disclose then rosterOpening? setup leaks owner event
              (execution.observe (application setup leaks) owner) else none) with
            | none => fun _ => (application setup leaks).silentPolicy
            | some (candidate, raw) =>
                (runtime setup).openingWindowPlayers leaks owner event candidate raw
                  (execution.recall owner).length (some slot)) network phase execution := by
  intro index event owned ready unsent counted phase
  rw [sourceServiceTimedPolicy_phase_law setup leaks rosters timing wholeProfile event owner owned
    network ticks execution (soleReady_of_ready setup execution.application ready)
    counted.le]
  conv_rhs => rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro slot _
  obtain ⟨visited, remaining, position, selected⟩ :=
    split_owner_visit owner (rosters event) slot.val slot.isLt
  have prefixLaw := sourceServiceTimedFamily_reveal_law setup leaks rosters fresh binding
    unresolved next wholeProfile profile refs source embedding refsBefore rank aligned execution
    agree history valid recalled origins effective network (rosters event) visited remaining slot
    position
    (by rw [counted, selected]) ready unsent
  have splitPlan : phase =
      ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        (List.replicate ticks .tick ++ [.expire event]) := by
    simp only [phase, List.append_assoc, List.cons_append, List.nil_append]
  let app := application setup leaks
  let branch : Bool → app.Policy := fun disclose past view =>
    match (if disclose then rosterOpening? setup leaks owner event
      (execution.observe app owner) else none) with
    | none => app.silentPolicy past view
    | some (candidate, raw) =>
        PMF.pure ((runtime setup).windowOpening leaks event candidate raw)
  let leftPlayers := Function.update (fun _ => app.silentPolicy) owner
    (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event slot)
  let rightPlayers := fun disclose => Function.update (fun _ => app.silentPolicy) owner
    (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
      (branch disclose) app.silentPolicy)
  trans (revealKernel profile (source.view owner)).bind fun disclose =>
    (runtime setup).runInteractionPlan leaks (rightPlayers disclose) network phase execution
  · change (runtime setup).runInteractionPlan leaks leftPlayers network phase execution = _
    rw [splitPlan, runInteractionPlan_append, prefixLaw, PMF.bind_bind]
    apply bind_congr_on_support _
    intro disclose _
    conv_rhs => rw [runInteractionPlan_append]
    apply bind_congr_on_support _
    intro current _
    exact servicePlan_players_eq setup leaks _ _ network _ (by simp) (by intro who; simp) current
  · apply bind_congr_on_support _
    intro disclose _
    have players := scheduled_optional_opening setup leaks owner event
      (rosterOffset setup rosters owner event) slot
      (if disclose then rosterOpening? setup leaks owner event (execution.observe app owner)
        else none)
    change (runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => app.silentPolicy) owner
        (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
          (branch disclose) app.silentPolicy)) network phase execution = _
    rw [players, counted]

/-- The real timed compiler realizes the guarded-disclosure traffic kernel
used by the conditional likelihood induction, for every focal player. -/
theorem sourceServiceTimedPolicy_reveal_traffic
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
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) (focal : Player) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (owned : (graph setup).actor? event = some owner)
      (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map ((runtime setup).bindingTraffic leaks focal) =
      (revealKernel profile (source.view owner)).bind
        (guardedDisclosureTranscript setup leaks network (rosters event) owner focal event ticks
          (timing event owner owned) execution) := by
  intro index event owned ready unsent counted
  rw [sourceServiceTimedPolicy_reveal_phase_law setup leaks rosters timing fresh binding
    unresolved next wholeProfile profile refs source embedding refsBefore rank aligned execution
    agree history valid recalled origins effective network ticks owned ready unsent counted,
    PMF.map_bind]
  apply bind_congr_on_support _
  intro disclose _
  cases disclose with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const,
        guardedDisclosureTranscript, List.append_assoc, List.cons_append, List.nil_append]
      rfl
  | true =>
      cases openingEq : rosterOpening? setup leaks owner event
          (execution.observe (application setup leaks) owner) with
      | none =>
          simp only [↓reduceIte, openingEq, PMF.bind_const, guardedDisclosureTranscript,
            List.append_assoc, List.cons_append, List.nil_append]
          rfl
      | some packet =>
          rcases packet with ⟨candidate, raw⟩
          simp only [↓reduceIte, openingEq, PMF.map_bind, guardedDisclosureTranscript,
            List.append_assoc, List.cons_append, List.nil_append]
          rfl

end Vegas
