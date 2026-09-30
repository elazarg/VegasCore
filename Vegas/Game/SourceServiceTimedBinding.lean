/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedPolicy
import Vegas.Game.RevealServiceRosterLaw
import Vegas.Game.SourceServiceBindingPhase
import GameTheoryExtensions.Math.Probability.Support

/-! # Binding lotteries at arbitrary scheduled owner visits

The timed family runs the original source binding lottery at its selected
visit. Before and after that visit, actual passive observations and all replay
choices are retained. The law below records the whole execution.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem scheduled_window_waiting
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (offset : Nat) {slots : Nat} (slot : Fin slots)
    (opening : (application setup leaks).Policy)
    (visits : List Player) (initial : (application setup leaks).Execution)
    (separated : (initial.recall owner).length + visits.count owner ≤ offset + slot.val ∨
      offset + slot.val < (initial.recall owner).length) :
    (runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).replayPolicy) owner
        ((application setup leaks).scheduledPolicy offset (some slot) opening
          (application setup leaks).replayPolicy)) network
      (visits.map ServiceInstruction.player) initial =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
        network (visits.map ServiceInstruction.player) initial := by
  classical
  let app := application setup leaks
  induction visits generalizing initial with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
        Function.comp_def]
      apply bind_congr_on_support _
      intro sample _
      let activated := initial.sampledActivation app actor sample
      have same : (Function.update (fun _ => app.replayPolicy) owner
          (app.scheduledPolicy offset (some slot) opening app.replayPolicy)) actor
          (activated.recall actor) (activated.observe app actor) =
            app.replayPolicy (activated.recall actor) (activated.observe app actor) := by
        by_cases equal : actor = owner
        · subst actor
          rw [Function.update_self]
          unfold ReactiveApplication.scheduledPolicy
          apply ite_eq_right
          simp only [Option.map_some, Option.some.injEq]
          change offset + slot.val ≠ (initial.recall owner).length
          simp only [List.count_cons_self] at separated
          omega
        · rw [Function.update_of_ne equal]
      change ((Function.update (fun _ => app.replayPolicy) owner
        (app.scheduledPolicy offset (some slot) opening app.replayPolicy)) actor
        (activated.recall actor) (activated.observe app actor)).bind _ = _
      rw [same]
      apply bind_congr_on_support _
      intro response _
      apply ih
      rw [app.respond_recall_length]
      change (initial.recall owner).length + (if actor = owner then 1 else 0) +
          rest.count owner ≤ offset + slot.val ∨
        offset + slot.val < (initial.recall owner).length + (if actor = owner then 1 else 0)
      by_cases equal : actor = owner
      · subst actor
        simp only [List.count_cons_self] at separated
        simp only [↓reduceIte]
        omega
      · simp only [List.count_cons_of_ne equal] at separated
        simpa only [equal, ↓reduceIte, Nat.add_zero] using separated

theorem scheduled_tail_waiting
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (event : (graph setup).EventId) (offset : Nat)
    {slots : Nat} (slot : Fin slots) (opening : (application setup leaks).Policy)
    (visits : List Player) (initial : (application setup leaks).Execution)
    (after : offset + slot.val < (initial.recall owner).length) :
    (runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).replayPolicy) owner
        ((application setup leaks).scheduledPolicy offset (some slot) opening
          (application setup leaks).replayPolicy)) network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
        network (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial := by
  rw [runInteractionPlan_append, runInteractionPlan_append,
    scheduled_window_waiting setup leaks network owner offset slot opening visits initial
      (Or.inr after)]
  apply bind_congr_on_support _
  intro current _
  exact servicePlan_players_eq setup leaks _ _ network _ (by simp) (by intro who; simp) current

/-- From any unsent point before the selected owner slot, the actual source
family is the original binding lottery followed by its signed native window.
The remaining visits need not be the complete phase roster. The equality
retains full executions and does not require an empty network. -/
theorem sourceServiceTimedFamily_binding_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
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
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore rank)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (serial : Nat)
    (freshSlot : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (network : (runtime setup).NetworkPolicy leaks)
    (visits visited remaining : List Player) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (slot : Fin ((rosters event).count owner))
      (_position : visits = visited ++ owner :: remaining)
      (_selected : rosterOffset setup rosters owner event + slot.val =
        (execution.recall owner).length + visited.count owner)
      (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false),
    (runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).replayPolicy) owner
        (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event slot)) network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution =
      (commitKernel profile (source.view owner)).bind fun choice =>
        (runtime setup).runInteractionPlan leaks
          (Function.update (fun _ => (application setup leaks).replayPolicy) owner
            ((application setup leaks).scheduledPolicy
              (rosterOffset setup rosters owner event) (some slot)
              (fun _ _ => PMF.pure
                ((runtime setup).reactiveBinding leaks owner event payload choice serial))
              (application setup leaks).replayPolicy)) network
          (visits.map ServiceInstruction.player ++ [.includeLatest event owner])
          execution := by
  intro index event slot position selected ready unsent
  let app := application setup leaks
  let offset := rosterOffset setup rosters owner event
  let opening := sourceServiceOpportunity setup leaks wholeProfile owner event
  let sourcePlayers := Function.update (fun _ => app.replayPolicy) owner
    (app.scheduledPolicy offset (some slot) opening app.replayPolicy)
  let raw := fun choice => (runtime setup).reactiveBinding leaks owner event payload choice serial
  let rawPlayers := fun choice => Function.update (fun _ => app.replayPolicy) owner
    (app.scheduledPolicy offset (some slot) (fun _ _ => PMF.pure (raw choice)) app.replayPolicy)
  let transport : Player → app.Policy := fun _ => app.replayPolicy
  have before : (execution.recall owner).length + visited.count owner ≤ offset + slot.val := by
    exact selected.ge
  have sourcePrefix := scheduled_window_waiting setup leaks network owner offset slot opening
    visited execution (Or.inl before)
  have rawPrefix := fun choice => scheduled_window_waiting setup leaks network owner offset slot
    (fun _ _ => PMF.pure (raw choice)) visited execution (Or.inl before)
  change (runtime setup).runInteractionPlan leaks sourcePlayers network
    (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution =
    (commitKernel profile (source.view owner)).bind fun choice =>
      (runtime setup).runInteractionPlan leaks (rawPlayers choice) network
        (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) execution
  simp only [position, List.map_append, List.map_cons, List.append_assoc,
    (runtime setup).runInteractionPlan_append]
  rw [sourcePrefix]
  dsimp only [rawPlayers, app]
  conv_rhs =>
    arg 2
    ext choice
    rw [rawPrefix choice]
  conv_rhs => rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro current reached
  have preserved := (runtime setup).replay_window_preserves leaks transport network owner execution
    (fun current who response _ _ member => app.replayPolicy_cases _ _ response member)
    (fun _ => True) ⟨by simp, by simp, by simp, by simp⟩ visited current reached
  have same := preserved.1
  have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
  have currentAgree : refs.Agrees source.state current.application.config.store := by
    rw [same]; exact agree
  have currentHistory : decodeHistory setup.program (current.application.config.history.map
      (setup.eventGraph.fromModeCompletion .sequential)) = source.history := by
    rw [same]; exact history
  have currentSlot : reactiveFreshSlot (current.observe app owner).application = some serial := by
    change reactiveFreshSlot (app.observePlayer current.application owner) = _
    rw [same]
    exact freshSlot
  have currentCandidate : current.application.candidates.lookup (owner, .prepared serial) =
      .fresh := by rw [same]; exact candidate
  have currentUnsent := (replay_window_eventRecorded setup leaks network visited execution current
    reached owner event).trans unsent
  have currentCount := fixed_plan_response_counts setup leaks network transport
    (visited.map ServiceInstruction.player) (by simp) execution current reached owner
  simp only [List.filterMap_map, Function.comp_def, instructionActor,
    List.filterMap_some] at currentCount
  have atSlot : (current.recall owner).length = offset + slot.val := by
    rw [currentCount]
    exact selected.symm
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    exact aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_bind _ _
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
  have sourceLaw := sourceServicePolicy_commit setup leaks fresh guard next wholeProfile profile
    refs source embedding refsBefore rank aligned activated currentAgree currentHistory currentReady
  have responses : sourceServicePolicy setup leaks wholeProfile owner
      (activated.recall owner) (activated.observe app owner) =
        (commitKernel profile (source.view owner)).map raw := by
    apply sourceLaw.trans
    apply map_congr_on_support _
    intro choice _
    exact serviceDecision_binding_fresh (runtime setup) leaks activated owner event payload
      outputEq codeEq node serial currentSlot currentCandidate choice
  have actionLaw : opening (activated.recall owner) (activated.observe app owner) =
      (commitKernel profile (source.view owner)).map raw := by
    simp only [opening, sourceServiceOpportunity, activatedUnsent, Bool.false_eq_true, ↓reduceIte]
    rw [responses, PMF.bind_map, ← PMF.bind_pure_comp, Function.comp_def]
    apply bind_congr_on_support _
    intro choice _
    cases choice <;> rfl
  have scheduled : (some slot).map (fun selected => offset + selected.val) =
      some (activated.recall owner).length := by
    change some (offset + slot.val) = some (current.recall owner).length
    exact congrArg some atSlot.symm
  change (sourcePlayers owner (activated.recall owner) (activated.observe app owner)).bind _ = _
  simp only [sourcePlayers, Function.update_self, ReactiveApplication.scheduledPolicy,
    ite_eq_left scheduled]
  rw [actionLaw, PMF.bind_map]
  apply bind_congr_on_support _
  intro choice _
  change _ = (if (some slot).map (fun selected => offset + selected.val) =
      some (activated.recall owner).length then PMF.pure (raw choice)
    else app.replayPolicy (activated.recall owner) (activated.observe app owner)).bind _
  rw [ite_eq_left scheduled, PMF.pure_bind]
  have after : offset + slot.val <
      ((activated.respond app owner (raw choice)).recall owner).length := by
    rw [app.respond_recall_length]
    simp only [↓reduceIte]
    change offset + slot.val < (current.recall owner).length + 1
    omega
  exact (scheduled_tail_waiting setup leaks network owner event offset slot opening remaining
    (activated.respond app owner (raw choice)) after).trans
      (scheduled_tail_waiting setup leaks network owner event offset slot
        (fun _ _ => PMF.pure (raw choice)) remaining
        (activated.respond app owner (raw choice)) after).symm

theorem split_owner_visit (owner : Player) (visits : List Player)
    (count : Nat) (inside : count < visits.count owner) :
    ∃ before after, visits = before ++ owner :: after ∧ before.count owner = count := by
  induction visits generalizing count with
  | nil => simp only [List.count_nil] at inside; omega
  | cons actor rest ih =>
      by_cases same : actor = owner
      · subst actor
        cases count with
        | zero => exact ⟨[], rest, rfl, rfl⟩
        | succ count =>
            have bound : count < rest.count owner := by
              simp only [List.count_cons_self] at inside
              omega
            obtain ⟨before, after, equality, counted⟩ := ih count bound
            refine ⟨owner :: before, after, ?_, ?_⟩
            · simp only [List.cons_append, equality]
            · simp only [List.count_cons_self, counted]
      · have bound : count < rest.count owner := by
          simpa only [List.count_cons_of_ne same] using inside
        obtain ⟨before, after, equality, counted⟩ := ih count bound
        refine ⟨actor :: before, after, ?_, ?_⟩
        · simp only [List.cons_append, equality]
        · simpa only [List.count_cons_of_ne same] using counted

/-- A shared arbitrary timing law is independent of the original binding
choice in the actual global compiler's whole phase execution. This includes
protected inclusion, all deadline commands, and every correlated native field. -/
theorem sourceServiceTimedPolicy_binding_phase_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
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
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore rank)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (serial : Nat)
    (freshSlot : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
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
      (commitKernel profile (source.view owner)).bind fun choice =>
        (timing event owner owned).bind fun slot =>
          (runtime setup).runInteractionPlan leaks
            (Function.update (fun _ => (application setup leaks).replayPolicy) owner
              ((application setup leaks).scheduledPolicy
                (rosterOffset setup rosters owner event) (some slot)
                (fun _ _ => PMF.pure
                  ((runtime setup).reactiveBinding leaks owner event payload choice serial))
                (application setup leaks).replayPolicy)) network phase execution := by
  intro index event owned ready unsent counted phase
  rw [sourceServiceTimedPolicy_phase_law setup leaks rosters timing wholeProfile event owner owned
    network ticks execution (soleReady_of_ready setup execution.application ready) counted.le]
  conv_rhs => rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro slot _
  obtain ⟨visited, remaining, position, selected⟩ :=
    split_owner_visit owner (rosters event) slot.val slot.isLt
  have prefixLaw := sourceServiceTimedFamily_binding_law setup leaks rosters fresh guard next
    wholeProfile profile refs source embedding refsBefore rank aligned execution agree history
    serial freshSlot candidate network (rosters event) visited remaining slot position
    (by rw [counted, selected]) ready unsent
  have splitPlan : phase =
      ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        (List.replicate ticks .tick ++ [.expire event]) := by
    simp only [phase, List.append_assoc, List.cons_append, List.nil_append]
  let leftPlayers := Function.update (fun _ => (application setup leaks).replayPolicy) owner
    (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event slot)
  let rightPlayers := fun choice =>
    Function.update (fun _ => (application setup leaks).replayPolicy) owner
      ((application setup leaks).scheduledPolicy (rosterOffset setup rosters owner event)
        (some slot)
        (fun _ _ => PMF.pure
          ((runtime setup).reactiveBinding leaks owner event payload choice serial))
        (application setup leaks).replayPolicy)
  change (runtime setup).runInteractionPlan leaks leftPlayers network phase execution =
    (commitKernel profile (source.view owner)).bind fun choice =>
      (runtime setup).runInteractionPlan leaks (rightPlayers choice) network phase execution
  rw [splitPlan, runInteractionPlan_append, prefixLaw, PMF.bind_bind]
  apply bind_congr_on_support _
  intro choice _
  conv_rhs => rw [runInteractionPlan_append]
  apply bind_congr_on_support _
  intro current _
  exact servicePlan_players_eq setup leaks _ _ network _ (by simp) (by intro who; simp) current

end Vegas
