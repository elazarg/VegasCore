/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedBinding
import Vegas.Game.SourceServiceTimedAdmissibility

/-! # Source binding laws from an active native decision

The current response starts after its passive observation. Conditioning timing
on the player's actual recall leaves only unpassed slots. Every such branch
executes the original source binding kernel within the remaining phase.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Disintegrate the source binding choice from the already active response
and the remaining roster. The current observation is not sampled again. -/
theorem sourceServiceTimedFamily_active_binding_law
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
    (remaining : List Player) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (slot : Fin ((rosters event).count owner))
      (_notPassed : (execution.recall owner).length ≤
        rosterOffset setup rosters owner event + slot.val)
      (_within : rosterOffset setup rosters owner event + slot.val <
        (execution.recall owner).length + 1 + remaining.count owner)
      (_granted : execution.application.serviceGrant = some event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false),
    let app := application setup leaks
    let players := Function.update (fun _ => app.replayPolicy) owner
      (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event slot)
    let plan := remaining.map ServiceInstruction.player ++ [.includeLatest event owner]
    (app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network plan) =
      (commitKernel profile (source.view owner)).bind fun choice =>
        let rawPlayers := Function.update (fun _ => app.replayPolicy) owner
          (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
            (fun _ _ => FinDist.pure
              ((runtime setup).reactiveBinding leaks owner event payload choice serial))
            app.replayPolicy)
        (app.invoke rawPlayers owner execution).bind
          ((runtime setup).runInteractionPlan leaks rawPlayers network plan) := by
  intro index event slot notPassed within granted unsent app players plan
  let offset := rosterOffset setup rosters owner event
  let opening := sourceServiceOpportunity setup leaks wholeProfile owner event
  let raw := fun choice => (runtime setup).reactiveBinding leaks owner event payload choice serial
  let rawPlayers := fun choice => Function.update (fun _ => app.replayPolicy) owner
    (app.scheduledPolicy offset (some slot) (fun _ _ => FinDist.pure (raw choice)) app.replayPolicy)
  change (app.invoke players owner execution).bind
    ((runtime setup).runInteractionPlan leaks players network plan) =
    (commitKernel profile (source.view owner)).bind fun choice =>
      (app.invoke (rawPlayers choice) owner execution).bind
        ((runtime setup).runInteractionPlan leaks (rawPlayers choice) network plan)
  by_cases now : offset + slot.val = (execution.recall owner).length
  · have outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind owner payload := by
      change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
        ((toEventGraph setup.program).nodes event) = _
      exact aligned.graphSuffix.nodeEq index
    have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq := by
      cases viewed : nodeView (graph setup) event with
      | sample otherPayload law kind code => cases kind.symm.trans outputEq
      | resolve other otherPayload binding checks kind code => cases kind.symm.trans outputEq
      | bind other otherPayload kind code =>
          obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
          rfl
    have sourceLaw := sourceServicePolicy_commit setup leaks fresh guard next wholeProfile profile
      refs source embedding refsBefore rank aligned execution agree history granted
    have responses : sourceServicePolicy setup leaks wholeProfile owner
        (execution.recall owner) (execution.observe app owner) =
          (commitKernel profile (source.view owner)).map raw := by
      apply sourceLaw.trans
      apply FinDist.map_congr_of_eq_on_support
      intro choice _
      exact serviceDecision_binding_fresh (runtime setup) leaks execution owner event payload
        outputEq codeEq node serial freshSlot candidate choice
    have actionLaw : opening (execution.recall owner) (execution.observe app owner) =
        (commitKernel profile (source.view owner)).map raw := by
      simp only [opening, sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte]
      rw [responses, FinDist.bind_map, FinDist.map_eq_bind]
      apply FinDist.bind_congr
      intro choice _
      cases choice <;> rfl
    have scheduled : some (rosterOffset setup rosters owner event + slot.val) =
        some (execution.recall owner).length := congrArg some now
    simp only [players, rawPlayers, ReactiveApplication.invoke, Function.update_self,
      sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
      offset, ite_eq_left scheduled, FinDist.bind_map, FinDist.pure_bind]
    change (opening (execution.recall owner) (execution.observe app owner)).bind _ = _
    rw [actionLaw, FinDist.bind_map]
    apply FinDist.bind_congr
    intro choice _
    have after : offset + slot.val <
        ((execution.respond app owner (raw choice)).recall owner).length := by
      rw [app.respond_recall_length]
      simp only [↓reduceIte, now]
      omega
    exact (scheduled_tail_waiting setup leaks network owner event offset slot opening remaining
      (execution.respond app owner (raw choice)) after).trans
      (scheduled_tail_waiting setup leaks network owner event offset slot
        (fun _ _ => FinDist.pure (raw choice)) remaining
        (execution.respond app owner (raw choice)) after).symm
  · have unused : some (rosterOffset setup rosters owner event + slot.val) ≠
        some (execution.recall owner).length :=
      fun equal => now (Option.some.inj equal)
    simp only [ReactiveApplication.invoke, players, rawPlayers, Function.update_self,
      sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
      offset, ite_eq_right unused, FinDist.bind_map]
    conv_rhs => rw [FinDist.bind_comm]
    apply FinDist.bind_congr
    intro response supported
    let current := execution.respond app owner response
    have same : current.application = execution.application :=
      ((runtime setup).replay_response_preserves leaks (fun _ => True) execution
        ⟨by simp, by simp, by simp, by simp⟩ owner response
        (app.replayPolicy_cases _ _ response supported)).1
    have currentAgree : refs.Agrees source.state current.application.config.store := by
      rw [same]
      exact agree
    have currentHistory : decodeHistory setup.program (current.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history := by
      rw [same]
      exact history
    have currentSlot : reactiveFreshSlot (current.observe app owner).application = some serial := by
      change reactiveFreshSlot (app.observePlayer current.application owner) = _
      rw [same]
      exact freshSlot
    have currentCandidate : current.application.candidates.lookup (owner, .prepared serial) =
        .fresh := by rw [same]; exact candidate
    have currentGrant : current.application.serviceGrant = some event := by rw [same]; exact granted
    have currentUnsent : (runtime setup).eventRecorded leaks (current.recall owner) event =
        false := by
      rcases app.replayPolicy_cases _ _ response supported with rfl | ⟨id, rfl⟩ <;>
        simpa only [current, eventRecorded, ReactiveApplication.Execution.respond, ↓reduceIte,
          List.any_append, List.any_cons, List.any_nil, submittedEvent?, reduceCtorEq,
          decide_false, Bool.or_false] using unsent
    have currentCount : (current.recall owner).length = (execution.recall owner).length + 1 := by
      simpa only [↓reduceIte] using app.respond_recall_length execution owner owner response
    obtain ⟨visited, tail, position, counted⟩ := split_owner_visit owner remaining
      (offset + slot.val - (current.recall owner).length) (by
        change offset + slot.val < _ at within
        change (execution.recall owner).length ≤ offset + slot.val at notPassed
        omega)
    have selected : offset + slot.val = (current.recall owner).length + visited.count owner := by
      change (execution.recall owner).length ≤ offset + slot.val at notPassed
      omega
    exact sourceServiceTimedFamily_binding_law setup leaks rosters fresh guard next
      wholeProfile profile refs source embedding refsBefore rank aligned current currentAgree
      currentHistory serial currentSlot currentCandidate network remaining visited tail slot
      position selected currentGrant currentUnsent

/-- At any actual unsent binding decision, the remaining physical execution
is the source binding kernel followed by the current posterior over submission
times. The identity includes the current response and protected deadline service. -/
theorem sourceServiceTimedPolicy_active_binding_law [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (permitted : ∀ who, (wholeProfile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore rank)
    (execution : (application setup leaks).Execution)
    (remainingFuel : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remainingFuel, some owner, execution⟩))
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (serial : Nat)
    (freshSlot : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (remaining : List Player) (ticks : Nat) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (owned : (graph setup).actor? event = some owner)
      (_granted : execution.application.serviceGrant = some event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length + 1 + remaining.count owner =
        rosterOffset setup rosters owner event + (rosters event).count owner),
    let app := application setup leaks
    let family := sourceServiceTimedFamily setup leaks rosters wholeProfile owner event
    let posterior := (app.policyMixture (timing event owner owned) family).posterior
      (execution.recall owner)
    let players := sourceServiceTimedPolicy setup leaks rosters timing wholeProfile
    let phase := remaining.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    (app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network phase) =
      (commitKernel profile (source.view owner)).bind fun choice =>
        posterior.bind fun slot =>
          let scheduled := Function.update (fun _ => app.replayPolicy) owner
            (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
              (fun _ _ => FinDist.pure
                ((runtime setup).reactiveBinding leaks owner event payload choice serial))
              app.replayPolicy)
          (app.invoke scheduled owner execution).bind
            ((runtime setup).runInteractionPlan leaks scheduled network phase) := by
  intro index event owned granted unsent counted app family posterior players phase
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have positive : 0 < (rosters event).count owner :=
    List.count_pos_iff.mpr (opportunities event owner payload outputEq)
  let last : Fin ((rosters event).count owner) := ⟨(rosters event).count owner - 1, by omega⟩
  have future := sourceServiceTimedMixture_binding_future setup leaks bounds values initialValues
    capacity rosters opportunities network wholeProfile permitted owner
    ⟨remainingFuel, some owner, execution⟩ trace rfl event granted owned payload outputEq unsent
    (timing event owner owned) last (full event owner owned last) (by dsimp only [last]; omega)
  rw [sourceServiceTimedPolicy_active_phase_law setup leaks rosters timing wholeProfile event
    owner owned network remaining ticks execution granted]
  conv_rhs => rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro slot supported
  have notPassed := future slot supported
  have within : rosterOffset setup rosters owner event + slot.val <
      (execution.recall owner).length + 1 + remaining.count owner := by
    rw [counted]
    exact Nat.add_lt_add_left slot.isLt _
  have active := sourceServiceTimedFamily_active_binding_law setup leaks rosters fresh guard next
    wholeProfile profile refs source embedding refsBefore rank aligned execution agree history
    serial freshSlot candidate network remaining slot notPassed within granted unsent
  let scheduled := Function.update (fun _ => app.replayPolicy) owner (family slot)
  let raw := fun choice => (runtime setup).reactiveBinding leaks owner event payload choice serial
  let rawPlayers := fun choice => Function.update (fun _ => app.replayPolicy) owner
    (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
      (fun _ _ => FinDist.pure (raw choice)) app.replayPolicy)
  let firstSteps := remaining.map ServiceInstruction.player ++ [.includeLatest event owner]
  let maintenance : List (ServiceInstruction (graph setup)) :=
    List.replicate ticks .tick ++ [.expire event]
  have split : phase = firstSteps ++ maintenance := by
    simp only [phase, firstSteps, maintenance, List.append_assoc, List.cons_append, List.nil_append]
  change (app.invoke scheduled owner execution).bind
    ((runtime setup).runInteractionPlan leaks scheduled network phase) =
    (commitKernel profile (source.view owner)).bind fun choice =>
      (app.invoke (rawPlayers choice) owner execution).bind
        ((runtime setup).runInteractionPlan leaks (rawPlayers choice) network phase)
  change (app.invoke scheduled owner execution).bind
    ((runtime setup).runInteractionPlan leaks scheduled network firstSteps) =
    (commitKernel profile (source.view owner)).bind (fun choice =>
      (app.invoke (rawPlayers choice) owner execution).bind
        ((runtime setup).runInteractionPlan leaks (rawPlayers choice) network firstSteps)) at active
  rw [split]
  conv_lhs =>
    arg 2
    ext current
    rw [runInteractionPlan_append]
  rw [← FinDist.bind_bind, active, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro choice _
  conv_rhs =>
    arg 2
    ext current
    rw [runInteractionPlan_append]
  rw [FinDist.bind_bind]
  apply FinDist.bind_congr
  intro current _
  apply FinDist.bind_congr
  intro final _
  exact servicePlan_players_eq setup leaks _ _ network maintenance
    (by simp [maintenance]) (by intro who; simp [maintenance]) final

end Vegas.SourceProgram.RevealService
