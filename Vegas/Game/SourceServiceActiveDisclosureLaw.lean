/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedDisclosure

/-! # Guarded disclosure laws from an active native decision

The current passive observation has already occurred. The remaining execution
retains the actual posterior over scheduled opportunities, including past
opportunities at which the effective source choice was silence.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The effective source disclosure can be drawn before the remaining active
phase. A past timing slot executes only replay responses on both sides. -/
theorem sourceServiceTimedFamily_active_reveal_law
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
    (network : (runtime setup).NetworkPolicy leaks) (remaining : List Player) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (slot : Fin ((rosters event).count owner))
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
      (revealKernel profile (source.view owner)).bind fun disclose =>
        let branch := fun past view =>
          match (if disclose then rosterOpening? setup leaks owner event
            (execution.observe app owner) else none) with
          | none => app.replayPolicy past view
          | some (candidate, raw) =>
              FinDist.pure ((runtime setup).windowOpening leaks event candidate raw)
        let rawPlayers := Function.update (fun _ => app.replayPolicy) owner
          (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
            branch app.replayPolicy)
        (app.invoke rawPlayers owner execution).bind
          ((runtime setup).runInteractionPlan leaks rawPlayers network plan) := by
  intro index event slot within granted unsent app players plan
  let offset := rosterOffset setup rosters owner event
  let opening := sourceServiceOpportunity setup leaks wholeProfile owner event
  let branch : Bool → app.Policy := fun disclose past view =>
    match (if disclose then rosterOpening? setup leaks owner event
      (execution.observe app owner) else none) with
    | none => app.replayPolicy past view
    | some (candidate, raw) =>
        FinDist.pure ((runtime setup).windowOpening leaks event candidate raw)
  let rawPlayers := fun disclose => Function.update (fun _ => app.replayPolicy) owner
    (app.scheduledPolicy offset (some slot) (branch disclose) app.replayPolicy)
  change (app.invoke players owner execution).bind
    ((runtime setup).runInteractionPlan leaks players network plan) =
    (revealKernel profile (source.view owner)).bind fun disclose =>
      (app.invoke (rawPlayers disclose) owner execution).bind
        ((runtime setup).runInteractionPlan leaks (rawPlayers disclose) network plan)
  by_cases now : offset + slot.val = (execution.recall owner).length
  · have actionLaw := sourceServiceOpportunity_reveal setup leaks fresh binding unresolved next
      wholeProfile profile refs source embedding refsBefore rank aligned execution agree history
      valid recalled origins effective granted unsent
    change opening (execution.recall owner) (execution.observe app owner) =
      (revealKernel profile (source.view owner)).bind
        (fun disclose => branch disclose (execution.recall owner) (execution.observe app owner))
      at actionLaw
    have scheduled : some (rosterOffset setup rosters owner event + slot.val) =
        some (execution.recall owner).length := congrArg some now
    simp only [players, rawPlayers, ReactiveApplication.invoke, Function.update_self,
      sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
      offset, ite_eq_left scheduled, FinDist.bind_map]
    change (opening (execution.recall owner) (execution.observe app owner)).bind _ = _
    rw [actionLaw, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro disclose _
    apply FinDist.bind_congr
    intro response _
    have after : offset + slot.val <
        ((execution.respond app owner response).recall owner).length := by
      rw [app.respond_recall_length]
      simp only [↓reduceIte, now]
      omega
    exact (scheduled_tail_waiting setup leaks network owner event offset slot opening remaining
      (execution.respond app owner response) after).trans
      (scheduled_tail_waiting setup leaks network owner event offset slot (branch disclose)
        remaining (execution.respond app owner response) after).symm
  · have unused : some (rosterOffset setup rosters owner event + slot.val) ≠
        some (execution.recall owner).length := fun equal => now (Option.some.inj equal)
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
    have currentCount : (current.recall owner).length = (execution.recall owner).length + 1 := by
      simpa only [↓reduceIte] using app.respond_recall_length execution owner owner response
    by_cases passed : offset + slot.val < (execution.recall owner).length
    · have after : offset + slot.val < (current.recall owner).length := by omega
      rw [scheduled_tail_waiting setup leaks network owner event offset slot opening remaining
        current after]
      conv_rhs =>
        arg 2
        ext disclose
        rw [scheduled_tail_waiting setup leaks network owner event offset slot (branch disclose)
          remaining current after]
      rw [FinDist.bind_const]
    · have currentAgree : refs.Agrees source.state current.application.config.store := by
        rw [same]
        exact agree
      have currentHistory : decodeHistory setup.program (current.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = source.history := by
        rw [same]
        exact history
      have currentValid : current.application.BindingInvariant := by rw [same]; exact valid
      have currentRecall := app.respond_inputRecall execution owner response recalled
      have currentOrigins := origins_replayed setup leaks execution origins owner response
        (app.replayPolicy_cases _ _ response supported)
      have currentGrant : current.application.serviceGrant = some event := by
        rw [same]
        exact granted
      have currentUnsent : (runtime setup).eventRecorded leaks (current.recall owner) event =
          false := by
        rcases app.replayPolicy_cases _ _ response supported with rfl | ⟨id, rfl⟩ <;>
          simpa only [current, eventRecorded, ReactiveApplication.Execution.respond, ↓reduceIte,
            List.any_append, List.any_cons, List.any_nil, submittedEvent?, reduceCtorEq,
            decide_false, Bool.or_false] using unsent
      obtain ⟨visited, tail, position, counted⟩ := split_owner_visit owner remaining
        (offset + slot.val - (current.recall owner).length) (by
          change offset + slot.val < _ at within
          omega)
      have selected : offset + slot.val = (current.recall owner).length + visited.count owner := by
        omega
      have law := sourceServiceTimedFamily_reveal_law setup leaks rosters fresh binding
        unresolved next wholeProfile profile refs source embedding refsBefore rank aligned
        current currentAgree currentHistory currentValid currentRecall currentOrigins effective
        network remaining visited tail slot position selected currentGrant currentUnsent
      have openingEq := rosterOpening?_application_eq setup leaks owner event current execution same
      dsimp only [event, index, app] at openingEq
      simp only [openingEq, branch, current, app, event, index, plan,
        sourceServiceTimedFamily] at law ⊢
      exact law

/-- The actual active timed compiler disintegrates into its recall-conditioned
schedule and the effective source disclosure law. Past silent opportunities
remain in the posterior and produce no new opening. -/
theorem sourceServiceTimedPolicy_active_reveal_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
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
    (network : (runtime setup).NetworkPolicy leaks) (remaining : List Player) (ticks : Nat) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
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
      (revealKernel profile (source.view owner)).bind fun disclose =>
        posterior.bind fun slot =>
          let branch := fun past view =>
            match (if disclose then rosterOpening? setup leaks owner event
              (execution.observe app owner) else none) with
            | none => app.replayPolicy past view
            | some (candidate, raw) =>
                FinDist.pure ((runtime setup).windowOpening leaks event candidate raw)
          let scheduled := Function.update (fun _ => app.replayPolicy) owner
            (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
              branch app.replayPolicy)
          (app.invoke scheduled owner execution).bind
            ((runtime setup).runInteractionPlan leaks scheduled network phase) := by
  intro index event owned granted unsent counted app family posterior players phase
  rw [sourceServiceTimedPolicy_active_phase_law setup leaks rosters timing wholeProfile event
    owner owned network remaining ticks execution granted]
  conv_rhs => rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro slot _
  have within : rosterOffset setup rosters owner event + slot.val <
      (execution.recall owner).length + 1 + remaining.count owner := by
    rw [counted]
    exact Nat.add_lt_add_left slot.isLt _
  have active := sourceServiceTimedFamily_active_reveal_law setup leaks rosters fresh binding
    unresolved next wholeProfile profile refs source embedding refsBefore rank aligned execution
    agree history valid recalled origins effective network remaining slot within granted unsent
  let scheduled := Function.update (fun _ => app.replayPolicy) owner (family slot)
  let branch : Bool → app.Policy := fun disclose past view =>
    match (if disclose then rosterOpening? setup leaks owner event
      (execution.observe app owner) else none) with
    | none => app.replayPolicy past view
    | some (candidate, raw) =>
        FinDist.pure ((runtime setup).windowOpening leaks event candidate raw)
  let rawPlayers := fun disclose => Function.update (fun _ => app.replayPolicy) owner
    (app.scheduledPolicy (rosterOffset setup rosters owner event) (some slot)
      (branch disclose) app.replayPolicy)
  let firstSteps := remaining.map ServiceInstruction.player ++ [.includeLatest event owner]
  let maintenance : List (ServiceInstruction (graph setup)) :=
    List.replicate ticks .tick ++ [.expire event]
  have split : phase = firstSteps ++ maintenance := by
    simp only [phase, firstSteps, maintenance, List.append_assoc, List.cons_append, List.nil_append]
  change (app.invoke scheduled owner execution).bind
    ((runtime setup).runInteractionPlan leaks scheduled network phase) =
    (revealKernel profile (source.view owner)).bind fun disclose =>
      (app.invoke (rawPlayers disclose) owner execution).bind
        ((runtime setup).runInteractionPlan leaks (rawPlayers disclose) network phase)
  change (app.invoke scheduled owner execution).bind
    ((runtime setup).runInteractionPlan leaks scheduled network firstSteps) =
    (revealKernel profile (source.view owner)).bind (fun disclose =>
      (app.invoke (rawPlayers disclose) owner execution).bind
        ((runtime setup).runInteractionPlan leaks (rawPlayers disclose) network firstSteps))
    at active
  rw [split]
  conv_lhs =>
    arg 2
    ext current
    rw [runInteractionPlan_append]
  rw [← FinDist.bind_bind, active, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro disclose _
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
