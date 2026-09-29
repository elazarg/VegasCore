/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ScheduledChoicePosterior
import Vegas.Game.SourceServiceTimedDisclosure

/-! # The actual unsent disclosure timing posterior

Every earlier replay is evaluated at its recorded full input. The source view
and opening candidate remain fixed throughout that real replay window, so its
response likelihood is the source silence probability times the replay law.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Exact timing probabilities through a real replay window. The input posterior
may already include earlier visits of this phase. -/
theorem sourceServiceTimedMixture_replay_window_posterior
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
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (final : (application setup leaks).Execution) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (timing : PMF (Fin ((rosters event).count owner))) (count : Nat)
      (candidate : Handle (graph setup)) (raw : Raw L)
      (_opening : rosterOpening? setup leaks owner event
        (execution.observe (application setup leaks) owner) = some (candidate, raw))
      (_granted : execution.application.serviceGrant = some event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length =
        rosterOffset setup rosters owner event + count)
      (_within : count + visits.count owner ≤ (rosters event).count owner)
      (_small : ((revealKernel profile (source.view owner)) true).toReal < 1)
      (_old : ∀ slot, ((((application setup leaks).policyMixture timing
        (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event)).posterior
          (execution.recall owner)) slot).toReal =
        (timing slot).toReal * (if slot.val < count then
          1 - ((revealKernel profile (source.view owner)) true).toReal else 1) /
            PMF.deferredSurvival (((revealKernel profile (source.view owner)) true).toReal)
              timing count)
      (_reached : final ∈ ((runtime setup).runInteractionPlan leaks
        (fun _ => (application setup leaks).replayPolicy) network
          (visits.map ServiceInstruction.player) execution).support),
    ∀ slot, ((((application setup leaks).policyMixture timing
      (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event)).posterior
        (final.recall owner)) slot).toReal =
      (timing slot).toReal * (if slot.val < count + visits.count owner then
        1 - ((revealKernel profile (source.view owner)) true).toReal else 1) /
          PMF.deferredSurvival (((revealKernel profile (source.view owner)) true).toReal)
            timing (count + visits.count owner) := by
  intro index event timing count candidate raw opening granted unsent counted within small old
    reached
  let app := application setup leaks
  let choice := revealKernel profile (source.view owner)
  let family := sourceServiceTimedFamily setup leaks rosters wholeProfile owner event
  let offset := rosterOffset setup rosters owner event
  induction visits generalizing execution count with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simpa only [List.count_nil, Nat.add_zero] using old
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
        Function.comp_def]
        at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      let activated := execution.sampledActivation app actor sample
      let current := activated.respond app actor response
      have casesResponse := app.replayPolicy_cases (activated.recall actor)
        (activated.observe app actor) response supported
      have same : current.application = execution.application :=
        ((runtime setup).replay_response_preserves leaks (fun _ => True) activated
          ⟨by simp, by simp, by simp, by simp⟩ actor response casesResponse).1
      have currentAgree : refs.Agrees source.state current.application.config.store := by
        rw [same]; exact agree
      have currentHistory : decodeHistory setup.program (current.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = source.history := by
        rw [same]; exact history
      have currentValid : current.application.BindingInvariant := by rw [same]; exact valid
      have currentRecall := app.respond_inputRecall activated actor response recalled
      have currentOrigins := origins_replayed setup leaks activated (origins.learn actor sample)
        actor response casesResponse
      have currentOpening := (rosterOpening?_application_eq setup leaks owner event current
        execution same).trans opening
      have currentGrant : current.application.serviceGrant = some event := by rw [same]; exact
        granted
      have currentUnsent : (runtime setup).eventRecorded leaks (current.recall owner) event =
          false := by
        by_cases equal : actor = owner
        · subst actor
          rcases casesResponse with rfl | ⟨id, rfl⟩ <;>
            simpa only [current, activated, eventRecorded, ReactiveApplication.Execution.respond,
              ReactiveApplication.Execution.sampledActivation,
              ↓reduceIte, List.any_append, List.any_cons, List.any_nil, submittedEvent?,
              reduceCtorEq, decide_false, Bool.or_false] using unsent
        · rw [app.respond_recall_other activated actor owner (Ne.symm equal) response]
          exact unsent
      by_cases sameOwner : actor = owner
      · subst actor
        have countBound : count < (rosters event).count owner := by
          simp only [List.count_cons_self] at within
          omega
        let slot : Fin ((rosters event).count owner) := ⟨count, countBound⟩
        obtain ⟨entry, entryRecall, entryView, entryAction⟩ :=
          (runtime setup).response_recall_entry leaks activated owner response
        have selectedLaw := sourceServiceOpportunity_reveal setup leaks fresh binding unresolved
          next
          wholeProfile profile refs source embedding refsBefore rank aligned activated agree history
          valid recalled (origins.learn owner sample) effective granted unsent
        have activatedOpening : rosterOpening? setup leaks owner event
            (activated.observe app owner) = some (candidate, raw) :=
          (rosterOpening?_application_eq setup leaks owner event activated execution rfl).trans
            opening
        replace selectedLaw : sourceServiceOpportunity setup leaks wholeProfile owner event
          (activated.recall owner) (activated.observe app owner) =
            choice.bind (fun disclose => match (if disclose then rosterOpening? setup leaks owner
              event (activated.observe app owner) else none) with
              | none => app.replayPolicy (activated.recall owner) (activated.observe app owner)
              | some (candidate, raw) =>
                  PMF.pure ((runtime setup).windowOpening leaks event candidate raw)) :=
          selectedLaw
        have actionLaw : sourceServiceOpportunity setup leaks wholeProfile owner event
            (execution.recall owner) entry.beforeView = choice.bind (fun disclose =>
              if disclose then PMF.pure ((runtime setup).windowOpening leaks event candidate
                raw)
              else app.replayPolicy (execution.recall owner) entry.beforeView) := by
          rw [entryView]
          refine selectedLaw.trans ?_
          apply bind_congr_on_support _
          intro disclose _
          cases disclose <;> simp only [Bool.false_eq_true, ↓reduceIte, activatedOpening]
          rfl
        have different : response ≠ (runtime setup).windowOpening leaks event candidate raw := by
          rcases casesResponse with rfl | ⟨id, rfl⟩ <;> simp [windowOpening]
        have responseProbability : ((sourceServiceOpportunity setup leaks wholeProfile owner event
            (execution.recall owner) entry.beforeView) entry.action).toReal =
              (1 - (choice true).toReal) *
                ((app.replayPolicy (execution.recall owner) entry.beforeView)
                    entry.action).toReal := by
          rw [actionLaw, PMF.bind_bool_mix, mix_apply_toReal,
            entryAction, PMF.pure_apply_of_ne _ _ different, ENNReal.toReal_zero, mul_zero,
            zero_add]
        have likelihood (selected : Fin ((rosters event).count owner)) :
            ((family selected (execution.recall owner) entry.beforeView) entry.action).toReal =
              (if selected = slot then 1 - (choice true).toReal else 1) *
                ((app.replayPolicy (execution.recall owner) entry.beforeView)
                    entry.action).toReal := by
          change (((if some (offset + selected.val) = some (execution.recall owner).length then
            sourceServiceOpportunity setup leaks wholeProfile owner event
              (execution.recall owner) entry.beforeView else
                app.replayPolicy (execution.recall owner) entry.beforeView))
                    entry.action).toReal = _
          by_cases equal : selected = slot
          · subst selected
            simp only [counted, slot, offset, ↓reduceIte]
            exact responseProbability
          · have unused : some (offset + selected.val) ≠ some (execution.recall owner).length := by
              rw [counted]
              intro equalCount
              apply equal
              apply Fin.ext
              exact Nat.add_left_cancel (Option.some.inj equalCount)
            simp only [ite_eq_right unused, equal, ↓reduceIte, one_mul]
            rfl
        have possible : entry.action ∈
            (app.replayPolicy (execution.recall owner) entry.beforeView).support := by
          rw [entryAction, entryView]
          exact supported
        have update := app.scheduledChoice_posterior_step timing family ((choice true).toReal)
          (ENNReal.toReal_nonneg) small (execution.recall owner) entry slot
            (app.replayPolicy (execution.recall owner) entry.beforeView) possible likelihood old
        have currentCount : (current.recall owner).length = offset + (count + 1) := by
          rw [app.respond_recall_length]
          simp only [↓reduceIte]
          change (execution.recall owner).length + 1 = _
          rw [counted]
          omega
        have updated : ∀ selected, (((app.policyMixture timing family).posterior
            (current.recall owner)) selected).toReal = (timing selected).toReal *
              (if selected.val < count + 1 then 1 - (choice true).toReal else 1) /
                PMF.deferredSurvival ((choice true).toReal) timing (count + 1) := by
          rw [entryRecall]
          exact update
        have tail := ih current currentAgree currentHistory currentValid currentRecall
          currentOrigins
          (count + 1) currentOpening currentGrant currentUnsent currentCount (by
            simp only [List.count_cons_self] at within
            omega) updated reached
        simpa only [List.count_cons_self, Nat.add_assoc, Nat.add_comm 1] using tail
      · have unchanged : current.recall owner = execution.recall owner :=
          app.respond_recall_other activated actor owner (Ne.symm sameOwner) response
        have tail := ih current currentAgree currentHistory currentValid currentRecall
          currentOrigins
          count currentOpening currentGrant currentUnsent
          ((congrArg List.length unchanged).trans counted) (by
            simpa only [List.count_cons_of_ne sameOwner] using within)
          (by simpa only [unchanged] using old) reached
        simpa only [List.count_cons_of_ne sameOwner] using tail

/-- Starting at a real phase boundary, the timing posterior is derived from
its original timing law and the complete supported native replay prefix. -/
theorem sourceServiceTimedMixture_replay_window_posterior_initial
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
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (final : (application setup leaks).Execution) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (timing : PMF (Fin ((rosters event).count owner)))
      (candidate : Handle (graph setup)) (raw : Raw L)
      (_opening : rosterOpening? setup leaks owner event
        (execution.observe (application setup leaks) owner) = some (candidate, raw))
      (_granted : execution.application.serviceGrant = some event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event)
      (_within : visits.count owner ≤ (rosters event).count owner)
      (_small : ((revealKernel profile (source.view owner)) true).toReal < 1)
      (_reached : final ∈ ((runtime setup).runInteractionPlan leaks
        (fun _ => (application setup leaks).replayPolicy) network
          (visits.map ServiceInstruction.player) execution).support),
    ∀ slot, ((((application setup leaks).policyMixture timing
      (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event)).posterior
        (final.recall owner)) slot).toReal =
      (timing slot).toReal * (if slot.val < visits.count owner then
        1 - ((revealKernel profile (source.view owner)) true).toReal else 1) /
          PMF.deferredSurvival (((revealKernel profile (source.view owner)) true).toReal)
            timing (visits.count owner) := by
  intro index event timing candidate raw opening granted unsent counted within small reached
  let app := application setup leaks
  let family := sourceServiceTimedFamily setup leaks rosters wholeProfile owner event
  have dormant := app.policyMixture_posterior_dormant timing family app.replayPolicy
    (rosterOffset setup rosters owner event)
    (fun slot past view earlier => app.scheduledPolicy_before _ _ _ _ past view earlier)
    (execution.recall owner) counted.le
  have old (slot : Fin ((rosters event).count owner)) :
      (((app.policyMixture timing family).posterior (execution.recall owner)) slot).toReal =
        (timing slot).toReal * (if slot.val < 0 then
          1 - ((revealKernel profile (source.view owner)) true).toReal else 1) /
            PMF.deferredSurvival (((revealKernel profile (source.view owner)) true).toReal)
              timing 0 := by
    rw [dormant]
    simp only [Nat.not_lt_zero, ↓reduceIte, mul_one, PMF.deferredSurvival,
      PMF.timingPrefix_zero, mul_zero, sub_zero, div_one]
  have result := sourceServiceTimedMixture_replay_window_posterior setup leaks rosters fresh binding
    unresolved next wholeProfile profile refs source embedding refsBefore rank aligned execution
    agree history valid recalled origins effective network visits final timing 0 candidate raw
    opening granted unsent (by simpa only [Nat.add_zero] using counted)
    (by simpa only [Nat.zero_add] using within) small old reached
  simpa only [Nat.zero_add] using result

end Vegas
