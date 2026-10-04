/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMenu
import Vegas.Pending.ReactiveResolutionWindowState
import Vegas.Pending.ReactiveServiceRecall

/-! # An actual decision in every retained resolution roster

The final unsent owner visit requires a bounded false or true decision. Earlier
waiting and passive samples remain present, but cannot consume the last visit
without recording an actual call for this event.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceService_resolution_roster_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (initial final : (application setup leaks).Execution)
    (ready : initial.application.config.cut.Ready event)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (unsent : (runtime setup).eventRecorded leaks (initial.recall owner) event = false)
    (opportunity : owner ∈ visits)
    (ends : (initial.recall owner).length + visits.count owner =
      rosterOffset setup rosters owner event + (rosters event).count owner)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    (runtime setup).eventRecorded leaks (final.recall owner) event = true := by
  let app := application setup leaks
  have ordinary : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions (runtime setup) leaks who past view :=
    fun who past view response selected => sourceServiceMenu_in_compiled setup leaks bounds
      rosters who past view (lawful who past view response selected)
  induction visits generalizing initial with
  | nil => cases opportunity
  | cons actor rest ih =>
      obtain ⟨middle, step, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at step
      change middle ∈ ((initial.environmentStep app (.activate actor)).bind
        (app.invoke players actor)).support at step
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at step
      obtain ⟨sample, _, step⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ step)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ step
      let activated := initial.sampledActivation app actor sample
      have sole := soleReady_of_ready setup initial.application ready
      have allowed := ordinary actor _ _ response chosen
      have actual : response = (⟨none⟩ : app.Action) ∨
          actor = owner ∧ (runtime setup).submittedEvent? leaks response = some event := by
        rcases bounds.compiled_resolution_cases (runtime setup) leaks actor _ _ event owner
          payload binding checks outputEq codeEq node sole response allowed with silent |
            ⟨acting, _, _, shape⟩ |
            ⟨candidate, value, evidence, acting, _, _, _, _, _, shape⟩
        · exact Or.inl silent
        · exact Or.inr ⟨Option.some.inj (acting.symm.trans owned), by rw [shape]; rfl⟩
        · exact Or.inr ⟨Option.some.inj (acting.symm.trans owned), by rw [shape]; rfl⟩
      rcases actual with silent | ⟨acting, named⟩
      · have restOpportunity : owner ∈ rest := by
          by_contra absent
          have acting : actor = owner := (List.mem_cons.mp opportunity).resolve_right absent |>.symm
          subst actor
          have last : (activated.recall owner).length + 1 =
              rosterOffset setup rosters owner event + (rosters event).count owner := by
            change (initial.recall owner).length + 1 = _
            simpa only [List.count_cons_self, List.count_eq_zero.mpr absent, Nat.zero_add]
              using ends
          have named := sourceService_final_resolution_submits setup leaks bounds rosters owner
            (activated.recall owner) (activated.observe app owner) event payload binding checks
            outputEq codeEq node (sole.ownTurn owned) owned
            ((initial.application.publicView_eventReady event).mpr ready) unsent last response
            (lawful owner _ _ response chosen)
          rw [silent] at named
          cases named
        have preserved := (runtime setup).silent_response_preserves leaks _ activated
          (published.learn actor sample) actor response silent
        have nextUnsent : (runtime setup).eventRecorded leaks
            ((activated.respond app actor response).recall owner) event = false := by
          rw [(runtime setup).eventRecorded_respond_transport leaks activated actor owner
            response silent event]
          exact unsent
        apply ih (activated.respond app actor response)
          (by rw [preserved.1]; exact ready)
          (by rw [preserved.2.1]; exact preserved.2.2.2.2.1)
          nextUnsent restOpportunity _ tail
        rw [app.respond_recall_length]
        change (initial.recall owner).length + (if actor = owner then 1 else 0) +
          rest.count owner = _
        simp only [List.count_cons, beq_iff_eq] at ends
        by_cases same : actor = owner
        · subst actor
          simp only [↓reduceIte] at ends ⊢
          omega
        · simpa only [same, ↓reduceIte, Nat.add_zero] using ends
      · subst actor
        have recorded := (runtime setup).eventRecorded_respond leaks activated owner response
          event named
        obtain ⟨entry, member, addressed⟩ :=
          ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
        apply ((runtime setup).eventRecorded_iff leaks _ event).mpr
        exact ⟨entry, ((runtime setup).runInteractionPlan_recall_prefix leaks players network
          (rest.map ServiceInstruction.player) (activated.respond app owner response)
          final tail owner).subset member, addressed⟩

end Vegas
