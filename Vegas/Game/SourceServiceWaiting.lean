/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRosterPolicy
import Vegas.Pending.ReactiveSilentSettlement

/-! # Actual waiting before the final source opportunity

Before the selected owner's final visit, the full source policy executes the
existing replay law. The equality retains the entire execution, including
all passive samples and private response recall. Its application and public
allocation data are therefore unchanged even when the initial pool is empty.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every earlier response is a real replay-policy response. The bound counts
only owner visits, so arbitrary foreign visits may intervene. -/
theorem sourceServiceLastPolicy_waiting_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (initial : (application setup leaks).Execution)
    (sole : initial.application.publicView.SoleReady event)
    (before : (initial.recall owner).length + visits.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner) :
    (runtime setup).runInteractionPlan leaks
        (sourceServiceLastPolicy setup leaks rosters profile) network
        (visits.map ServiceInstruction.player) initial =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).silentPolicy)
        network (visits.map ServiceInstruction.player) initial := by
  classical
  let app := application setup leaks
  induction visits generalizing initial with
  | nil => rfl
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
        Function.comp_def]
      apply bind_congr_on_support _
      intro sample _
      let activated := initial.sampledActivation app who sample
      have law : sourceServiceLastPolicy setup leaks rosters profile who
          (activated.recall who) (activated.observe app who) =
          app.silentPolicy (activated.recall who) (activated.observe app who) := by
        apply sourceServiceLastPolicy_wait setup leaks rosters profile who
          (activated.recall who) (activated.observe app who)
        intro selected serving
        have facts := PublicView.ownTurn?_spec _ who selected serving
        change initial.application.publicView.EventReady selected ∧ _ at facts
        cases sole.2 selected facts.1
        cases Option.some.inj (facts.2.symm.trans owned)
        apply Or.inr
        change (initial.recall owner).length + 1 ≠ _
        simp only [List.count_cons_self] at before
        omega
      change (sourceServiceLastPolicy setup leaks rosters profile who
        (activated.recall who) (activated.observe app who)).bind _ =
        (app.silentPolicy (activated.recall who) (activated.observe app who)).bind _
      rw [law]
      apply bind_congr_on_support _
      intro response supported
      have unchanged : (activated.respond app who response).application = initial.application := by
        rcases app.silentPolicy_cases _ _ response supported with rfl; rfl
      apply ih _ (by rw [unchanged]; exact sole)
      rw [app.respond_recall_length]
      change (initial.recall owner).length + (if who = owner then 1 else 0) + rest.count owner < _
      by_cases same : who = owner
      · subst who
        simp only [List.count_cons_self] at before
        simp only [↓reduceIte]
        omega
      · simp only [same, ↓reduceIte, Nat.add_zero]
        simpa only [List.count_cons_of_ne same] using before

/-- The actual waiting prefix preserves the complete application and public
settlement data. Its replay copies and observed samples remain in the state. -/
theorem sourceServiceLastPolicy_waiting_data
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (initial final : (application setup leaks).Execution)
    (sole : initial.application.publicView.SoleReady event)
    (before : (initial.recall owner).length + visits.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner)
    (safe : Message Player (WitnessedPacket (graph setup)) → Prop)
    (packets : initial.network.Satisfies safe)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network
        (visits.map ServiceInstruction.player) initial).support) :
    final.application = initial.application ∧ final.network.ledger = initial.network.ledger ∧
      final.receipts = initial.receipts ∧ final.network.nextSerial = initial.network.nextSerial ∧
      final.network.Satisfies safe ∧ initial.network.pending ⊆ final.network.pending := by
  rw [sourceServiceLastPolicy_waiting_law setup leaks rosters profile network event owner owned
    visits initial sole before] at reached
  exact (runtime setup).silent_window_preserves leaks (fun _ =>
    (application setup leaks).silentPolicy) network owner initial
      (fun current who response _ _ supported => (application setup leaks).silentPolicy_cases
        (current.recall who) (current.observe (application setup leaks) who) response supported)
      safe packets visits final reached

private theorem include_players_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (first second : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (execution : (application setup leaks).Execution) :
    (runtime setup).interactionStep leaks first network (.includeLatest event owner) execution =
      (runtime setup).interactionStep leaks second network
        (.includeLatest event owner) execution := by
  simp only [interactionStep, interactionInstruction, PMF.pure_bind]
  rcases (runtime setup).reactiveLatest_wait_or_owned leaks event owner
      (execution.observeEnvironment ((runtime setup).reactiveApplication leaks)) with
    waiting | ⟨id, _authored, included⟩
  · rw [waiting]
    rfl
  · rw [included]
    rfl

theorem sourceServiceLastPolicy_foreign_tail
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (absent : owner ∉ visits)
    (initial : (application setup leaks).Execution)
    (sole : initial.application.publicView.SoleReady event) :
    (runtime setup).runInteractionPlan leaks
        (sourceServiceLastPolicy setup leaks rosters profile) network
        (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).silentPolicy)
        network (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial := by
  let app := application setup leaks
  induction visits generalizing initial with
  | nil =>
      simpa only [List.map_nil, List.nil_append, runInteractionPlan, PMF.bind_pure] using
        include_players_eq setup leaks _ _ network event owner initial
  | cons who rest ih =>
      have foreign : who ≠ owner := fun same => absent (by simp only [same, List.mem_cons_self])
      have restAbsent : owner ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, List.cons_append, runInteractionPlan, interactionStep,
        interactionInstruction, PMF.pure_bind, ReactiveApplication.dispatch,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
        Function.comp_def]
      apply bind_congr_on_support _
      intro sample _
      let activated := initial.sampledActivation app who sample
      have law := sourceServiceLastPolicy_wait setup leaks rosters profile who
        (activated.recall who) (activated.observe app who) fun selected serving => by
          have facts := PublicView.ownTurn?_spec _ who selected serving
          change initial.application.publicView.EventReady selected ∧ _ at facts
          cases sole.2 selected facts.1
          exact absurd (Option.some.inj (facts.2.symm.trans owned)) foreign
      change (sourceServiceLastPolicy setup leaks rosters profile who
        (activated.recall who) (activated.observe app who)).bind _ =
        (app.silentPolicy (activated.recall who) (activated.observe app who)).bind _
      rw [law]
      apply bind_congr_on_support _
      intro response supported
      apply ih restAbsent
      rcases app.silentPolicy_cases _ _ response supported with rfl; exact sole

theorem silent_window_eventRecorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).silentPolicy) network
        (visits.map ServiceInstruction.player) initial).support)
    (owner : Player) (event : (graph setup).EventId) :
    (runtime setup).eventRecorded leaks (final.recall owner) event =
      (runtime setup).eventRecorded leaks (initial.recall owner) event := by
  classical
  let app := application setup leaks
  induction visits generalizing initial with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rw [ih _ reached]
      by_cases same : owner = who
      · subst who
        rcases app.silentPolicy_cases _ _ response supported with rfl;
          simp only [eventRecorded, ReactiveApplication.Execution.respond, ↓reduceIte,
            List.any_append, List.any_cons, List.any_nil, submittedEvent?, reduceCtorEq,
            decide_false, Bool.or_false]
        rfl
      · rw [app.respond_recall_other _ who owner same]
        rfl

end Vegas
