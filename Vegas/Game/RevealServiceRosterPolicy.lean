/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePolicy
import Vegas.Pending.ReactiveOpeningWindow
import Interaction.ScheduledOpeningPosterior

/-! # One source policy over all visits of a revelation roster

These are policies on the existing native input: actual own recall and current
view. The source disclosure law and authentic opening are recovered from that
view. A fixed public roster supplies response-count offsets. Conditional timing
is a proof parameter for fully mixed approximants, not private runtime state.

The limiting policy explicitly stops after an opening. It does not evaluate a
zero-probability latent-mixture fallback at an off-path early opening. Coverage,
all-site consistency and sequential optimality remain separate obligations.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def rosterOffset (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (event : (graph setup).EventId) : Nat :=
  (((List.finRange (graph setup).order.eventCount).take event.val).flatMap rosters).count who

/-- The immutable local opening data, before choosing an evidence-request
representation. It reads only the owner's current application observation. -/
def rosterOpening? (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (event : (graph setup).EventId)
    (view : (application setup leaks).PlayerView) : Option (Handle (graph setup) × Raw L) :=
  match nodeView (graph setup) event with
  | .sample .. | .bind .. => none
  | .resolve _ payload binding checks _ _ =>
      match EventGraph.EventCode.resolveOutput? binding checks true
          view.application.observation.store with
      | none | some .failure => none
      | some (.success value) => do
          let candidate ← view.application.publicView.accepted binding.field
          if candidate.1 ≠ who then none else some (candidate, ⟨payload, value⟩)

def rosterSelection {slots : Nat} (choice : FinDist Bool) (timing : FinDist (Fin slots)) :
    FinDist (Option (Fin slots)) :=
  choice.bind fun disclose => if disclose then timing.map some else FinDist.pure none

theorem rosterSelection_projects {slots : Nat} (choice : FinDist Bool)
    (timing : FinDist (Fin slots)) :
    (rosterSelection choice timing).map Option.isSome = choice := by
  rw [rosterSelection, FinDist.map_bind]
  conv_rhs => rw [← FinDist.bind_pure choice]
  apply FinDist.bind_congr
  intro disclose _
  cases disclose <;> simp only [Bool.false_eq_true, ↓reduceIte, FinDist.map_pure,
    Option.isSome_none, FinDist.map_comp, Function.comp_def, Option.isSome_some, FinDist.map_const]

theorem rosterSelection_fullSupport {slots : Nat} (choice : FinDist Bool)
    (timing : FinDist (Fin slots)) (choiceFull : choice.FullSupport)
    (timingFull : timing.FullSupport) : (rosterSelection choice timing).FullSupport := by
  intro selected
  simp only [rosterSelection, FinDist.support_bind, Set.mem_iUnion]
  cases selected with
  | none => exact ⟨false, choiceFull false, by simp⟩
  | some slot =>
      refine ⟨true, choiceFull true, ?_⟩
      simp only [↓reduceIte, FinDist.support_map]
      exact ⟨slot, timingFull slot, rfl⟩

/-- One total native policy for every event and visit. On actual phase
histories its recomputed source law is constant, because all retained responses
preserve the application until protected inclusion. -/
def rosterPolicy (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.serviceGrant with
  | none => (application setup leaks).replayPolicy past view
  | some event =>
      if owned : (graph setup).actor? event = some who then
        match rosterOpening? setup leaks who event view with
        | none => (application setup leaks).replayPolicy past view
        | some (candidate, raw) =>
            ((application setup leaks).policyMixture
              (rosterSelection (sourceChoiceLaw setup leaks profile who view)
                (timing event who owned))
              (fun selected => (application setup leaks).scheduledPolicy
                (rosterOffset setup rosters who event) selected
                (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
                (application setup leaks).replayPolicy)).policy past view
      else (application setup leaks).replayPolicy past view

open Classical in
/-- The explicit common limit: wait before the final owner visit, make the
source choice there, and retain only silence/replay after any earlier opening. -/
def rosterLimitPolicy (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.serviceGrant with
  | none => (application setup leaks).replayPolicy past view
  | some event =>
      if (graph setup).actor? event = some who then
        match rosterOpening? setup leaks who event view with
        | none => (application setup leaks).replayPolicy past view
        | some (candidate, raw) =>
            let offset := rosterOffset setup rosters who event
            let opening := (runtime setup).windowOpening leaks event candidate raw
            if ((past.drop offset).any fun entry => entry.action = opening) ||
                decide (past.length + 1 ≠ offset + (rosters event).count who) then
              (application setup leaks).replayPolicy past view
            else (sourceChoiceLaw setup leaks profile who view).bind fun disclose =>
              if disclose then FinDist.pure opening
              else (application setup leaks).replayPolicy past view
      else (application setup leaks).replayPolicy past view

/-- Source choices do not inspect network observations or response recall. -/
theorem sourceChoiceLaw_application_eq (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : BehavioralProfile setup.program) (who : Player)
    (left right : (application setup leaks).Execution)
    (same : left.application = right.application) :
    sourceChoiceLaw setup leaks profile who (left.observe (application setup leaks) who) =
      sourceChoiceLaw setup leaks profile who (right.observe (application setup leaks) who) := by
  rcases left with ⟨leftState, leftNetwork, leftReceipts, leftRecall, leftEnvironment⟩
  rcases right with ⟨rightState, rightNetwork, rightReceipts, rightRecall, rightEnvironment⟩
  change leftState = rightState at same
  cases same
  rfl

theorem rosterOpening?_application_eq (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (event : (graph setup).EventId)
    (left right : (application setup leaks).Execution)
    (same : left.application = right.application) :
    rosterOpening? setup leaks who event (left.observe (application setup leaks) who) =
      rosterOpening? setup leaks who event (right.observe (application setup leaks) who) := by
  rcases left with ⟨leftState, leftNetwork, leftReceipts, leftRecall, leftEnvironment⟩
  rcases right with ⟨rightState, rightNetwork, rightReceipts, rightRecall, rightEnvironment⟩
  change leftState = rightState at same
  cases same
  rfl

/-- Every response supported by the single roster policy preserves the
application. This includes responses after an off-path early opening. -/
theorem rosterPolicy_application (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (who : Player)
    (execution : (application setup leaks).Execution)
    (action : (application setup leaks).Action)
    (supported : action ∈ (rosterPolicy setup leaks rosters timing profile who
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
    (execution.respond (application setup leaks) who action).application =
      execution.application := by
  have waiting (member : action ∈ ((application setup leaks).replayPolicy
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
      (execution.respond (application setup leaks) who action).application =
        execution.application := by
    rcases (application setup leaks).replayPolicy_cases _ _ action member with rfl | ⟨id, rfl⟩
    · rfl
    · rfl
  unfold rosterPolicy at supported
  split at supported
  · exact waiting supported
  · split at supported
    · split at supported
      · exact waiting supported
      · rw [ReactiveApplication.policyMixture_policy] at supported
        obtain ⟨selected, _, supported⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
        unfold ReactiveApplication.scheduledPolicy at supported
        split at supported
        · cases FinDist.mem_support_pure.mp supported
          rfl
        · exact waiting supported
    · exact waiting supported

/-- The source disclosure law remains fixed after each actual supported
response, regardless of timing, replay, pending observations, or own recall. -/
theorem rosterPolicy_sourceChoice_unchanged (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (who observer : Player)
    (execution : (application setup leaks).Execution)
    (action : (application setup leaks).Action)
    (supported : action ∈ (rosterPolicy setup leaks rosters timing profile who
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
    sourceChoiceLaw setup leaks profile observer
      ((execution.respond (application setup leaks) who action).observe
        (application setup leaks) observer) =
      sourceChoiceLaw setup leaks profile observer
        (execution.observe (application setup leaks) observer) :=
  sourceChoiceLaw_application_eq setup leaks profile observer _ _
    (rosterPolicy_application setup leaks rosters timing profile who execution action supported)

/-- A whole actual activation window, at any prefix length, leaves the source
application observation unchanged under the fixed roster policy. The proof
quantifies over every supported timing/replay branch, including early openings. -/
theorem rosterPolicy_run_application (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (rosterPolicy setup leaks rosters timing profile) network
        (visits.map ServiceInstruction.player) initial).support) :
    final.application = initial.application := by
  let app := application setup leaks
  induction visits generalizing initial with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      rfl
  | cons who rest ih =>
      simp only [List.map_cons, EventGraphRuntime.runInteractionPlan,
        EventGraphRuntime.interactionStep, EventGraphRuntime.interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map,
        FinDist.bind_bind] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨action, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      exact (ih _ reached).trans
        (rosterPolicy_application setup leaks rosters timing profile who
          (initial.sampledActivation app who sample) action supported)

theorem rosterPolicy_phase_data (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (rosterPolicy setup leaks rosters timing profile) network
        (visits.map ServiceInstruction.player) initial).support)
    (who : Player) (event : (graph setup).EventId) :
    sourceChoiceLaw setup leaks profile who (final.observe (application setup leaks) who) =
      sourceChoiceLaw setup leaks profile who (initial.observe (application setup leaks) who) ∧
    rosterOpening? setup leaks who event (final.observe (application setup leaks) who) =
      rosterOpening? setup leaks who event (initial.observe (application setup leaks) who) := by
  have same := rosterPolicy_run_application setup leaks rosters timing profile network visits
    initial final reached
  exact ⟨sourceChoiceLaw_application_eq setup leaks profile who final initial same,
    rosterOpening?_application_eq setup leaks who event final initial same⟩

/-- At an actual phase, the single policy is the same scheduled mixture at
every input with that unchanged application state. Its parameters are recovered
from the initial local observation, not supplied by a hidden global state. -/
theorem rosterPolicy_at_phase (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (unchanged : current.application = initial.application) (who : Player) :
    rosterPolicy setup leaks rosters timing profile who (current.recall who)
        (current.observe (application setup leaks) who) =
      (runtime setup).openingWindowMixturePlayers leaks owner event candidate raw
        (rosterOffset setup rosters owner event)
        (rosterSelection
          (sourceChoiceLaw setup leaks profile owner
            (initial.observe (application setup leaks) owner))
          (timing event owner owned)) who (current.recall who)
            (current.observe (application setup leaks) who) := by
  have grant : (current.observe (application setup leaks) who).application.publicView.serviceGrant =
      some event := by change current.application.serviceGrant = some event; rw [unchanged, granted]
  unfold rosterPolicy
  simp only [grant]
  by_cases active : who = owner
  · subst who
    rw [dite_eq_left owned,
      rosterOpening?_application_eq setup leaks owner event current initial unchanged, opening,
      sourceChoiceLaw_application_eq setup leaks profile owner current initial unchanged]
    simp only [EventGraphRuntime.openingWindowMixturePlayers, Function.update_self]
  · have foreign : (graph setup).actor? event ≠ some who := by
      rw [owned]
      exact fun same => active (Option.some.inj same).symm
    rw [dite_eq_right foreign]
    simp only [EventGraphRuntime.openingWindowMixturePlayers, Function.update_of_ne active]

/-- The actual global policy evaluates every finite prefix of a phase as its
single locally recovered timing mixture. No phase-specific strategy is assumed
in the statement of the left execution. -/
theorem rosterPolicy_window_eq (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (unchanged : current.application = initial.application)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player) :
    (runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
        network (visits.map ServiceInstruction.player) current =
      (runtime setup).runInteractionPlan leaks
        ((runtime setup).openingWindowMixturePlayers leaks owner event candidate raw
          (rosterOffset setup rosters owner event)
          (rosterSelection
            (sourceChoiceLaw setup leaks profile owner
              (initial.observe (application setup leaks) owner))
            (timing event owner owned))) network
              (visits.map ServiceInstruction.player) current := by
  let app := application setup leaks
  induction visits generalizing current with
  | nil => rfl
  | cons who rest ih =>
      simp only [List.map_cons, EventGraphRuntime.runInteractionPlan,
        EventGraphRuntime.interactionStep, EventGraphRuntime.interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map,
        FinDist.bind_bind]
      apply FinDist.bind_congr
      intro sample _
      let activated := current.sampledActivation app who sample
      have law := rosterPolicy_at_phase setup leaks rosters timing profile initial activated
        event owner granted owned candidate raw opening unchanged who
      change (rosterPolicy setup leaks rosters timing profile who (activated.recall who)
        (activated.observe app who)).bind _ = _
      rw [law]
      apply FinDist.bind_congr
      intro action supported
      have original : action ∈ (rosterPolicy setup leaks rosters timing profile who
          (activated.recall who) (activated.observe app who)).support := by
        rw [law]
        exact supported
      apply ih (activated.respond app who action)
      exact (rosterPolicy_application setup leaks rosters timing profile who activated action
        original).trans unchanged

end Vegas.SourceProgram.RevealService
