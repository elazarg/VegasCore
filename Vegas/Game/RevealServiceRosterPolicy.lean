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

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def rosterOffset (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (event : (graph setup).EventId) : Nat :=
  (((List.finRange (graph setup).order.eventCount).take event.val).flatMap rosters).count who

/-- A timing law: for each event with an owner, a distribution over the owner's
visits in that event's roster. -/
abbrev TimingLaw (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) : Type :=
  ∀ event who, (graph setup).actor? event = some who → PMF (Fin ((rosters event).count who))

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

def rosterSelection {slots : Nat} (choice : PMF Bool) (timing : PMF (Fin slots)) :
    PMF (Option (Fin slots)) :=
  choice.bind fun disclose => if disclose then timing.map some else PMF.pure none

theorem rosterSelection_projects {slots : Nat} (choice : PMF Bool)
    (timing : PMF (Fin slots)) :
    (rosterSelection choice timing).map Option.isSome = choice := by
  rw [rosterSelection, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure choice]
  apply bind_congr_on_support _
  intro disclose _
  cases disclose
  · simp only [Bool.false_eq_true, ↓reduceIte, PMF.pure_map, Option.isSome_none]
  · simp only [↓reduceIte, PMF.map_comp, Function.comp_def, Option.isSome_some]
    exact PMF.map_const _ _

theorem rosterSelection_fullSupport {slots : Nat} (choice : PMF Bool)
    (timing : PMF (Fin slots)) (choiceFull : FullSupport choice)
    (timingFull : FullSupport timing) : FullSupport (rosterSelection choice timing) := by
  intro selected
  simp only [rosterSelection, PMF.support_bind, Set.mem_iUnion]
  cases selected with
  | none => exact ⟨false, choiceFull false, by simp⟩
  | some slot =>
      refine ⟨true, choiceFull true, ?_⟩
      simp only [↓reduceIte, PMF.support_map]
      exact ⟨slot, timingFull slot, rfl⟩

/-- One total native policy for every event and visit. On actual phase
histories its recomputed source law is constant, because all retained responses
preserve the application until protected inclusion. -/
def rosterPolicy (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      PMF (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (application setup leaks).silentPolicy past view
  | some event =>
      if owned : (graph setup).actor? event = some who then
        match rosterOpening? setup leaks who event view with
        | none => (application setup leaks).silentPolicy past view
        | some (candidate, raw) =>
            ((application setup leaks).policyMixture
              (rosterSelection (sourceChoiceLaw setup leaks profile who view)
                (timing event who owned))
              (fun selected => (application setup leaks).scheduledPolicy
                (rosterOffset setup rosters who event) selected
                (fun _ _ => PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
                (application setup leaks).silentPolicy)).policy past view
      else (application setup leaks).silentPolicy past view

open Classical in
/-- The explicit common limit: wait before the final owner visit, make the
source choice there, and retain only silence after any earlier opening. -/
def rosterLimitPolicy (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (application setup leaks).silentPolicy past view
  | some event =>
      if (graph setup).actor? event = some who then
        match rosterOpening? setup leaks who event view with
        | none => (application setup leaks).silentPolicy past view
        | some (candidate, raw) =>
            let offset := rosterOffset setup rosters who event
            let opening := (runtime setup).windowOpening leaks event candidate raw
            if ((past.drop offset).any fun entry => entry.action = opening) ||
                decide (past.length + 1 ≠ offset + (rosters event).count who) then
              (application setup leaks).silentPolicy past view
            else (sourceChoiceLaw setup leaks profile who view).bind fun disclose =>
              if disclose then PMF.pure opening
              else (application setup leaks).silentPolicy past view
      else (application setup leaks).silentPolicy past view

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
      PMF (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (who : Player)
    (execution : (application setup leaks).Execution)
    (action : (application setup leaks).Action)
    (supported : action ∈ (rosterPolicy setup leaks rosters timing profile who
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
    (execution.respond (application setup leaks) who action).application =
      execution.application := by
  have waiting (member : action ∈ ((application setup leaks).silentPolicy
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
      (execution.respond (application setup leaks) who action).application =
        execution.application := by
    rcases (application setup leaks).silentPolicy_cases _ _ action member with rfl
    rfl
  unfold rosterPolicy at supported
  split at supported
  · exact waiting supported
  · split at supported
    · split at supported
      · exact waiting supported
      · rw [ReactiveApplication.policyMixture_policy] at supported
        obtain ⟨selected, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
        unfold ReactiveApplication.scheduledPolicy at supported
        split at supported
        · cases (PMF.mem_support_pure_iff _ _).mp supported
          rfl
        · exact waiting supported
    · exact waiting supported

/-- The source disclosure law remains fixed after each actual supported
response, regardless of timing, silence, pending observations, or own recall. -/
theorem rosterPolicy_sourceChoice_unchanged (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      PMF (Fin ((rosters event).count who)))
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
quantifies over every supported timing/silence branch, including early openings. -/
theorem rosterPolicy_run_application (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      PMF (Fin ((rosters event).count who)))
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
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons who rest ih =>
      simp only [List.map_cons, EventGraphRuntime.runInteractionPlan,
        EventGraphRuntime.interactionStep, EventGraphRuntime.interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨action, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (ih _ reached).trans
        (rosterPolicy_application setup leaks rosters timing profile who
          (initial.sampledActivation app who sample) action supported)

theorem rosterPolicy_phase_data (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      PMF (Fin ((rosters event).count who)))
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
      PMF (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (sole : initial.application.publicView.SoleReady event)
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
  have soleNow : current.application.publicView.SoleReady event := by
    rw [unchanged]
    exact sole
  unfold rosterPolicy
  by_cases active : who = owner
  · subst who
    have serving : (current.observe (application setup leaks) owner).application.publicView.ownTurn?
        owner = some event :=
      current.application.publicView.ownTurn?_of_ownTurn owner event (soleNow.ownTurn owned)
    simp only [serving]
    rw [dite_eq_left owned,
      rosterOpening?_application_eq setup leaks owner event current initial unchanged, opening,
      sourceChoiceLaw_application_eq setup leaks profile owner current initial unchanged]
    simp only [EventGraphRuntime.openingWindowMixturePlayers, Function.update_self]
  · have foreign : (graph setup).actor? event ≠ some who := by
      rw [owned]
      exact fun same => active (Option.some.inj same).symm
    have idle : (current.observe (application setup leaks) who).application.publicView.ownTurn?
        who = none := soleNow.ownTurn?_foreign foreign
    simp only [idle, EventGraphRuntime.openingWindowMixturePlayers, Function.update_of_ne active]

/-- The actual global policy evaluates every finite prefix of a phase as its
single locally recovered timing mixture. No phase-specific strategy is assumed
in the statement of the left execution. -/
theorem rosterPolicy_window_eq (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      PMF (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (initial current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (sole : initial.application.publicView.SoleReady event)
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
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def]
      apply bind_congr_on_support _
      intro sample _
      let activated := current.sampledActivation app who sample
      have law := rosterPolicy_at_phase setup leaks rosters timing profile initial activated
        event owner sole owned candidate raw opening unchanged who
      change (rosterPolicy setup leaks rosters timing profile who (activated.recall who)
        (activated.observe app who)).bind _ = _
      rw [law]
      apply bind_congr_on_support _
      intro action supported
      have original : action ∈ (rosterPolicy setup leaks rosters timing profile who
          (activated.recall who) (activated.observe app who)).support := by
        rw [law]
        exact supported
      apply ih (activated.respond app who action)
      exact (rosterPolicy_application setup leaks rosters timing profile who activated action
        original).trans unchanged

end Vegas
