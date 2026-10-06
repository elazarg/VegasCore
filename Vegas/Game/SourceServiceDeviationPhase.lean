/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixFactorization
import Vegas.Pending.ReactiveOwnerPhase
import GameTheoryExtensions.Math.Probability.ObservedChoice

/-! # One player's permitted deviation, phase by phase

The calendar serves one event per phase. Against the timed calendar profile, a
player who deviates within the permitted menu is silent in every phase whose
event it does not own: the menu offers it nothing else there. Such a phase
therefore runs exactly as under the timed profile.

In a phase of its own event the deviator may follow any permitted policy while
every other player is silent. The deviator's choice of a source action is then
a behavioral choice of its source view: its native input adds only traffic
whose law, given the source state, depends on that view alone, so the choice
can be simulated from the view by drawing that traffic privately.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- In a phase whose event a player does not own, the permitted menu offers
that player only silence. -/
theorem sourceServiceMenu_foreign_silent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (sole : view.application.publicView.SoleReady event)
    (foreign : (graph setup).actor? event ≠ some who)
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view) :
    response = ⟨none⟩ := by
  classical
  have idle := sole.ownTurn?_foreign foreign
  change response ∈ sourceServiceActions setup leaks bounds rosters who past view at member
  unfold sourceServiceActions at member
  have notRequired : ¬ bindingRequired setup leaks rosters who past view := by
    rintro ⟨chosen, _, selected, _⟩
    rw [idle] at selected
    cases selected
  rw [ite_eq_right notRequired] at member
  unfold MessageBounds.compiledActions at member
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | silenced
  · have offered := (Finset.mem_filter.mp decision).1
    unfold MessageBounds.decisionActions at offered
    simp only [idle] at offered
    exact Finset.mem_singleton.mp offered
  · exact Finset.mem_singleton.mp silenced

/-- A permitted policy is silent in a phase whose event its player does not own. -/
theorem permitted_foreign_silent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (policy : (application setup leaks).Policy)
    (lawful : ∀ past view response, response ∈ (policy past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (sole : view.application.publicView.SoleReady event)
    (foreign : (graph setup).actor? event ≠ some who) :
    policy past view = (application setup leaks).silentPolicy past view :=
  pmf_eq_pure_of_support_subset_singleton _ _ fun response member =>
    sourceServiceMenu_foreign_silent setup leaks bounds rosters who past view event sole foreign
      response (lawful past view response member)

open Classical in
/-- Silence wherever the permitted menu admits it, and a uniformly drawn
permitted response elsewhere. Every response of this policy is permitted. -/
def permittedSilence (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) : (application setup leaks).Policy := fun past view =>
  if (⟨none⟩ : (application setup leaks).Action) ∈
      (sourceServiceMenu setup leaks bounds rosters).actions who past view then
    (application setup leaks).silentPolicy past view
  else (sourceServiceMenu setup leaks bounds rosters).uniformResponses who past view

theorem permittedSilence_lawful (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (member : response ∈ (permittedSilence setup leaks bounds rosters who past view).support) :
    response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
  classical
  unfold permittedSilence at member
  split at member
  · rename_i silent
    rw [(application setup leaks).silentPolicy_cases past view response member]
    exact silent
  · exact ((sourceServiceMenu setup leaks bounds rosters).uniformResponses_support who past view
      response).mp member

theorem permittedSilence_foreign (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (sole : view.application.publicView.SoleReady event)
    (foreign : (graph setup).actor? event ≠ some who) :
    permittedSilence setup leaks bounds rosters who past view =
      (application setup leaks).silentPolicy past view := by
  classical
  obtain ⟨offered, member⟩ := (sourceServiceMenu setup leaks bounds rosters).nonempty who past view
  have silent : (⟨none⟩ : (application setup leaks).Action) ∈
      (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
    rw [← sourceServiceMenu_foreign_silent setup leaks bounds rosters who past view event sole
      foreign offered member]
    exact member
  unfold permittedSilence
  rw [ite_eq_left silent]

omit [Fintype Player] in
/-- Two profiles that agree at every input of a phase's sole ready event run
the event's complete service phase identically. -/
theorem rosterBlock_players_congr (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (first second : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event)
    (agree : ∀ actor past (view : (application setup leaks).PlayerView),
      view.application.publicView.SoleReady event →
        first actor past view = second actor past view) :
    (runtime setup).runInteractionPlan leaks first network (rosterBlock setup rosters event)
        execution =
      (runtime setup).runInteractionPlan leaks second network (rosterBlock setup rosters event)
        execution := by
  have visits : ∀ (roster : List Player) (current : (application setup leaks).Execution),
      current.application.publicView.SoleReady event →
        (runtime setup).runInteractionPlan leaks first network
            (roster.map ServiceInstruction.player) current =
          (runtime setup).runInteractionPlan leaks second network
            (roster.map ServiceInstruction.player) current := by
    intro roster
    induction roster with
    | nil => intro _ _; rfl
    | cons actor rest ih =>
        intro current currentSole
        simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
          PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
          ReactiveApplication.resume, ReactiveApplication.invoke,
          ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
          Function.comp_def]
        apply bind_congr_on_support _
        intro sample _
        let activated := current.sampledActivation (application setup leaks) actor sample
        have activatedSole : (activated.observe (application setup leaks)
            actor).application.publicView.SoleReady event := currentSole
        change (first actor (activated.recall actor)
          (activated.observe (application setup leaks) actor)).bind _ =
          (second actor (activated.recall actor)
            (activated.observe (application setup leaks) actor)).bind _
        rw [agree actor _ _ activatedSole]
        apply bind_congr_on_support _
        intro response _
        apply ih
        have unchanged := (runtime setup).reactive_respond_application leaks activated actor
          response
        rw [unchanged.2]
        exact currentSole
  rw [rosterBlock_eq_ending, runInteractionPlan_append, runInteractionPlan_append,
    visits _ execution sole]
  apply bind_congr_on_support _
  intro current _
  apply servicePlan_players_eq setup leaks first second network
  · unfold rosterPhaseEnding
    split <;> simp
  · intro player
    unfold rosterPhaseEnding
    split <;> simp

/-- **A phase the deviator does not own** runs exactly as under the timed
calendar profile. -/
theorem deviation_foreign_block (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters) (profile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    (lawful : ∀ past view response, response ∈ (deviation past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId)
    (foreign : (graph setup).actor? event ≠ some who)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event) :
    (runtime setup).runInteractionPlan leaks
        (Function.update (sourceServiceTimedPolicy setup leaks rosters timing profile) who
          deviation) network (rosterBlock setup rosters event) execution =
      (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing profile) network
        (rosterBlock setup rosters event) execution := by
  apply rosterBlock_players_congr setup leaks rosters _ _ network event execution sole
  intro actor past view viewSole
  by_cases same : actor = who
  · subst actor
    rw [Function.update_self, permitted_foreign_silent setup leaks bounds rosters who deviation
      lawful past view event viewSole foreign,
      sourceServiceTimedPolicy_idle setup leaks rosters timing profile who past view
        (viewSole.idle foreign)]
  · rw [Function.update_of_ne same]

/-- **The deviator's own phase**: every other player is silent, so the phase
runs as the deviator alone against silence. -/
theorem deviation_owned_block (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters) (profile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event) :
    (runtime setup).runInteractionPlan leaks
        (Function.update (sourceServiceTimedPolicy setup leaks rosters timing profile) who
          deviation) network (rosterBlock setup rosters event) execution =
      (runtime setup).runInteractionPlan leaks
        (Function.update (fun _ => (application setup leaks).silentPolicy) who deviation) network
        (rosterBlock setup rosters event) execution ∧
    (runtime setup).runInteractionPlan leaks
        (Function.update (sourceServiceTimedPolicy setup leaks rosters timing profile) who
          deviation) network (rosterBlock setup rosters event) execution =
      (runtime setup).runInteractionPlan leaks
        (Function.update (permittedSilence setup leaks bounds rosters) who deviation) network
        (rosterBlock setup rosters event) execution := by
  have foreign (actor : Player) (other : actor ≠ who) :
      (graph setup).actor? event ≠ some actor := by
    intro acts
    exact other (Option.some.inj (acts.symm.trans owned))
  constructor
  · apply rosterBlock_players_congr setup leaks rosters _ _ network event execution sole
    intro actor past view viewSole
    by_cases same : actor = who
    · subst actor
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne same, Function.update_of_ne same,
        sourceServiceTimedPolicy_idle setup leaks rosters timing profile actor past view
          (viewSole.idle (foreign actor same))]
  · apply rosterBlock_players_congr setup leaks rosters _ _ network event execution sole
    intro actor past view viewSole
    by_cases same : actor = who
    · subst actor
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne same, Function.update_of_ne same,
        sourceServiceTimedPolicy_idle setup leaks rosters timing profile actor past view
          (viewSole.idle (foreign actor same)),
        permittedSilence_foreign setup leaks bounds rosters actor past view event viewSole
          (foreign actor same)]

end Vegas
