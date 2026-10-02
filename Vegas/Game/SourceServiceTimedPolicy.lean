/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRosterPolicy
import Vegas.Game.RevealServiceRosterTiming
import Vegas.Game.RevealServiceRosterLaw
import Vegas.Pending.ReactivePolicyMixture
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ScheduledOpening

/-! # Shared timing of full-source decisions

One ordinary behavioral policy realizes a common timing lottery at each
source event. The source decision is drawn at the selected owner visit.
All other visits retain the real replay policy. Every family checks actual
own recall before emitting, including at off-path inputs of the mixture.
The latent slot is proof data of behavioral realization, not runtime state.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The existing source decision with silent choices realized by the full
replay law. Recorded prior emissions stop every timing branch. -/
def sourceServiceOpportunity
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId) :
    (application setup leaks).Policy := fun past view =>
  if (runtime setup).eventRecorded leaks past event then
    (application setup leaks).silentPolicy past view
  else (sourceServicePolicy setup leaks profile who past view).bind fun response =>
    if response.transmission = none then (application setup leaks).silentPolicy past view
    else PMF.pure response

def sourceServiceTimedFamily
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (slot : Fin ((rosters event).count who)) : (application setup leaks).Policy :=
  (application setup leaks).scheduledPolicy (rosterOffset setup rosters who event) (some slot)
    (sourceServiceOpportunity setup leaks profile who event)
    (application setup leaks).silentPolicy

def sourceServiceTimedPolicy
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (application setup leaks).silentPolicy past view
  | some event =>
      if owned : (graph setup).actor? event = some who then
        ((application setup leaks).policyMixture (timing event who owned)
          (sourceServiceTimedFamily setup leaks rosters profile who event)).policy past view
      else (application setup leaks).silentPolicy past view

/-- At its own turn a player follows the event's timing mixture. -/
theorem sourceServiceTimedPolicy_turn
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (serving : view.application.publicView.ownTurn? who = some event) :
    sourceServiceTimedPolicy setup leaks rosters timing profile who past view =
      ((application setup leaks).policyMixture (timing event who owned)
        (sourceServiceTimedFamily setup leaks rosters profile who event)).policy past view := by
  simp only [sourceServiceTimedPolicy, serving, owned, ↓reduceDIte]

/-- A player owning no ready event replays. -/
theorem sourceServiceTimedPolicy_idle
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (idle : view.application.publicView.Idle who) :
    sourceServiceTimedPolicy setup leaks rosters timing profile who past view =
      (application setup leaks).silentPolicy past view := by
  simp only [sourceServiceTimedPolicy, PublicView.ownTurn?_eq_none _ who idle]

/-- Every recorded opening or binding prevents a second fresh response,
even when the current input has zero probability under a timing family. -/
theorem sourceServiceTimedPolicy_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (serving : view.application.publicView.ownTurn? who = some event)
    (recorded : (runtime setup).eventRecorded leaks past event = true) :
    sourceServiceTimedPolicy setup leaks rosters timing profile who past view =
      (application setup leaks).silentPolicy past view := by
  simp only [sourceServiceTimedPolicy, serving]
  split
  · rw [ReactiveApplication.policyMixture_policy]
    have same : ∀ slot : Fin ((rosters event).count who),
        sourceServiceTimedFamily setup leaks rosters profile who event slot past view =
          (application setup leaks).silentPolicy past view := by
      intro slot
      simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
        sourceServiceOpportunity, recorded, ↓reduceIte, ite_self]
    simp only [same, PMF.bind_const]
  · rfl

/-- The phase's behavioral timing mixture equals the actual finite mixture
of scheduled executions. All passive samples and private native recall remain
in the law. The source decision kernel itself is not replaced by a premise. -/
theorem sourceServiceTimedFamily_execution
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (timing : PMF (Fin ((rosters event).count who)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (plan : List (ServiceInstruction (graph setup)))
    (execution : (application setup leaks).Execution)
    (before : (execution.recall who).length ≤ rosterOffset setup rosters who event) :
    (runtime setup).runInteractionPlan leaks
      (Function.update players who ((application setup leaks).policyMixture timing
        (sourceServiceTimedFamily setup leaks rosters profile who event)).policy)
      network plan execution = timing.bind fun slot =>
        (runtime setup).runInteractionPlan leaks
          (Function.update players who
            (sourceServiceTimedFamily setup leaks rosters profile who event slot))
          network plan execution := by
  let app := application setup leaks
  let family := sourceServiceTimedFamily setup leaks rosters profile who event
  have dormant := app.policyMixture_posterior_dormant timing family app.silentPolicy
    (rosterOffset setup rosters who event)
    (fun slot past view earlier => app.scheduledPolicy_before _ _ _ _ past view earlier)
    (execution.recall who) before
  have actual := (runtime setup).runInteractionPlan_policyMixture leaks timing family who
    players network plan execution
  dsimp only at actual
  rw [dormant] at actual
  exact actual.symm

theorem sourceServiceTimedPolicy_window_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event) :
    (runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (visits.map ServiceInstruction.player) execution =
      (runtime setup).runInteractionPlan leaks
        (Function.update (fun _ => (application setup leaks).silentPolicy) owner
          ((application setup leaks).policyMixture (timing event owner owned)
            (sourceServiceTimedFamily setup leaks rosters profile owner event)).policy)
        network (visits.map ServiceInstruction.player) execution := by
  classical
  let app := application setup leaks
  induction visits generalizing execution with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
        Function.comp_def]
      apply bind_congr_on_support _
      intro sample _
      let activated := execution.sampledActivation app actor sample
      have currentSole : (activated.observe app actor).application.publicView.SoleReady
          event := sole
      have law : sourceServiceTimedPolicy setup leaks rosters timing profile actor
          (activated.recall actor) (activated.observe app actor) =
          (Function.update (fun _ => app.silentPolicy) owner
            (app.policyMixture (timing event owner owned)
              (sourceServiceTimedFamily setup leaks rosters profile owner event)).policy) actor
            (activated.recall actor) (activated.observe app actor) := by
        by_cases same : actor = owner
        · subst actor
          have serving := PublicView.ownTurn?_of_ownTurn _ owner event (currentSole.ownTurn owned)
          simp only [sourceServiceTimedPolicy, serving]
          rw [dite_eq_left owned, Function.update_self]
        · have foreign : (graph setup).actor? event ≠ some actor := by
            intro acts
            exact same (Option.some.inj (acts.symm.trans owned))
          simp only [sourceServiceTimedPolicy, currentSole.ownTurn?_foreign foreign]
          rw [Function.update_of_ne same]
      change (sourceServiceTimedPolicy setup leaks rosters timing profile actor
        (activated.recall actor) (activated.observe app actor)).bind _ = _
      rw [law]
      apply bind_congr_on_support _
      intro response _
      apply ih
      have unchanged := (runtime setup).reactive_respond_application leaks activated actor response
      rw [unchanged.2]
      exact sole

/-- One shared timing lottery disintegrates the actual global source policy
through the complete current roster and deadline service. -/
theorem sourceServiceTimedPolicy_phase_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event)
    (before : (execution.recall owner).length ≤ rosterOffset setup rosters owner event) :
    let phase := (rosters event).map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    (runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network phase execution =
      (timing event owner owned).bind fun slot =>
        (runtime setup).runInteractionPlan leaks
          (Function.update (fun _ => (application setup leaks).silentPolicy) owner
            (sourceServiceTimedFamily setup leaks rosters profile owner event slot))
          network phase execution := by
  intro phase
  let app := application setup leaks
  let mixed := Function.update (fun _ => app.silentPolicy) owner
    (app.policyMixture (timing event owner owned)
      (sourceServiceTimedFamily setup leaks rosters profile owner event)).policy
  trans (runtime setup).runInteractionPlan leaks mixed network phase execution
  · dsimp only [phase]
    rw [runInteractionPlan_append, runInteractionPlan_append,
      sourceServiceTimedPolicy_window_eq setup leaks rosters timing profile event owner owned
        network (rosters event) execution sole]
    apply bind_congr_on_support _
    intro current _
    exact servicePlan_players_eq setup leaks _ _ network _ (by simp) (by intro who; simp) current
  · exact sourceServiceTimedFamily_execution setup leaks rosters profile owner event
      (timing event owner owned) (fun _ => app.silentPolicy) network phase execution before

/-- The actual continuation from an active owner decision is the posterior
mixture of scheduled continuations, retaining the already sampled input. -/
theorem sourceServiceTimedPolicy_active_phase_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (network : (runtime setup).NetworkPolicy leaks) (remaining : List Player) (ticks : Nat)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event) :
    let app := application setup leaks
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let family := sourceServiceTimedFamily setup leaks rosters profile owner event
    let phase := remaining.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    (app.invoke players owner execution).bind
      ((runtime setup).runInteractionPlan leaks players network phase) =
      ((app.policyMixture (timing event owner owned) family).posterior
        (execution.recall owner)).bind fun slot =>
          let scheduled := Function.update (fun _ => app.silentPolicy) owner (family slot)
          (app.invoke scheduled owner execution).bind
            ((runtime setup).runInteractionPlan leaks scheduled network phase) := by
  intro app players family phase
  let mixture := app.policyMixture (timing event owner owned) family
  let mixed := Function.update (fun _ => app.silentPolicy) owner mixture.policy
  trans (app.invoke mixed owner execution).bind
    ((runtime setup).runInteractionPlan leaks mixed network phase)
  · simp only [ReactiveApplication.invoke, PMF.bind_map, Function.comp_def]
    have responseLaw : players owner (execution.recall owner) (execution.observe app owner) =
        mixed owner (execution.recall owner) (execution.observe app owner) := by
      simp only [players, sourceServiceTimedPolicy, mixed, Function.update_self]
      have serving : (execution.observe app owner).application.publicView.ownTurn? owner =
          some event := PublicView.ownTurn?_of_ownTurn _ owner event (sole.ownTurn owned)
      simp only [serving, dite_eq_left owned]
      rfl
    rw [responseLaw]
    apply bind_congr_on_support _
    intro response _
    have currentSole : (execution.respond app owner response).application.publicView.SoleReady
        event := by
      rw [((runtime setup).reactive_respond_application leaks execution owner response).2]
      exact sole
    dsimp only [phase, Function.comp_apply]
    rw [runInteractionPlan_append, runInteractionPlan_append,
      sourceServiceTimedPolicy_window_eq setup leaks rosters timing profile event owner owned
        network remaining _ currentSole]
    apply bind_congr_on_support _
    intro current _
    exact servicePlan_players_eq setup leaks _ _ network _ (by simp) (by intro who; simp) current
  · exact ((runtime setup).invoke_runInteractionPlan_policyMixture leaks
      (timing event owner owned) family owner (fun _ => app.silentPolicy) network phase
      execution).symm

/-- A pure final timing slot is the checked limiting source compiler at
every input, including native inputs that are unreachable in its own law. -/
theorem sourceServiceTimedPolicy_final
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (coverage : ActorOpportunities setup rosters)
    (profile : BehavioralProfile setup.program) :
    sourceServiceTimedPolicy setup leaks rosters
      (fun event who owned => PMF.pure (rosterLastSlot setup rosters coverage event who owned))
      profile = sourceServiceLastPolicy setup leaks rosters profile := by
  funext who past view
  unfold sourceServiceTimedPolicy sourceServiceLastPolicy
  cases serving : view.application.publicView.ownTurn? who with
  | none => rfl
  | some event =>
      simp only
      by_cases owned : (graph setup).actor? event = some who
      · rw [dite_eq_left owned]
        let app := application setup leaks
        let slot := rosterLastSlot setup rosters coverage event who owned
        let family := sourceServiceTimedFamily setup leaks rosters profile who event
        have fixed := app.policyMixture_posterior_pure_append (PMF.pure slot) family []
          past slot rfl
        simp only [List.nil_append] at fixed
        rw [app.policyMixture_policy, fixed, PMF.pure_bind]
        have last := rosterLastSlot_final setup rosters coverage event who owned
        change slot.val + 1 = _ at last
        simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
          Option.map_some, Option.some.injEq, sourceServiceOpportunity, owned, true_and]
        have selected : rosterOffset setup rosters who event + slot.val = past.length ↔
            past.length + 1 = rosterOffset setup rosters who event +
              (rosters event).count who := by omega
        simp only [selected]
        cases recorded : (runtime setup).eventRecorded leaks past event <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false, false_and, true_and,
            ite_self]
      · simp only [owned, false_and, ↓reduceIte, ↓reduceDIte]

end Vegas
