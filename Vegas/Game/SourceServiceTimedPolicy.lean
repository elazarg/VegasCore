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

namespace Vegas.SourceProgram.RevealService

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
    (application setup leaks).replayPolicy past view
  else (sourceServicePolicy setup leaks profile who past view).bind fun response =>
    if response.transmission = none then (application setup leaks).replayPolicy past view
    else FinDist.pure response

def sourceServiceTimedFamily
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (slot : Fin ((rosters event).count who)) : (application setup leaks).Policy :=
  (application setup leaks).scheduledPolicy (rosterOffset setup rosters who event) (some slot)
    (sourceServiceOpportunity setup leaks profile who event)
    (application setup leaks).replayPolicy

def sourceServiceTimedPolicy
    (setup : Setup (Player := Player) (L := L))
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
        ((application setup leaks).policyMixture (timing event who owned)
          (sourceServiceTimedFamily setup leaks rosters profile who event)).policy past view
      else (application setup leaks).replayPolicy past view

/-- Every recorded opening or binding prevents a second fresh response,
even when the current input has zero probability under a timing family. -/
theorem sourceServiceTimedPolicy_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (granted : view.application.publicView.serviceGrant = some event)
    (recorded : (runtime setup).eventRecorded leaks past event = true) :
    sourceServiceTimedPolicy setup leaks rosters timing profile who past view =
      (application setup leaks).replayPolicy past view := by
  simp only [sourceServiceTimedPolicy, granted]
  split
  · rw [ReactiveApplication.policyMixture_policy]
    have same : ∀ slot : Fin ((rosters event).count who),
        sourceServiceTimedFamily setup leaks rosters profile who event slot past view =
          (application setup leaks).replayPolicy past view := by
      intro slot
      simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
        sourceServiceOpportunity, recorded, ↓reduceIte, ite_self]
    simp only [same, FinDist.bind_const]
  · rfl

/-- The phase's behavioral timing mixture equals the actual finite mixture
of scheduled executions. All passive samples and private native recall remain
in the law. The source decision kernel itself is not replaced by a premise. -/
theorem sourceServiceTimedFamily_execution
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (timing : FinDist (Fin ((rosters event).count who)))
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
  have dormant := app.policyMixture_posterior_dormant timing family app.replayPolicy
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
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (execution : (application setup leaks).Execution)
    (granted : execution.application.serviceGrant = some event) :
    (runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (visits.map ServiceInstruction.player) execution =
      (runtime setup).runInteractionPlan leaks
        (Function.update (fun _ => (application setup leaks).replayPolicy) owner
          ((application setup leaks).policyMixture (timing event owner owned)
            (sourceServiceTimedFamily setup leaks rosters profile owner event)).policy)
        network (visits.map ServiceInstruction.player) execution := by
  classical
  let app := application setup leaks
  induction visits generalizing execution with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro sample _
      let activated := execution.sampledActivation app actor sample
      have currentGrant : (activated.observe app actor).application.publicView.serviceGrant =
          some event := granted
      have law : sourceServiceTimedPolicy setup leaks rosters timing profile actor
          (activated.recall actor) (activated.observe app actor) =
          (Function.update (fun _ => app.replayPolicy) owner
            (app.policyMixture (timing event owner owned)
              (sourceServiceTimedFamily setup leaks rosters profile owner event)).policy) actor
            (activated.recall actor) (activated.observe app actor) := by
        simp only [sourceServiceTimedPolicy, currentGrant]
        by_cases same : actor = owner
        · subst actor
          rw [dite_eq_left owned, Function.update_self]
        · have foreign : (graph setup).actor? event ≠ some actor := by
            intro acts
            exact same (Option.some.inj (acts.symm.trans owned))
          rw [dite_eq_right foreign, Function.update_of_ne same]
      change (sourceServiceTimedPolicy setup leaks rosters timing profile actor
        (activated.recall actor) (activated.observe app actor)).bind _ = _
      rw [law]
      apply FinDist.bind_congr
      intro response _
      apply ih
      have unchanged := (runtime setup).reactive_respond_application leaks activated actor response
      exact (congrArg PublicView.serviceGrant unchanged.2).trans granted

/-- One shared timing lottery disintegrates the actual global source policy
through the complete current roster and deadline service. -/
theorem sourceServiceTimedPolicy_phase_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat)
    (execution : (application setup leaks).Execution)
    (granted : execution.application.serviceGrant = some event)
    (before : (execution.recall owner).length ≤ rosterOffset setup rosters owner event) :
    let phase := (rosters event).map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    (runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network phase execution =
      (timing event owner owned).bind fun slot =>
        (runtime setup).runInteractionPlan leaks
          (Function.update (fun _ => (application setup leaks).replayPolicy) owner
            (sourceServiceTimedFamily setup leaks rosters profile owner event slot))
          network phase execution := by
  intro phase
  let app := application setup leaks
  let mixed := Function.update (fun _ => app.replayPolicy) owner
    (app.policyMixture (timing event owner owned)
      (sourceServiceTimedFamily setup leaks rosters profile owner event)).policy
  trans (runtime setup).runInteractionPlan leaks mixed network phase execution
  · dsimp only [phase]
    rw [runInteractionPlan_append, runInteractionPlan_append,
      sourceServiceTimedPolicy_window_eq setup leaks rosters timing profile event owner owned
        network (rosters event) execution granted]
    apply FinDist.bind_congr
    intro current _
    exact servicePlan_players_eq setup leaks _ _ network _ (by simp) (by intro who; simp) current
  · exact sourceServiceTimedFamily_execution setup leaks rosters profile owner event
      (timing event owner owned) (fun _ => app.replayPolicy) network phase execution before

/-- A pure final timing slot is the checked limiting source compiler at
every input, including native inputs that are unreachable in its own law. -/
theorem sourceServiceTimedPolicy_final
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (coverage : ∀ event owner, (graph setup).actor? event = some owner →
      owner ∈ rosters event)
    (profile : BehavioralProfile setup.program) :
    sourceServiceTimedPolicy setup leaks rosters
      (fun event who owned => FinDist.pure (rosterLastSlot setup rosters coverage event who owned))
      profile = sourceServiceLastPolicy setup leaks rosters profile := by
  funext who past view
  unfold sourceServiceTimedPolicy sourceServiceLastPolicy
  cases granted : view.application.publicView.serviceGrant with
  | none => rfl
  | some event =>
      simp only
      by_cases owned : (graph setup).actor? event = some who
      · rw [dite_eq_left owned]
        let app := application setup leaks
        let slot := rosterLastSlot setup rosters coverage event who owned
        let family := sourceServiceTimedFamily setup leaks rosters profile who event
        have fixed := app.policyMixture_posterior_pure_append (FinDist.pure slot) family []
          past slot rfl
        simp only [List.nil_append] at fixed
        rw [app.policyMixture_policy, fixed, FinDist.pure_bind]
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

end Vegas.SourceProgram.RevealService
