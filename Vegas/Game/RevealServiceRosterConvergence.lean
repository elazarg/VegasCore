/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterMixing
import Vegas.Game.RevealServiceRosterLimit

/-! # One common roster perturbation converges at every information site -/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_policy_converges
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (sequence : Nat → (setup.informationModel admission).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (source : Profile (setup.informationModel admission).behavioralSignature)
    (converges : ∀ who (site : (setup.informationModel admission).InformationSite who),
      PMFConvergesPointwise (fun n => (sequence n).strategy who site.1) (source who site.1))
    (timing : Nat → TimingLaw setup rosters)
    (timingFull : ∀ n event who owned, FullSupport (timing n event who owned))
    (timingConverges : ∀ event who owned, ∃ last : Fin ((rosters event).count who),
      last.val + 1 = (rosters event).count who ∧
      PMFConvergesPointwise (fun n => timing n event who owned) (PMF.pure last))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).protocol
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some control))
    (active : control.actor = some who) :
    PMFConvergesPointwise
      (fun n => rosterPolicy setup leaks rosters (timing n)
        (setup.decodeBehavioralProfile admission (sequence n).strategy) who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who))
      (rosterLimitPolicy setup leaks rosters (setup.decodeBehavioralProfile admission source) who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :=
    by
  let app := application setup leaks
  let extended := bounds.withInitialValues (initialLaw setup)
  let menu := rosterMenu setup leaks extended rosters
  obtain ⟨event, slot, granted, prior, sample, initial, state, selected, initialSupport,
      related, sourceSupport, grant, offset, serials, published, reached, activated,
      unchanged, _⟩ :=
    roster_decision_phase setup leaks extended rosters network reveals openable
      who control trace active
  have soleNow : (control.execution.observe app who).application.publicView.SoleReady event := by
    change control.execution.application.publicView.SoleReady event
    rw [unchanged]
    exact soleReady_of_ready setup granted.application grant
  by_cases ownedEvent : (graph setup).actor? event = some who
  · obtain ⟨site, siteView, _, candidate, raw, opening, owned, valid, _, _⟩ :=
      roster_owner_choice_data setup leaks bounds reveals admission source who event ownedEvent
        initial initialSupport state granted related sourceSupport
    have law (profile : Profile (setup.informationModel admission).behavioralSignature) :
        sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission profile) who
          (granted.observe app who) =
        (profile who site.1).map (fun choice => OwnAction.disclosure choice.1) := by
      obtain ⟨otherSite, otherView, otherLaw, _⟩ := roster_owner_choice_data setup leaks bounds
        reveals admission profile who event ownedEvent initial initialSupport state granted
          related sourceSupport
      rw [otherView] at otherLaw
      rw [siteView]
      exact otherLaw
    have full (n : Nat) : FullSupport (sourceChoiceLaw setup leaks
        (setup.decodeBehavioralProfile admission (sequence n).strategy) who
        (granted.observe app who)) := by
      rw [law]
      exact setup.reveal_choice_fullSupport reveals admission (sequence n) (mixed n) who site
    have choiceConverges : PMFConvergesPointwise
        (fun n => sourceChoiceLaw setup leaks
          (setup.decodeBehavioralProfile admission (sequence n).strategy) who
          (granted.observe app who))
        (sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission source) who
          (granted.observe app who)) := by
      simp only [law]
      exact (converges who site).map (fun choice => OwnAction.disclosure choice.1)
    obtain ⟨last, final, timingLimit⟩ := timingConverges event who ownedEvent
    rw [activated]
    exact roster_owner_policy_limit setup leaks extended rosters granted event who
      (soleReady_of_ready setup granted.application grant) ownedEvent candidate raw opening owned
      valid (offset who) serials published menu.uniformResponses
      (fun player past view response supported =>
        (menu.uniformResponses_support player past view response).mp supported)
      network ((rosters event).take slot) (roster_count_before selected) prior reached sample
      (fun n => setup.decodeBehavioralProfile admission (sequence n).strategy)
      (setup.decodeBehavioralProfile admission source) full choiceConverges timing
      (fun n => timingFull n event who ownedEvent) last final timingLimit
  · have waiting (profile : BehavioralProfile setup.program)
        (when : TimingLaw setup rosters) :
        rosterPolicy setup leaks rosters when profile who (control.execution.recall who)
          (control.execution.observe app who) =
          app.replayPolicy (control.execution.recall who) (control.execution.observe app who) := by
      have idle := PublicView.ownTurn?_eq_none _ who (soleNow.idle ownedEvent)
      generalize input : control.execution.observe app who = view at idle ⊢
      unfold rosterPolicy
      rw [idle]
    have limitWaiting : rosterLimitPolicy setup leaks rosters
        (setup.decodeBehavioralProfile admission source) who (control.execution.recall who)
        (control.execution.observe app who) =
          app.replayPolicy (control.execution.recall who) (control.execution.observe app who) := by
      have idle := PublicView.ownTurn?_eq_none _ who (soleNow.idle ownedEvent)
      generalize input : control.execution.observe app who = view at idle ⊢
      unfold rosterLimitPolicy
      rw [idle]
    change PMFConvergesPointwise
      (fun n => rosterPolicy setup leaks rosters (timing n)
        (setup.decodeBehavioralProfile admission (sequence n).strategy) who
        (control.execution.recall who) (control.execution.observe app who))
      (rosterLimitPolicy setup leaks rosters (setup.decodeBehavioralProfile admission source) who
        (control.execution.recall who) (control.execution.observe app who))
    simp_rw [waiting, limitWaiting]
    exact pmfConvergesPointwise_const _

/-- A single source perturbation and timing sequence converges to the single
finite compiled profile at every native information site. -/
theorem rosterPerturbedProfile_converges
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (sequence : Nat → (setup.informationModel admission).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (source : Profile (setup.informationModel admission).behavioralSignature)
    (converges : ∀ who (site : (setup.informationModel admission).InformationSite who),
      PMFConvergesPointwise (fun n => (sequence n).strategy who site.1) (source who site.1))
    (timing : Nat → TimingLaw setup rosters)
    (timingFull : ∀ n event who owned, FullSupport (timing n event who owned))
    (timingConverges : ∀ event who owned, ∃ last : Fin ((rosters event).count who),
      last.val + 1 = (rosters event).count who ∧
      PMFConvergesPointwise (fun n => timing n event who owned) (PMF.pure last))
    (who : Player)
    (site : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationSite who) :
    PMFConvergesPointwise
      (fun n => rosterPerturbedProfile setup leaks bounds rosters network admission
        (sequence n) (timing n) who site.1)
      (rosterCompiledProfile setup leaks bounds rosters network
        (setup.decodeBehavioralProfile admission source) who site.1) := by
  classical
  let app := application setup leaks
  let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
  let scheduler := rosterScheduler setup leaks rosters network
  let horizon := (rosterPlan setup rosters).length
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active _ site history
  have observed := (menu.info (initialLaw setup) horizon scheduler who history.1.trace).symm.trans
    history.2
  cases stateEq : history.1.state with
  | none =>
      rw [stateEq] at active
      cases active
  | some control =>
      rw [stateEq] at active
      have acting : control.actor = some who := active
      have traced : (menu.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
        stateEq ▸ history.1.trace
      rw [stateEq] at observed
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who) else none) = site.1
        at observed
      rw [ite_eq_left acting] at observed
      rcases site with ⟨info, occurs⟩
      dsimp only at observed ⊢
      cases observed
      have physical := roster_policy_converges setup leaks bounds rosters network reveals openable
        admission sequence mixed source converges timing timingFull timingConverges
        who control traced acting
      have approxLaw (n : Nat) := menu.restrictPolicy_map_val (initialLaw setup) horizon scheduler
        who (rosterPolicy setup leaks rosters (timing n)
          (setup.decodeBehavioralProfile admission (sequence n).strategy) who)
        _ _ (rosterPolicy_admissible setup leaks bounds rosters network reveals openable admission
          (sequence n) (mixed n) (timing n) (timingFull n) who control traced acting)
      have limitLaw := menu.restrictPolicy_map_val (initialLaw setup) horizon scheduler who
        (rosterLimitPolicy setup leaks rosters (setup.decodeBehavioralProfile admission source) who)
        _ _ (rosterLimitPolicy_admissible setup leaks bounds rosters network reveals openable
          (setup.decodeBehavioralProfile admission source) who control traced acting)
      intro choice
      obtain ⟨action, _, chosen⟩ := choice.2
      have approxProb (n : Nat) :
          rosterPerturbedProfile setup leaks bounds rosters network admission
            (sequence n) (timing n) who
            (some (control.execution.recall who, control.execution.observe app who)) choice =
          rosterPolicy setup leaks rosters (timing n)
            (setup.decodeBehavioralProfile admission (sequence n).strategy) who
            (control.execution.recall who) (control.execution.observe app who) action := by
        refine (pmf_map_apply_of_injective _ Subtype.val_injective choice).symm.trans ?_
        refine (congrArg (fun law => law (Subtype.val choice)) (approxLaw n)).trans ?_
        rw [chosen]
        exact pmf_map_apply_of_injective _ (Option.some_injective _) _
      have limitProb :
          rosterCompiledProfile setup leaks bounds rosters network
            (setup.decodeBehavioralProfile admission source) who
            (some (control.execution.recall who, control.execution.observe app who)) choice =
          rosterLimitPolicy setup leaks rosters (setup.decodeBehavioralProfile admission source)
            who (control.execution.recall who) (control.execution.observe app who) action := by
        refine (pmf_map_apply_of_injective _ Subtype.val_injective choice).symm.trans ?_
        refine (congrArg (fun law => law (Subtype.val choice)) limitLaw).trans ?_
        rw [chosen]
        exact pmf_map_apply_of_injective _ (Option.some_injective _) _
      rw [limitProb]
      exact (physical action).congr fun n => (approxProb n).symm

end Vegas
