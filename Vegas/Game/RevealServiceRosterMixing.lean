/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterDecisionData
import Vegas.Game.RevealServiceRosterEvidence
import Vegas.Game.RevealServiceMixing

/-! # Fully mixed source profiles cover every legal roster decision

The finite source profile determines the native response law at every retained
history, including histories with an earlier opening. Full support follows
from the original source choices and positive timing probabilities.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_owner_choice_data
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (reveals : setup.program.RevealOnly) (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (who : Player) (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (state : ProtocolState setup.program) (execution : (application setup leaks).Execution)
    (related : PublicPrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state execution)
    (supported : state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
      (fun owner => RevealOnly.uniformPolicy owner setup.program reveals)))^[event.val]
        (FinDist.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).support)
    (granted : execution.application.serviceGrant = some event) :
    ∃ site : (setup.informationModel admission).InformationSite who,
      site.1 = setup.protocolObserve who (some state) ∧
      sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission profile) who
          (execution.observe (application setup leaks) who) =
        (profile who site.1).map (fun choice => OwnAction.disclosure choice.1) ∧
      ∃ candidate raw,
        rosterOpening? setup leaks who event (execution.observe (application setup leaks) who) =
          some (candidate, raw) ∧ candidate.1 = who ∧
        execution.application.candidates.lookup candidate = .openable raw ∧
        (bounds.withInitialValues (initialLaw setup)).AllowsHandle candidate ∧
        raw ∈ (bounds.withInitialValues (initialLaw setup)).values := by
  let decoded := setup.decodeBehavioralProfile admission profile
  obtain ⟨site, siteView⟩ := roster_source_site setup leaks reveals admission who event owned
    initial initialSupport state execution related supported
  have data := owner_choices_at_prefix setup leaks bounds decoded who initial initialSupport
    setup.program reveals decoded (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program decoded)
    event.val event.isLt state execution related event (by omega) owned granted
  refine ⟨site, siteView, ?_, data.2.2⟩
  have encoded : setup.toProtocolBehavioralPolicy admission who (decoded who)
      (((setup.behavioralPolicyEquiv admission who).symm (profile who)).2) = profile who :=
    (setup.behavioralPolicyEquiv admission who).apply_symm_apply (profile who)
  have sourceLaw := setup.toProtocolBehavioralPolicy_map_val admission who (decoded who)
    (((setup.behavioralPolicyEquiv admission who).symm (profile who)).2)
    (some (ProtocolState.observe who setup.program state))
  rw [encoded] at sourceLaw
  simp only [Option.elim_some] at sourceLaw
  rw [siteView]
  have choiceLaw := data.1
  rw [← sourceLaw, FinDist.map_comp] at choiceLaw
  exact choiceLaw

/-- The physical response law has exactly the retained support at every legal
decision, not merely at histories reached by the compiled profile. -/
theorem roster_policy_support_exact
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, (timing event who owned).FullSupport)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).protocol
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some control))
    (active : control.actor = some who) (action : (application setup leaks).Action) :
    action ∈ (rosterPolicy setup leaks rosters timing
      (setup.decodeBehavioralProfile admission source.strategy) who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support ↔
    action ∈ rosterActions setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
      who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) :=
    by
  let app := application setup leaks
  let extended := bounds.withInitialValues (initialLaw setup)
  let menu := rosterMenu setup leaks extended rosters
  let decoded := setup.decodeBehavioralProfile admission source.strategy
  obtain ⟨event, slot, granted, prior, sample, initial, state, selected, initialSupport,
      related, sourceSupport, grant, offset, serials, published, reached, activated,
      unchanged, _⟩ :=
    roster_decision_phase setup leaks extended rosters network reveals openable
      who control trace active
  have grantNow : (control.execution.observe app who).application.publicView.serviceGrant =
      some event := by change control.execution.application.serviceGrant = _; rw [unchanged, grant]
  by_cases ownedEvent : (graph setup).actor? event = some who
  · obtain ⟨site, _, choiceLaw, candidate, raw, opening, owned, valid, handle, value⟩ :=
      roster_owner_choice_data setup leaks bounds reveals admission source.strategy who event
        ownedEvent initial initialSupport state granted related sourceSupport grant
    have full := rosterSelection_fullSupport _ (timing event who ownedEvent)
      (choiceLaw ▸ setup.reveal_choice_fullSupport reveals admission source mixed who site)
      (timingFull event who ownedEvent)
    have law := rosterPolicy_at_phase setup leaks rosters timing decoded granted control.execution
      event who grant ownedEvent candidate raw opening unchanged who
    simp only [EventGraphRuntime.openingWindowMixturePlayers, Function.update_self] at law
    rw [law, activated]
    have covered : ∀ player past view response,
        response ∈ (menu.uniformResponses player past view).support →
          response ∈ rosterActions setup leaks extended rosters player past view := by
      intro player past view response supported
      exact (menu.uniformResponses_support player past view response).mp supported
    refine ⟨?_, ?_⟩
    · intro supported
      refine roster_owner_coverage setup leaks extended rosters granted event who grant ownedEvent
        candidate raw opening owned valid (offset who) serials published menu.uniformResponses
        covered network ((rosters event).take slot) (roster_count_before selected)
        prior reached sample _ full (fun fresh => ?_) action supported
      have normal := roster_fresh_normal setup leaks extended rosters network reveals openable
        who control trace active ((runtime setup).windowOpening leaks event candidate raw)
        (by rw [activated]; exact fresh)
      apply (((runtime setup).reactiveNormalization leaks).menu_mem
        (extended.rawMenu (runtime setup) leaks) who _ _ _).mpr
      refine ⟨_, roster_opening_raw_available setup leaks extended event candidate raw handle value
        who _ _, ?_⟩
      rw [activated] at normal
      exact normal
    · intro member
      exact roster_owner_fullSupport setup leaks extended rosters granted event who grant ownedEvent
        candidate raw opening owned valid (offset who) serials published menu.uniformResponses
        covered network ((rosters event).take slot) (roster_count_before selected)
        prior reached sample _ full action member
  · have waiting : rosterPolicy setup leaks rosters timing decoded who
        (control.execution.recall who) (control.execution.observe app who) =
          app.replayPolicy (control.execution.recall who) (control.execution.observe app who) := by
      simp only [rosterPolicy, grantNow, dite_eq_right ownedEvent]
      rfl
    rw [waiting]
    refine ⟨replay_roster setup leaks extended rosters who _ _ action, ?_⟩
    intro member
    rcases roster_response_cases setup leaks extended rosters who _ _ action member with
      replay | fresh
    · exact replay
    · have absent : rosterFresh? setup leaks rosters who (control.execution.recall who)
          (control.execution.observe app who) = none := by
        unfold rosterFresh?
        rw [grantNow]
        dsimp only [Option.bind]
        exact ite_eq_left ownedEvent
      rw [absent] at fresh
      cases fresh

/-- Every fresh response at a legal decision fits the effective finite menu,
using the initialized commitment values and actual certificate provenance. -/
theorem roster_fresh_available
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).protocol
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some control))
    (active : control.actor = some who) (action : (application setup leaks).Action)
    (fresh : rosterFresh? setup leaks rosters who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = some action) :
    action ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
      who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) :=
    by
  let extended := bounds.withInitialValues (initialLaw setup)
  let profile : BehavioralProfile setup.program :=
    fun player => RevealOnly.uniformPolicy player setup.program reveals
  obtain ⟨event, _, granted, _, _, initial, state, _, initialSupport,
      related, _, grant, _, _, _, _, _, unchanged, _⟩ :=
    roster_decision_phase setup leaks extended rosters network reveals openable
      who control trace active
  obtain ⟨sentEvent, candidate, raw, sentGrant, owned, sentOpening, rfl, _⟩ :=
    rosterFresh?_shape setup leaks rosters who _ _ action fresh
  change control.execution.application.serviceGrant = some sentEvent at sentGrant
  rw [unchanged, grant] at sentGrant
  cases Option.some.inj sentGrant
  have data := owner_choices_at_prefix setup leaks bounds profile who initial initialSupport
    setup.program reveals profile (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt state granted related event (by omega) owned grant
  obtain ⟨expected, expectedRaw, opening, _, _, handle, value⟩ := data.2.2
  have same := rosterOpening?_application_eq setup leaks who event control.execution granted
    unchanged
  rw [sentOpening, opening] at same
  cases Option.some.inj same
  apply (((runtime setup).reactiveNormalization leaks).menu_mem
    (extended.rawMenu (runtime setup) leaks) who _ _ _).mpr
  exact ⟨_, roster_opening_raw_available setup leaks extended event candidate raw handle value
    who _ _, roster_fresh_normal setup leaks extended rosters network reveals openable
      who control trace active _ fresh⟩

section Compilation

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)
  (reveals : setup.program.RevealOnly)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

include reveals openable in
theorem rosterLimitPolicy_admissible (profile : BehavioralProfile setup.program) (who : Player) :
    (rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (rosterLimitPolicy setup leaks rosters profile who) := by
  classical
  intro control trace active action supported
  rcases rosterLimitPolicy_cases setup leaks rosters profile who _ _ action supported with
    replay | fresh
  · exact replay_roster setup leaks _ rosters who _ _ action replay
  · apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_union_right _ ?_, ?_⟩
    · rw [fresh]
      simp
    · exact roster_fresh_available setup leaks bounds rosters network reveals openable
        who control trace active action fresh

/-- The prescribed finite profile waits until the final owner visit and
stops after every earlier opening, including zero-probability histories. -/
def rosterCompiledProfile (profile : BehavioralProfile setup.program) :
    Profile ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).behavioralSignature := fun who =>
  (rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters).restrictPolicy
    (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who
    (rosterLimitPolicy setup leaks rosters profile who)

end Compilation

section Perturbation

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)
  (reveals : setup.program.RevealOnly)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (admission : CommitmentInterface setup.program)
  (source : (setup.informationModel admission).BehavioralAssessment)
  (mixed : source.IsFullyMixed)
  (timing : TimingLaw setup rosters)
  (timingFull : ∀ event who owned, (timing event who owned).FullSupport)

include reveals openable mixed timingFull in
theorem rosterPolicy_admissible (who : Player) :
    (rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (rosterPolicy setup leaks rosters timing
        (setup.decodeBehavioralProfile admission source.strategy) who) := by
  intro control trace active action supported
  exact (roster_policy_support_exact setup leaks bounds rosters network reveals openable admission
    source mixed timing timingFull who control trace active action).mp supported

/-- A finite native perturbation with the original source choices and strictly
positive disclosure timing. Restriction preserves its physical response law
at every legal history. -/
def rosterPerturbedProfile :
    Profile ((rosterMenu setup leaks
      (bounds.withInitialValues (initialLaw setup)) rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).behavioralSignature := fun who =>
  (rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters).restrictPolicy
    (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who
    (rosterPolicy setup leaks rosters timing
      (setup.decodeBehavioralProfile admission source.strategy) who)

include reveals openable mixed timingFull in
theorem rosterPerturbedProfile_fullyMixed :
    (InformationModel.BehavioralAssessment.ofStrategy
      (rosterPerturbedProfile setup leaks bounds rosters network admission
        source timing)).IsFullyMixed := by
  exact ReactiveApplication.ResponseMenu.restrictProfile_fullSupport
      (rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters)
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
      (rosterPolicy setup leaks rosters timing
        (setup.decodeBehavioralProfile admission source.strategy))
      (rosterPolicy_admissible setup leaks bounds rosters network reveals openable admission
        source mixed timing timingFull)
      (fun who control trace active action member =>
        (roster_policy_support_exact setup leaks bounds rosters network reveals openable admission
          source mixed timing timingFull who control trace active action).mpr member)

end Perturbation

end Vegas.SourceProgram.RevealService
