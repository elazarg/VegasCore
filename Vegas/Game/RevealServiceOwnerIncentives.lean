/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceMixing
import Vegas.Game.RevealServiceOwnerValue
import Vegas.Game.SourceLocalContinuation

/-! # Ordinary information-site incentives of the revelation compiler

At each actual native owner site, the compiled Boolean marginal is the
original source law. Physical replay aliases do not alter this marginal.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (admission : CommitmentInterface setup.program)

include reveals observer openable in
theorem owner_compiled_choice_law [setup.FiniteInitialLaw]
    (source : Profile (setup.informationModel admission).behavioralSignature)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (who : Player)
    (site : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationSite who)
    (reference : Profile
      (information setup leaks (bounds.withInitialValues (initialLaw setup))
        watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (history : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationHistory who site.1)
    (supported : history.1 ∈
      ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
        reference (blockOffset event.val + 2 * event.val + 3)).support)
    (sourceSite : (setup.informationModel admission).InformationSite who)
    (sourceView : sourceSite.1 =
      setup.protocolObserve who (prefixReadout setup leaks event.val history.1.state)) :
    (compiledProfile setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
      (setup.decodeBehavioralProfile admission source) weight nonnegative small who site.1).map
        (fun choice => sourceChoice setup leaks (choice.1.getD ⟨none⟩)) =
      (source who sourceSite.1).map (fun choice => OwnAction.disclosure choice.1) := by
  let extended := bounds.withInitialValues (initialLaw setup)
  let decoded := setup.decodeBehavioralProfile admission source
  have ordinary : who ≠ watcher := fun same => observer event (same ▸ owned)
  obtain ⟨past, view, info⟩ : ∃ past view, site.1 = some (past, view) := by
    cases observed : site.1 with
    | none =>
        obtain ⟨_, _, response, member⟩ := site.2
        rw [observed] at member
        cases member
    | some input => exact ⟨input.1, input.2, rfl⟩
  obtain ⟨sourceLaw, opening, selected, covered⟩ := owner_choice_data setup leaks bounds watcher who
    reveals observer openable admission source reference event owned history.1 supported past view
      (history.2.trans info)
  rw [← sourceView] at sourceLaw
  have physical := compiledProfile_map_val setup leaks extended watcher decoded weight nonnegative
    small who past view
  have projected := congrArg (fun distribution => distribution.map
    (fun response => sourceChoice setup leaks (response.getD ⟨none⟩))) physical
  simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at projected
  rw [policy, ite_eq_right ordinary,
    ordinaryPolicy_projects setup leaks extended decoded weight nonnegative small
      who past view opening selected covered, sourceLaw] at projected
  rw [info]
  exact projected

omit [Fintype Player] in
private theorem source_site_nonterminal (who : Player)
    (site : (setup.informationModel admission).InformationSite who) : site.AllNonterminal := by
  obtain ⟨witness, running, _action⟩ := site.2
  intro current stopped
  change current.1.state.elim False (ProtocolState.terminal setup.program) at stopped
  have zero : setup.protocolRemaining current.1.state = 0 := by
    cases same : current.1.state with
    | none => rw [same] at stopped; exact stopped.elim
    | some state =>
        rw [same] at stopped
        exact (ProtocolState.remaining_zero_iff_terminal setup.program state).mpr stopped
  have counted := setup.protocol_history_length admission current.1.trace
  have depths := (setup.common_decision_depth admission who site current).trans
    (setup.common_decision_depth admission who site witness).symm
  exact running (setup.protocol_bounded admission witness.1.state witness.1.trace (by omega))

include reveals observer openable in
open Classical in
/-- Matching Boolean laws at one native and source site gives matching actual
continuation values. The source state posterior and unchanged baseline source
continuation supply everything needed after the immediate action. -/
theorem owner_context_eq_source_local [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (source : (setup.informationModel admission).BehavioralAssessment)
    (target : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).BehavioralAssessment)
    (strategy : target.strategy = compiledProfile setup leaks
      (bounds.withInitialValues (initialLaw setup)) watcher
      (setup.decodeBehavioralProfile admission source.strategy) 0 le_rfl (by norm_num))
    (who : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (site : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationSite who)
    (clock : InformationModel.InformationSite.CommonDepth
      (information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher) site
        (blockOffset event.val + 2 * event.val + 3))
    (sourceSite : (setup.informationModel admission).InformationSite who)
    (belief : (target.belief who site).map
        (fun current => prefixReadout setup leaks event.val current.1.state) =
      source.stateBelief who sourceSite)
    (law : PMF ((information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).Choice who site.1))
    (sourceLaw : PMF ((setup.informationModel admission).Choice who sourceSite.1))
    (choices : law.map (fun choice => sourceChoice setup leaks (choice.1.getD ⟨none⟩)) =
      sourceLaw.map (fun choice => OwnAction.disclosure choice.1))
    (utility : State L setup.program.terminalCtx → ℝ) :
    (target.continuationContext site
      (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
      (2 * horizon setup watcher + 1 - (blockOffset event.val + 2 * event.val + 3))).value
        ((target.strategy who).withLaw site.1 law) =
      (source.continuationContext sourceSite
        (fun final => (setup.protocolReadout final.state).elim 0 utility)
        (instructionCount setup.program + 1)).value
          ((source.strategy who).withLaw sourceSite.1 sourceLaw) := by
  classical
  have := setup.reveal_finite_history reveals admission
  have sectionExists (disclose : Bool) :
      ∃ choice : (setup.informationModel admission).Choice who sourceSite.1,
        OwnAction.disclosure choice.1 = disclose := by
    have present := setup.reveal_choice_fullSupport reveals admission
      (setup.revealReference reveals admission) (setup.revealReference_fullyMixed reveals admission)
      who sourceSite disclose
    obtain ⟨choice, _supported, same⟩ := PMF.support_map .. ▸ present
    exact ⟨choice, same⟩
  choose represent representativeLaw using sectionExists
  let joint (disclose : Bool) (actor : Player) :=
    if actor = who then (represent disclose).1 else none
  have chosen (disclose : Bool) : OwnAction.disclosure (joint disclose who) = disclose := by
    simpa only [joint, ite_eq_left rfl] using representativeLaw disclose
  have enough (history : (setup.informationModel admission).InformationHistory who sourceSite.1) :
      setup.protocolRemaining history.1.state ≤ instructionCount setup.program + 1 := by
    have count := setup.protocol_history_length admission history.1.trace
    omega
  rw [owner_context_local_value setup leaks bounds watcher who reveals observer openable
    (setup.decodeBehavioralProfile admission source.strategy) target strategy event owned site
      clock law joint chosen utility, belief,
    setup.continuationContext_local_value_stateBelief admission source who sourceSite
      (source_site_nonterminal setup admission who sourceSite) sourceLaw utility
      (instructionCount setup.program) enough]
  simp only [InformationModel.BehavioralAssessment.stateBelief, expect_map, Function.comp_def]
  apply expect_congr_on_support
  intro history _supported
  have projected := congrArg (fun distribution => expect distribution (fun disclose =>
    expect ((setup.protocolStep history.1.state (joint disclose)).bind
      (setup.continuationLaw
        (setup.decodeBehavioralProfile admission source.strategy))) utility)) choices
  simp only [expect_map, Function.comp_def] at projected
  rw [projected]
  apply expect_congr_on_support
  intro choice _supported
  have sameStep : setup.protocolStep history.1.state (joint (OwnAction.disclosure choice.1)) =
      setup.protocolStep history.1.state (fun actor => if actor = who then choice.1 else none) := by
    have active := InformationModel.InformationSite.active _ sourceSite history
    cases state : history.1.state with
    | none => rfl
    | some current =>
        have actor : ProtocolView.actor who setup.program
            (ProtocolState.observe who setup.program current) = some who := by
          simpa only [Setup.executionProtocol, state, Setup.protocolObserve, Option.map_some,
            Option.elim_some] using active
        exact congrArg (fun distribution => distribution.map some)
          (ProtocolState.step_disclosure_congr who setup.program reveals current actor
            (joint (OwnAction.disclosure choice.1))
            (fun player => if player = who then choice.1 else none)
            (by simpa only [↓reduceIte] using chosen (OwnAction.disclosure choice.1)))
  rw [sameStep]

include reveals observer openable in
open Classical in
/-- Original source sequential rationality rules out every local native
response law, including mixtures over privately remembered replay aliases. -/
theorem owner_local_optimal [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (source : (setup.informationModel admission).BehavioralAssessment)
    (target : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).BehavioralAssessment)
    (strategy : target.strategy = compiledProfile setup leaks
      (bounds.withInitialValues (initialLaw setup)) watcher
      (setup.decodeBehavioralProfile admission source.strategy) 0 le_rfl (by norm_num))
    (who : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some who)
    (site : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationSite who)
    (clock : InformationModel.InformationSite.CommonDepth
      (information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher) site
        (blockOffset event.val + 2 * event.val + 3))
    (reference : Profile
      (information setup leaks (bounds.withInitialValues (initialLaw setup))
        watcher).behavioralSignature)
    (history : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationHistory who site.1)
    (supported : history.1 ∈
      ((information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).runBehavioral
        reference (blockOffset event.val + 2 * event.val + 3)).support)
    (sourceSite : (setup.informationModel admission).InformationSite who)
    (sourceView : sourceSite.1 =
      setup.protocolObserve who (prefixReadout setup leaks event.val history.1.state))
    (belief : (target.belief who site).map
        (fun current => prefixReadout setup leaks event.val current.1.state) =
      source.stateBelief who sourceSite)
    (utility : State L setup.program.terminalCtx → ℝ)
    (optimal : source.IsSequentiallyRationalAt sourceSite
      (source.continuationContext sourceSite
        (fun final => (setup.protocolReadout final.state).elim 0 utility)
          (instructionCount setup.program + 1)))
    (law : PMF ((information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).Choice who site.1)) :
    (target.continuationContext site
      (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
      (2 * horizon setup watcher + 1 - (blockOffset event.val + 2 * event.val + 3))).value
        ((target.strategy who).withLaw site.1 law) ≤
      (target.continuationContext site
        (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
        (2 * horizon setup watcher + 1 - (blockOffset event.val + 2 * event.val + 3))).value
          (target.strategy who) := by
  have represented (disclose : Bool) :
      ∃ choice : (setup.informationModel admission).Choice who sourceSite.1,
        OwnAction.disclosure choice.1 = disclose := by
    have present := setup.reveal_choice_fullSupport reveals admission
      (setup.revealReference reveals admission) (setup.revealReference_fullyMixed reveals admission)
      who sourceSite disclose
    obtain ⟨choice, _supported, same⟩ := PMF.support_map .. ▸ present
    exact ⟨choice, same⟩
  choose represent representativeLaw using represented
  let sourceLaw := law.map fun choice =>
    represent (sourceChoice setup leaks (choice.1.getD ⟨none⟩))
  have choices : law.map (fun choice => sourceChoice setup leaks (choice.1.getD ⟨none⟩)) =
      sourceLaw.map (fun choice => OwnAction.disclosure choice.1) := by
    simp only [sourceLaw, PMF.map_comp, Function.comp_def, representativeLaw]
  have changed := owner_context_eq_source_local setup leaks bounds watcher reveals observer
    openable admission source target strategy who event owned site clock sourceSite belief law
      sourceLaw choices utility
  have baselineChoices : (target.strategy who site.1).map
      (fun choice => sourceChoice setup leaks (choice.1.getD ⟨none⟩)) =
        (source.strategy who sourceSite.1).map (fun choice => OwnAction.disclosure choice.1) := by
    rw [strategy]
    exact owner_compiled_choice_law setup leaks bounds watcher reveals observer openable admission
      source.strategy 0 le_rfl (by norm_num) who site reference event owned history supported
      sourceSite sourceView
  have baseline := owner_context_eq_source_local setup leaks bounds watcher reveals observer
    openable admission source target strategy who event owned site clock sourceSite belief
      (target.strategy who site.1) (source.strategy who sourceSite.1) baselineChoices utility
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self,
    InformationModel.BehavioralPolicy.withLaw_eq_self] at baseline
  rw [changed, baseline]
  have := setup.reveal_finite_history reveals admission
  exact (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _) fun _ _ =>
      (payoffIntegrable_of_finite _ _)).mp optimal _ (Set.mem_univ _)

end Vegas
