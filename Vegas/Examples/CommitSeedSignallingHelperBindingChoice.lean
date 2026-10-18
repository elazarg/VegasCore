/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperSafeContext
import Vegas.Examples.CommitSeedSignallingHelperBindingWait
import Vegas.Examples.CommitSeedSignallingHelperFailedPreparationValue

/-! # Actual supported declarations at the seed-eligible helper input -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Restricting the assessed raw strategy preserves its exact response law
at every genuine counted source, including a source of zero assessed reach. -/
theorem counted_assessment_response_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (who : Player) (current : source.state = some ⟨remaining, some who, execution⟩) :
    countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
      who (execution.recall who) (execution.observe app who) =
    rawMenu.decodeProfile initial horizon scheduler assessment.strategy who
      (execution.recall who) (execution.observe app who) := by
  classical
  have running : ¬ countedProtocol.terminal source.state := by
    rw [current]
    intro stopped
    cases stopped.2
  have active : countedProtocol.active source.state who := by rw [current]; rfl
  obtain ⟨site, observed⟩ := countedModel.exists_informationSite_of_active who source running active
  have atInput : site.1 = some (execution.recall who, execution.observe app who) := by
    rw [observed]
    change (countedMenu.signals initial horizon scheduler).infoOf who source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  have covered (response : app.Action)
      (chosen : response ∈ (players who (execution.recall who)
        (execution.observe app who)).support) :
      response ∈ countedMenu.actions who (execution.recall who) (execution.observe app who) :=
    raw_equilibrium_counted_site_covered assessment equilibrium who site (execution.recall who)
      (execution.observe app who) atInput response chosen
  have embedded := countedMenu.embed_restrictPolicy initial horizon scheduler who (players who)
    (execution.recall who) (execution.observe app who) covered
  change ((countedMenu.embedPolicy initial horizon scheduler who
    (countedMenu.restrictPolicy initial horizon scheduler who (players who)))
      (some (execution.recall who, execution.observe app who))).map
        (fun selected => selected.1.getD ⟨none⟩) =
      players who (execution.recall who) (execution.observe app who)
  rw [embedded]
  simp only [ReactiveApplication.encodePolicy, PMF.map_comp, Function.comp_def, Option.getD_some]
  change (players who (execution.recall who) (execution.observe app who)).map id = _
  exact PMF.map_id _

open Classical in
/-- Sequential rationality transfers the actual nonnegative whole safe
continuation value to every incumbent-supported committed current choice. -/
theorem helper_eligible_supported_context_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool) (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : bit = true → helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1)
    (supported : choice ∈ (assessment.strategy alice site.1).support) :
    0 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
      ((assessment.strategy alice).commit site.1 choice) := by
  classical
  have safe := raw_helper_context_value_nonnegative assessment equilibrium source remaining
    execution current request bit clock quiet helper remembered helperRequest helperClock waited
      marker sender addressed visible readout site atSite
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler alice site)
  have integrable (policy : rawModel.BehavioralPolicy alice) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate site
      (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final) policy
  have better := assessment.supported_choice_optimal
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff alice)
    (equilibrium.1 alice site) (integrable (assessment.strategy alice)) choice supported
      (assessment.strategy alice) (integrable (assessment.strategy alice))
  exact safe.trans better

/-- Every supported response at a known eligible original helper input
really sends a counted binding with usable Bool preparation. Silence and
accepted unusable declarations are excluded on the full raw information fiber. -/
theorem helper_eligible_supported_choice_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool) (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : bit = true → helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1)
    (supported : choice ∈ (assessment.strategy alice site.1).support) :
    ∃ (material : WitnessedSubmission graph) (value : Bool),
      choice.1 = some ⟨some material⟩ ∧
      (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice (execution.recall alice)
        (execution.observe app alice) ∧
      (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  classical
  have lower := helper_eligible_supported_context_value_nonnegative assessment equilibrium source
    remaining execution current request bit clock quiet helper remembered helperRequest helperClock
      waited marker sender addressed visible readout site atSite choice supported
  have atInput : site.1 = some (execution.recall alice, execution.observe app alice) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf alice source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun value _ => PhaseCount.countClean_initial runtime leaks value) source.trace
  rw [current] at clean
  have own : OwnPermitted alice execution :=
    ⟨clean.1, fun message member _ => clean.2 message member⟩
  have pastClean := (ownPermitted_iff_past alice execution clean.1).mp own
  have available : choice.1 ∈ rawModel.menu alice
      (some (execution.recall alice, execution.observe app alice)) := by
    simpa only [atInput] using choice.2
  obtain ⟨response, _rawAllowed, selected⟩ := available
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have omitted := raw_helper_binding_wait_context_value assessment equilibrium source remaining
        execution current request bit clock quiet helper remembered helperRequest helperClock marker
          sender addressed visible readout site atSite choice selected
      rw [omitted] at lower
      norm_num at lower
  | some material =>
      have offered := clean_supported_response_counted assessment equilibrium alice site
        (execution.recall alice) (execution.observe app alice) atInput pastClean choice supported
          ⟨some material⟩ selected
      cases interpretation : material.call.opening.bind (fun raw => raw.as? BaseTy.bool) with
      | none =>
          have failed := raw_failed_helper_binding_context_value assessment equilibrium source
            remaining execution current request bit clock quiet helper remembered helperRequest
              helperClock material offered interpretation marker sender addressed visible readout
                site atSite choice selected
          rw [failed] at lower
          norm_num at lower
      | some value => exact ⟨material, value, selected, offered, interpretation⟩

/-- The actual decoded incumbent kernel sends a usable declaration at the
same complete helper input. This is a physical-response statement, with the
original raw policy and its unchanged future retained. -/
theorem helper_eligible_decoded_response_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool) (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : bit = true → helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (response : app.Action)
    (chosen : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      alice (execution.recall alice) (execution.observe app alice)).support) :
    ∃ (material : WitnessedSubmission graph) (value : Bool),
      response.transmission = some material ∧
      response ∈ countedMenu.actions alice (execution.recall alice) (execution.observe app alice) ∧
      (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  classical
  have atInput : site.1 = some (execution.recall alice, execution.observe app alice) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf alice source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have law : rawMenu.decodeProfile initial horizon scheduler assessment.strategy alice
      (execution.recall alice) (execution.observe app alice) =
      (assessment.strategy alice site.1).map (fun choice => choice.1.getD ⟨none⟩) := by
    rw [atInput]
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
      ReactiveApplication.ResponseMenu.rawChoice]
  rw [law, PMF.support_map] at chosen
  obtain ⟨choice, supported, responseEq⟩ := chosen
  obtain ⟨material, value, selected, offered, interpreted⟩ :=
    helper_eligible_supported_choice_usable assessment equilibrium source remaining execution
      current request bit clock quiet helper remembered helperRequest helperClock waited marker
        sender addressed visible readout site atSite choice supported
  have actual : response = (⟨some material⟩ : app.Action) := by
    simpa only [selected, Option.getD_some] using responseEq.symm
  refine ⟨material, value, ?_, ?_, interpreted⟩
  · exact congrArg (fun response : app.Action => response.transmission) actual
  · rw [actual]
    exact offered

/-- When the helper has already been receipted at clock two, every supported
current choice waits for the useful clock-three slot. The safe whole deviation
and the losing one-shot transmission retain the same assessed continuation. -/
theorem helper_wrong_slot_supported_choice_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (choice : rawModel.Choice alice site.1)
    (supported : choice ∈ (assessment.strategy alice site.1).support) :
    choice.1 = some ⟨none⟩ := by
  classical
  have safe := raw_clock_two_helper_context_value_nonnegative assessment equilibrium source
    remaining execution current request clock quiet marker sender addressed visible site atSite
  have factor := rawModel.runnerFactorsAt_terminal canonicalCertificate
    (rawMenu.decisionRecall initial horizon scheduler).actsOnceWhereItMatters
    (rawMenu.informationSite_allNonterminal initial horizon scheduler alice site)
  have integrable (policy : rawModel.BehavioralPolicy alice) :=
    assessment.continuationContext_integrable_of_bounded_terminal canonicalCertificate site
      (rawPayoff alice) 6 (fun final _ => rawPayoff_abs_le alice final) policy
  have better := assessment.supported_choice_optimal
    (rawModel.runBehavioralTerminalFrom canonicalCertificate) site factor (rawPayoff alice)
    (equilibrium.1 alice site) (integrable (assessment.strategy alice)) choice supported
      (assessment.strategy alice) (integrable (assessment.strategy alice))
  have lower := safe.trans better
  change 0 ≤ (assessment.continuationContext canonicalCertificate site (rawPayoff alice)).value
    ((assessment.strategy alice).commit site.1 choice) at lower
  have atInput : site.1 = some (execution.recall alice, execution.observe app alice) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf alice source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun value _ => PhaseCount.countClean_initial runtime leaks value) source.trace
  rw [current] at clean
  have own : OwnPermitted alice execution :=
    ⟨clean.1, fun message member _ => clean.2 message member⟩
  have pastClean := (ownPermitted_iff_past alice execution clean.1).mp own
  have available : choice.1 ∈ rawModel.menu alice
      (some (execution.recall alice, execution.observe app alice)) := by
    simpa only [atInput] using choice.2
  obtain ⟨response, _rawAllowed, selected⟩ := available
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact selected
  | some material =>
      have offered := clean_supported_response_counted assessment equilibrium alice site
        (execution.recall alice) (execution.observe app alice) atInput pastClean choice supported
          ⟨some material⟩ selected
      have failed := raw_wrong_helper_binding_context_value assessment equilibrium source remaining
        execution current request clock quiet material offered marker sender addressed visible
          receipted site atSite choice selected
      rw [failed] at lower
      norm_num at lower

/-- The literal incumbent policy kernel is silent at the wrong helper slot,
including at full information inputs of zero assessed reach. -/
theorem helper_wrong_slot_raw_decoded_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace) :
    rawMenu.decodeProfile initial horizon scheduler assessment.strategy alice
      (execution.recall alice) (execution.observe app alice) = PMF.pure ⟨none⟩ := by
  classical
  have atInput : site.1 = some (execution.recall alice, execution.observe app alice) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf alice source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have law : rawMenu.decodeProfile initial horizon scheduler assessment.strategy alice
      (execution.recall alice) (execution.observe app alice) =
      (assessment.strategy alice site.1).map (fun choice => choice.1.getD ⟨none⟩) := by
    rw [atInput]
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp, Function.comp_def,
      ReactiveApplication.ResponseMenu.rawChoice]
  rw [law]
  apply pmf_eq_pure_of_support_subset_singleton
  intro response chosen
  obtain ⟨choice, supported, responseEq⟩ := PMF.support_map .. ▸ chosen
  have selected := helper_wrong_slot_supported_choice_wait assessment equilibrium source remaining
    execution current request clock quiet marker sender addressed visible receipted site atSite
      choice supported
  have actual : response = (⟨none⟩ : app.Action) := by
    simpa only [selected, Option.getD_some] using responseEq.symm
  exact actual

/-- The globally count-covered representation of the same assessment sends
usable material at the eligible helper input. No old-word consistency is
required to identify its actual current kernel. -/
theorem helper_eligible_counted_response_usable
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool) (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : bit = true → helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace)
    (response : app.Action)
    (chosen : response ∈ (countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) alice (execution.recall alice)
        (execution.observe app alice)).support) :
    ∃ (material : WitnessedSubmission graph) (value : Bool),
      response.transmission = some material ∧
      response ∈ countedMenu.actions alice (execution.recall alice) (execution.observe app alice) ∧
      (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  rw [counted_assessment_response_law assessment equilibrium source remaining execution alice
    current] at chosen
  exact helper_eligible_decoded_response_usable assessment equilibrium source remaining execution
    current request bit clock quiet helper remembered helperRequest helperClock waited marker
      sender addressed visible readout site atSite response chosen

/-- The counted continuation has exactly the same forced silent law as the
raw incumbent at the wrong helper slot. -/
theorem helper_wrong_slot_counted_decoded_wait
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts)
    (site : rawModel.InformationSite alice)
    (atSite : site.1 = countedModel.infoOf alice source.trace) :
    countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
      alice (execution.recall alice) (execution.observe app alice) = PMF.pure ⟨none⟩ := by
  rw [counted_assessment_response_law assessment equilibrium source remaining execution alice
    current]
  exact helper_wrong_slot_raw_decoded_wait assessment equilibrium source remaining execution
    current request clock quiet marker sender addressed visible receipted site atSite

private theorem source_raw_site (source : countedProtocol.History) (remaining : Nat)
    (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩) :
    ∃ site : rawModel.InformationSite alice,
      site.1 = countedModel.infoOf alice source.trace := by
  have running : ¬ countedProtocol.terminal source.state := by
    rw [current]
    intro stopped
    cases stopped.2
  have active : countedProtocol.active source.state alice := by rw [current]; rfl
  obtain ⟨site, observed⟩ :=
    countedModel.exists_informationSite_of_active alice source running active
  exact ⟨(countedInRaw.actionRestriction initial horizon scheduler).site alice site, observed⟩

/-- At a genuine source the usable-response classification requires no
separately supplied information-site witness. -/
theorem helper_eligible_counted_response_usable_at_source
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (bit : Bool) (clock : execution.application.current.native.clock = if bit then 3 else 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry)
    (remembered : helper ∈ execution.recall alice ∨
      helper = originalResponseEntry execution alice ⟨none⟩)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : bit = true → helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (readout : (∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts) ↔ bit = true)
    (response : app.Action)
    (chosen : response ∈ (countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) alice (execution.recall alice)
        (execution.observe app alice)).support) :
    ∃ (material : WitnessedSubmission graph) (value : Bool),
      response.transmission = some material ∧
      response ∈ countedMenu.actions alice (execution.recall alice) (execution.observe app alice) ∧
      (material.call.opening.bind fun raw => raw.as? .bool) = some value := by
  obtain ⟨site, atSite⟩ := source_raw_site source remaining execution current
  exact helper_eligible_counted_response_usable assessment equilibrium source remaining execution
    current request bit clock quiet helper remembered helperRequest helperClock waited marker
      sender addressed visible readout site atSite response chosen

/-- The actual wrong-slot counted law is silent at the genuine source,
with its information-site witness derived from that source. -/
theorem helper_wrong_slot_counted_decoded_wait_at_source
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts) :
    countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
      alice (execution.recall alice) (execution.observe app alice) = PMF.pure ⟨none⟩ := by
  obtain ⟨site, atSite⟩ := source_raw_site source remaining execution current
  exact helper_wrong_slot_counted_decoded_wait assessment equilibrium source remaining execution
    current request clock quiet marker sender addressed visible receipted site atSite

end Vegas.Examples.CommitSeedSignalling
