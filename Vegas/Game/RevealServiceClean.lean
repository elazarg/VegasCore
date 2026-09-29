/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServicePayoffs

/-! # Zero liability at every retained terminal history

The operational prefix invariant covers every legal restricted history, not
only the histories reached by a compiled equilibrium. Its public transcript
contains successful canonical publications and therefore supplies no departure
evidence. This remains true after arbitrary retained continuation policies.
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

include reveals observer openable in
/-- A legal terminal C history has no attributable departure evidence for any
player, independently of all strategies and limiting equilibrium beliefs. -/
theorem terminal_history_clean
    (history : (protocol setup leaks bounds watcher).History)
    (terminal : (protocol setup leaks bounds watcher).terminal history.state) (who : Player) :
    ¬ departureAtState setup leaks who history.state := by
  let responses := menu setup leaks bounds watcher
  let profile := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  have length := (application setup leaks).trace_bound (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)
    (responses.toRawTrace (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) history.trace)
  rw [responses.toRawTrace_length] at length
  have supported := (responses.uniform_fullyMixed (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)).terminal_supported history terminal
      (2 * horizon setup watcher + 1) (by omega)
  have stateSupport : history.state ∈ (((information setup leaks bounds watcher).runBehavioral
      profile (2 * horizon setup watcher + 1)).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨history, supported, rfl⟩
  rw [menu_execution_law setup leaks responses watcher profile,
    PMF.support_bind] at stateSupport
  obtain ⟨initial, initially, continued⟩ := Set.mem_iUnion₂.mp stateSupport
  rw [PMF.support_map] at continued
  obtain ⟨execution, reached, same⟩ := continued
  let players := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) profile
  have completePlan : planPrefix setup watcher (eventCount setup.program) =
      plan setup watcher := by
    apply congrArg (List.flatMap (block setup watcher))
    simp only [List.take_eq_self_iff, List.length_finRange]
    exact Nat.le_refl _
  have actual : execution ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players ((runtime setup).reportNetwork leaks watcher)
        (planPrefix setup watcher (eventCount setup.program))
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support := by
    rw [completePlan, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initial, initially, reached⟩
  obtain ⟨sourceInitial, _, source, related, _decoded, _priorView, _sourceReach⟩ :=
    initialized_prefix_support setup leaks bounds watcher reveals observer openable players
      (menu_decode_reports setup leaks bounds watcher profile)
      (menu_decode_ordinary setup leaks bounds watcher profile)
      (eventCount setup.program) (Nat.le_refl _) execution actual
  rw [← same]
  change ¬ departureEvidence setup leaks who execution
  exact PrefixCheckpoint.runtime_fact (fun current => ¬ departureEvidence setup leaks who current)
    (fun _source _refs _rank current checkpoint =>
      departureEvidence_clear_of_transcript setup leaks who current _
        checkpoint.ledger checkpoint.receipts)
    setup.program _ _ _ 0 (eventCount setup.program) source execution related

include reveals observer openable in
/-- Every sufficiently long retained continuation is clean, including pure
local deviations at information sets that have zero equilibrium probability. -/
theorem continuation_clean
    (profile : Profile (information setup leaks bounds watcher).behavioralSignature)
    (history final : (protocol setup leaks bounds watcher).History)
    (fuel : Nat) (enough : 2 * horizon setup watcher + 1 - history.trace.length ≤ fuel)
    (supported : final ∈ ((information setup leaks bounds watcher).runBehavioralFrom profile fuel
      history).support) (who : Player) :
    ¬ departureAtState setup leaks who final.state := by
  apply terminal_history_clean setup leaks bounds watcher reveals observer openable final _ who
  rcases (protocol setup leaks bounds watcher).runRandomizedFor_terminal_or_length
      ((information setup leaks bounds watcher).randomizedChooser profile) fuel history final
      supported with terminal | length
  · exact terminal
  · exact (menu setup leaks bounds watcher).bounded (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) final.state final.trace (by omega)

include reveals observer openable in
/-- Every final history a retained continuation context can reach is free of
departure evidence, so there net and base utility agree. -/
private theorem continuationContext_net_eq_on_support
    (assessment : (information setup leaks bounds watcher).BehavioralAssessment)
    (base : (application setup leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ)
    (who : Player) (site : (information setup leaks bounds watcher).InformationSite who)
    (alternative : (information setup leaks bounds watcher).BehavioralPolicy who)
    (fuel : Nat)
    (enough : ∀ history : (information setup leaks bounds watcher).InformationHistory who site.1,
      2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel) :
    ∀ final ∈ ((assessment.continuationContext site (fun final => base final.state who)
        fuel).outcome alternative).support,
      netUtility setup leaks watcher base deposit final.state who = base final.state who := by
  intro final supported
  obtain ⟨history, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  exact netUtility_clean setup leaks watcher who base deposit final.state
    (continuation_clean setup leaks bounds watcher reveals observer openable _ history.1 final
      fuel (enough history) supported who)

include reveals observer openable in
/-- Deposits leave every retained conditional comparison unchanged. The
alternative is an arbitrary whole continuation policy, not only one response. -/
theorem continuationContext_net_value
    (assessment : (information setup leaks bounds watcher).BehavioralAssessment)
    (base : (application setup leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ)
    (who : Player) (site : (information setup leaks bounds watcher).InformationSite who)
    (alternative : (information setup leaks bounds watcher).BehavioralPolicy who)
    (fuel : Nat)
    (enough : ∀ history : (information setup leaks bounds watcher).InformationHistory who site.1,
      2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel) :
    (assessment.continuationContext site
      (fun final => netUtility setup leaks watcher base deposit final.state who) fuel).value
        alternative =
      (assessment.continuationContext site (fun final => base final.state who) fuel).value
        alternative :=
  expect_congr_on_support (continuationContext_net_eq_on_support setup leaks bounds watcher
    reveals observer openable assessment base deposit who site alternative fuel enough)

include reveals observer openable in
/-- Deposits leave integrability of every retained continuation unchanged. -/
theorem continuationContext_net_integrable
    (assessment : (information setup leaks bounds watcher).BehavioralAssessment)
    (base : (application setup leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ)
    (who : Player) (site : (information setup leaks bounds watcher).InformationSite who)
    (alternative : (information setup leaks bounds watcher).BehavioralPolicy who)
    (fuel : Nat)
    (enough : ∀ history : (information setup leaks bounds watcher).InformationHistory who site.1,
      2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel) :
    (assessment.continuationContext site
      (fun final => netUtility setup leaks watcher base deposit final.state who) fuel).IntegrableAt
        alternative ↔
      (assessment.continuationContext site (fun final => base final.state who) fuel).IntegrableAt
        alternative := by
  have same := continuationContext_net_eq_on_support setup leaks bounds watcher reveals observer
    openable assessment base deposit who site alternative fuel enough
  exact ⟨payoffIntegrable_congr_on_support same,
    payoffIntegrable_congr_on_support fun final supported => (same final supported).symm⟩

include reveals observer openable in
/-- Charging only departure evidence preserves exactly the C equilibria;
even retained off-equilibrium continuations are free of charges. -/
theorem sequential_equilibrium_net_iff
    (assessment : (information setup leaks bounds watcher).BehavioralAssessment)
    (antichain : (information setup leaks bounds watcher).DecisionInformationAntichain)
    (base : (application setup leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ) :
    assessment.IsSequentialEquilibriumFor antichain (fun who site =>
      assessment.continuationContext site
        (fun final => netUtility setup leaks watcher base deposit final.state who)
        (2 * horizon setup watcher + 1)) ↔
      assessment.IsSequentialEquilibriumFor antichain (fun who site =>
        assessment.continuationContext site (fun final => base final.state who)
          (2 * horizon setup watcher + 1)) := by
  have same who (site : (information setup leaks bounds watcher).InformationSite who) :=
    Context.isLocallyOptimal_congr (allowed := Set.univ) (choice := assessment.strategy who)
      (fun policy => continuationContext_net_integrable setup leaks bounds watcher reveals observer
        openable assessment base deposit who site policy (2 * horizon setup watcher + 1)
        (fun _ => Nat.sub_le ..))
      (fun policy _ => continuationContext_net_value setup leaks bounds watcher reveals observer
        openable assessment base deposit who site policy (2 * horizon setup watcher + 1)
        (fun _ => Nat.sub_le ..))
  constructor
  · rintro ⟨rational, consistent⟩
    exact ⟨fun who site => (same who site).mp (rational who site), consistent⟩
  · rintro ⟨rational, consistent⟩
    exact ⟨fun who site => (same who site).mpr (rational who site), consistent⟩

end Vegas
