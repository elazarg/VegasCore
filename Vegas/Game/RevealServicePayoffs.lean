/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCollection
import Vegas.Game.RevealServiceCompletion
import Vegas.Game.SourceServiceReadout
import Vegas.Pending.RevealTranscript
import GameTheoryExtensions.Analysis.Enforcement

/-! # Net utilities for the monitored reveal service

One collectible deposit per ordinary player is charged at settlement when a
packet it signed, on the ledger or in the watcher's report, is forbidden by the
settled record. The utility and deposit are fixed before choosing an
equilibrium. Reporting has no separate payment here; the watcher retains its
declared base utility and must be indifferent for the watcher-extension theorem.

The comparison tolerates arbitrary outcomes after an extra response, including
communication that a recipient reads before the watcher reports. Its probability
bound concerns actual collection evidence, supplied by the monitored service.
The deduction models collection in utility units, not an implementation of escrow.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Every bounded raw play has a complete source-state readout. Decoding does
not invent default payloads, even after arbitrary malformed responses. -/
theorem sourceReadout_succeeds [Fintype Player]
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (profile : ∀ who, (responses.information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).BehavioralPolicy who)
    (history : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).History)
    (supported : history ∈ ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioral profile
        (2 * horizon setup watcher + 1)).support) :
    (sourceReadout setup leaks history.state).isSome = true := by
  obtain ⟨execution, same, terminal⟩ :=
    menu_settles setup leaks responses watcher reveals profile history supported
  rw [same]
  change (if execution.application.config.cut.Terminal then
    Vegas.decodeState? (Vegas.terminalRefs setup.program)
      execution.application.config.store else none).isSome = true
  rw [ite_eq_left terminal]
  exact Vegas.decodeState?_isSome_of_available _ _
    (fun field => execution.application.config.store_available_of_terminal terminal field)

open Classical in
/-- An ordinary player's deposit is forfeited once on attributable evidence.
The base utility may include the initial private type and terminal result. -/
def netUtility (watcher : Player)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (state : (application setup leaks).ProtocolState)
    (who : Player) : ℝ :=
  base state who -
    if who ≠ watcher ∧ departureAtState setup leaks watcher who state then deposit who else 0

theorem departureAtState_normalization (watcher who : Player)
    (state : (application setup leaks).ProtocolState) :
    departureAtState setup leaks watcher who
        (((runtime setup).reactiveNormalization leaks).state state) ↔
      departureAtState setup leaks watcher who state := by
  cases state <;> rfl

theorem netUtility_normalization (watcher : Player)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ)
    (invariant : ∀ state,
      base (((runtime setup).reactiveNormalization leaks).state state) = base state)
    (state : (application setup leaks).ProtocolState) :
    netUtility setup leaks watcher base deposit
        (((runtime setup).reactiveNormalization leaks).state state) =
      netUtility setup leaks watcher base deposit state := by
  funext who
  unfold netUtility
  rw [invariant, propext (departureAtState_normalization setup leaks watcher who state)]

theorem netUtility_watcher (watcher : Player)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (state : (application setup leaks).ProtocolState) :
    netUtility setup leaks watcher base deposit state watcher = base state watcher := by
  simp only [netUtility, ne_eq, not_true_eq_false, false_and, ↓reduceIte, sub_zero]

theorem netUtility_clean (watcher who : Player)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (state : (application setup leaks).ProtocolState)
    (clean : ¬ departureAtState setup leaks watcher who state) :
    netUtility setup leaks watcher base deposit state who = base state who := by
  simp only [netUtility, clean, and_false, ↓reduceIte, sub_zero]

omit [DecidableEq Player] in
private theorem cast_option_map {α β : Type} (same : α = β) (value : Option α) :
    cast (congrArg Option same) value = value.map (cast same) := by
  cases same
  cases value <;> rfl

/-- Every entry of a canonical publication transcript is permitted by the
settled record of a reachable execution: the record accepted it, it carries
its exact certificate, and its value passes its event's checks on the settled
public store. -/
theorem publicationLedger_permitted (execution : (application setup leaks).Execution)
    (inputs : (graph setup).Inputs)
    (reachable : execution.application.config.Reachable inputs)
    (accepted : AcceptedHandles (graph setup))
    (ledger : execution.network.ledger =
      publicationLedger accepted ((graph setup).publicObserve execution.application.config))
    (receipts : execution.receipts =
      publicationReceipts accepted ((graph setup).publicObserve execution.application.config))
    (message : Message Player (WitnessedPacket (graph setup)))
    (member : message ∈ execution.network.ledger) :
    ((runtime setup).settledRecord leaks execution).permits message = true := by
  let config := execution.application.config
  have certified := publicationLedger_certified accepted _ message (ledger ▸ member)
  have decoded : (message.sender, message.payload) ∈
      publicationPackets accepted ((graph setup).publicObserve config) := by
    have inLedger : message ∈ publicationLedger accepted ((graph setup).publicObserve config) :=
      ledger ▸ member
    rw [← RevealTranscript.numberPackets_decode (fun _ : Player => 0)
      (publicationPackets accepted ((graph setup).publicObserve config))]
    exact List.mem_map_of_mem inLedger
  obtain ⟨event, _, encoded⟩ := List.mem_filterMap.mp decoded
  change publicationPacket? accepted ((graph setup).publicStore config.store) event = _ at encoded
  rw [publicationPacket?_publicStore] at encoded
  have acceptedId : ((runtime setup).settledRecord leaks execution).Accepts message.id := by
    change (message.id, true) ∈ execution.receipts
    rw [receipts]
    exact List.mem_map_of_mem (ledger ▸ member)
  unfold publicationPacket? at encoded
  split at encoded
  · cases encoded
  · cases encoded
  · rename_i owner payload binding checks outputEq codeEq node
    split at encoded
    · cases encoded
    · cases encoded
    · rename_i value stored
      obtain ⟨candidate, _, packet⟩ := Option.map_eq_some_iff.mp encoded
      rcases message with ⟨id, call, evidence, token⟩
      cases Prod.ext_iff.mp packet |>.2
      have published : (⟨.inr event, outputEq⟩ :
          EventGraph.FieldRef (graph setup).layout (.publication payload)).get?
            config.store = some (.success value) :=
        (cast_option_map (congrArg EventGraph.EventField.Value outputEq) _).trans stored
      have guards := EventGraph.Config.Reachable.publication_guards reachable event owner payload
        binding checks outputEq codeEq value published
      refine SettledRecord.permits_of_accepted _ _ event rfl acceptedId ⟨certified, ?_⟩
      refine (PublicView.openingGuardsAccepted_iff _ owner event payload binding checks outputEq
        codeEq node candidate _ _).mpr ⟨value, rfl, ?_⟩
      change EventGraph.GuardCheck.allAccepted? checks ((graph setup).publicStore config.store)
        (.success value) = some true
      rw [EventGraph.GuardCheck.allAccepted?_publicStore]
      exact guards

/-- A canonical publication transcript with an empty watcher report supplies
no departure evidence. In particular silent source withholding is not charged
merely because it publishes failure. -/
theorem departureEvidence_clear_of_transcript (watcher owner : Player)
    (execution : (application setup leaks).Execution) (inputs : (graph setup).Inputs)
    (reachable : execution.application.config.Reachable inputs)
    (accepted : AcceptedHandles (graph setup))
    (ledger : execution.network.ledger =
      publicationLedger accepted ((graph setup).publicObserve execution.application.config))
    (receipts : execution.receipts =
      publicationReceipts accepted ((graph setup).publicObserve execution.application.config))
    (unreported : execution.network.leaked watcher = []) :
    ¬ departureEvidence setup leaks watcher owner execution := by
  rintro ⟨message, place, _, forbidden⟩
  rcases place with published | observed
  · rw [publicationLedger_permitted setup leaks execution inputs reachable accepted ledger
      receipts message published] at forbidden
    cases forbidden
  · rw [unreported] at observed
    cases observed

theorem netUtility_ordinary (watcher who : Player) (ordinary : who ≠ watcher)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) :
    (fun state => netUtility setup leaks watcher base deposit state who) =
      Enforcement.sanctionedUtility (fun state => base state who)
        {state | departureAtState setup leaks watcher who state} (deposit who) := by
  classical
  funext state
  unfold netUtility Enforcement.sanctionedUtility
  change (base state who - if who ≠ watcher ∧ departureAtState setup leaks watcher who state then
    deposit who else 0) =
      (base state who - if departureAtState setup leaks watcher who state then deposit who else 0)
  by_cases detected : departureAtState setup leaks watcher who state
  · rw [ite_eq_left ⟨ordinary, detected⟩, ite_eq_left detected]
  · rw [ite_eq_right (fun h => detected h.2), ite_eq_right detected]

/-- A conditional collection bound controls net utility under any subsequent
play whose base payoff is integrable. No independence between collection,
disclosure, and payoff is required. -/
theorem netUtility_expect_le (watcher who : Player) (ordinary : who ≠ watcher)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (law : PMF (application setup leaks).ProtocolState) (upper probability : ℝ)
    (bounded : ∀ state ∈ law.support, base state who ≤ upper)
    (integrable : PayoffIntegrable law fun state => base state who)
    (collection : probability ≤
        (law.toOuterMeasure {state | departureAtState setup leaks watcher who state}).toReal) :
    expect law (fun state => netUtility setup leaks watcher base deposit state who) ≤
      upper - probability * deposit who := by
  rw [netUtility_ordinary setup leaks watcher who ordinary,
    Enforcement.expect_sanctionedUtility _ _ _ _ integrable]
  apply sub_le_sub _ (mul_le_mul_of_nonneg_right collection nonnegative)
  calc
    _ ≤ expect law (fun _ => upper) :=
      expect_mono bounded integrable (payoffIntegrable_constant _ _)
    _ = upper := expect_constant ..

/-- A whole-payoff-range deposit compares a monitored extra response with any
clean legal continuation. Both distributions are the actual native state laws,
with integrable base payoffs; the legal continuation may be randomized and may
withhold later openings. -/
theorem netUtility_comparison (watcher who : Player) (ordinary : who ≠ watcher)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (extra legal : PMF (application setup leaks).ProtocolState)
    (lower upper probability : ℝ)
    (above : ∀ state ∈ extra.support, base state who ≤ upper)
    (below : ∀ state ∈ legal.support, lower ≤ base state who)
    (clean : ∀ state ∈ legal.support, ¬ departureAtState setup leaks watcher who state)
    (extraIntegrable : PayoffIntegrable extra fun state => base state who)
    (legalIntegrable : PayoffIntegrable legal fun state => base state who)
    (collection : probability ≤
        (extra.toOuterMeasure {state | departureAtState setup leaks watcher who state}).toReal)
    (sufficient : upper - lower ≤ probability * deposit who) :
    expect extra (fun state => netUtility setup leaks watcher base deposit state who) ≤
      expect legal (fun state => netUtility setup leaks watcher base deposit state who) := by
  calc
    _ ≤ upper - probability * deposit who := netUtility_expect_le setup leaks watcher who ordinary
      base deposit nonnegative extra upper probability above extraIntegrable collection
    _ ≤ lower := by linarith
    _ = expect legal (fun _ => lower) := (expect_constant ..).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _)
        (payoffIntegrable_congr_on_support (fun state supported =>
          (netUtility_clean setup leaks watcher who base deposit state
            (clean state supported)).symm) legalIntegrable)
      intro state supported
      rw [netUtility_clean setup leaks watcher who base deposit state (clean state supported)]
      exact below state supported

end Vegas
