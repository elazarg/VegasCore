/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCollection
import Vegas.Game.RevealServiceCompletion
import Vegas.Compile.EventGraphReadout
import Vegas.Pending.RevealTranscript
import GameTheoryExtensions.Analysis.Enforcement

/-! # Net utilities for the monitored reveal service

One collectible deposit per ordinary player is charged on attributable rejection
or public format evidence. The utility and deposit are fixed before choosing an
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

/-- Decode the existing typed terminal store, retaining initial private cells
jointly with the public results. An unfinished execution has no readout. -/
def sourceReadout (state : (application setup leaks).ProtocolState) :
    Option (State L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.config
    if config.cut.Terminal then
      Vegas.decodeState? (Vegas.terminalRefs setup.program) config.store
    else none

theorem sourceReadout_normalization (state : (application setup leaks).ProtocolState) :
    sourceReadout setup leaks (((runtime setup).reactiveNormalization leaks).state state) =
      sourceReadout setup leaks state := by
  cases state <;> rfl

theorem sourceReadout_eq_some (control : (application setup leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal)
    (source : State L setup.program.terminalCtx)
    (agree : (Vegas.terminalRefs setup.program).Agrees source
      control.execution.application.config.store) :
    sourceReadout setup leaks (some control) = some source := by
  unfold sourceReadout
  rw [Option.bind_some, ite_eq_left terminal]
  exact Vegas.decodeState?_eq_some _ source _ agree

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

/-- Analysis utility of the actual terminal source readout, prior to a deposit
deduction. Initial private types may affect this utility. -/
def baseUtility (utility : State L setup.program.terminalCtx → Player → ℝ)
    (state : (application setup leaks).ProtocolState) (who : Player) : ℝ :=
  (sourceReadout setup leaks state).elim 0 (fun source => utility source who)

theorem baseUtility_normalization (utility : State L setup.program.terminalCtx → Player → ℝ)
    (state : (application setup leaks).ProtocolState) :
    baseUtility setup leaks utility (((runtime setup).reactiveNormalization leaks).state state) =
      baseUtility setup leaks utility state := by
  unfold baseUtility
  rw [sourceReadout_normalization]

theorem baseUtility_watcher (utility : State L setup.program.terminalCtx → Player → ℝ)
    (watcher : Player) (indifferent : ∀ source, utility source watcher = 0)
    (state : (application setup leaks).ProtocolState) :
    baseUtility setup leaks utility state watcher = 0 := by
  unfold baseUtility
  cases sourceReadout setup leaks state <;>
    simp only [Option.elim_none, Option.elim_some, indifferent]

open Classical in
/-- An ordinary player's deposit is forfeited once on attributable evidence.
The base utility may include the initial private type and terminal result. -/
def netUtility (watcher : Player)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (state : (application setup leaks).ProtocolState)
    (who : Player) : ℝ :=
  base state who - if who ≠ watcher ∧ departureAtState setup leaks who state then deposit who else 0

theorem departureAtState_normalization (who : Player)
    (state : (application setup leaks).ProtocolState) :
    departureAtState setup leaks who (((runtime setup).reactiveNormalization leaks).state state) ↔
      departureAtState setup leaks who state := by
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
  rw [invariant, propext (departureAtState_normalization setup leaks who state)]

theorem netUtility_watcher (watcher : Player)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (state : (application setup leaks).ProtocolState) :
    netUtility setup leaks watcher base deposit state watcher = base state watcher := by
  simp only [netUtility, ne_eq, not_true_eq_false, false_and, ↓reduceIte, sub_zero]

theorem netUtility_clean (watcher who : Player)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (state : (application setup leaks).ProtocolState)
    (clean : ¬ departureAtState setup leaks who state) :
    netUtility setup leaks watcher base deposit state who = base state who := by
  simp only [netUtility, clean, and_false, ↓reduceIte, sub_zero]

/-- The public transcript invariant discharges zero liability. In particular,
silent source withholding is not charged merely because it publishes failure. -/
theorem departureEvidence_clear_of_transcript (owner : Player)
    (execution : (application setup leaks).Execution)
    (accepted : AcceptedHandles (graph setup))
    (ledger : execution.network.ledger =
      publicationLedger accepted ((graph setup).publicObserve execution.application.config))
    (receipts : execution.receipts =
      publicationReceipts accepted ((graph setup).publicObserve execution.application.config)) :
    ¬ departureEvidence setup leaks owner execution := by
  rintro (⟨id, _authored, rejected⟩ | malformed)
  · rw [receipts] at rejected
    exact publicationReceipts_successful accepted _ id rejected
  · have clear := ledgerViolation_clear owner certifiedOpening execution.network.ledger
      (fun message member _ => publicationLedger_certified accepted _ message (ledger ▸ member))
    rw [clear] at malformed
    cases malformed

theorem netUtility_ordinary (watcher who : Player) (ordinary : who ≠ watcher)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) :
    (fun state => netUtility setup leaks watcher base deposit state who) =
      Enforcement.sanctionedUtility (fun state => base state who)
        {state | departureAtState setup leaks who state} (deposit who) := by
  classical
  funext state
  unfold netUtility Enforcement.sanctionedUtility
  change (base state who - if who ≠ watcher ∧ departureAtState setup leaks who state then
    deposit who else 0) =
      (base state who - if departureAtState setup leaks who state then deposit who else 0)
  by_cases detected : departureAtState setup leaks who state
  · rw [ite_eq_left ⟨ordinary, detected⟩, ite_eq_left detected]
  · rw [ite_eq_right (fun h => detected h.2), ite_eq_right detected]

/-- A conditional collection bound controls net utility under any subsequent
play. No independence between collection, disclosure, and payoff is required. -/
theorem netUtility_expect_le (watcher who : Player) (ordinary : who ≠ watcher)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (law : PMF (application setup leaks).ProtocolState) (upper probability : ℝ)
    (bounded : ∀ state ∈ law.support, base state who ≤ upper)
    (collection : probability ≤
        (law.toOuterMeasure {state | departureAtState setup leaks who state}).toReal) :
    expect law (fun state => netUtility setup leaks watcher base deposit state who) ≤
      upper - probability * deposit who := by
  rw [netUtility_ordinary setup leaks watcher who ordinary,
    Enforcement.expect_sanctionedUtility]
  apply sub_le_sub _ (mul_le_mul_of_nonneg_right collection nonnegative)
  calc
    _ ≤ expect law (fun _ => upper) := FinDist.expect_mono bounded
    _ = upper := expect_constant ..

/-- A whole-payoff-range deposit compares a monitored extra response with any
clean legal continuation. Both distributions are the actual native state laws;
the legal continuation may be randomized and may withhold later openings. -/
theorem netUtility_comparison (watcher who : Player) (ordinary : who ≠ watcher)
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (extra legal : PMF (application setup leaks).ProtocolState)
    (lower upper probability : ℝ)
    (above : ∀ state ∈ extra.support, base state who ≤ upper)
    (below : ∀ state ∈ legal.support, lower ≤ base state who)
    (clean : ∀ state ∈ legal.support, ¬ departureAtState setup leaks who state)
    (collection : probability ≤
        (extra.toOuterMeasure {state | departureAtState setup leaks who state}).toReal)
    (sufficient : upper - lower ≤ probability * deposit who) :
    expect extra (fun state => netUtility setup leaks watcher base deposit state who) ≤
      expect legal (fun state => netUtility setup leaks watcher base deposit state who) := by
  calc
    _ ≤ upper - probability * deposit who := netUtility_expect_le setup leaks watcher who ordinary
      base deposit nonnegative extra upper probability above collection
    _ ≤ lower := by linarith
    _ = expect legal (fun _ => lower) := (expect_constant ..).symm
    _ ≤ _ := by
      apply FinDist.expect_mono
      intro state supported
      rw [netUtility_clean setup leaks watcher who base deposit state (clean state supported)]
      exact below state supported

end Vegas
