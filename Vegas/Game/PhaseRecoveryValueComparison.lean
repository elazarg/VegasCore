/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueInputWeights
import Vegas.Game.PhaseTimingContinuationFiber
import Vegas.Game.PhaseTimingContinuationLower
import Vegas.Pending.PhaseAttemptEntryFiber
import Vegas.Pending.PhaseBindingReadiness
import GameTheoryExtensions.Math.Probability.ProductTransport
import Vegas.Pending.PhaseAttemptFirstPassage
import Interaction.ReactiveRecallReplay
import Vegas.Pending.PhaseAttemptPassage
import Vegas.Game.PhaseRecoveryValueBelief
import GameTheoryExtensions.Analysis.Protocol.PassageBayes
import Vegas.Game.PhaseClearProfileLocality
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import Vegas.Pending.PhaseAttemptEntryStopping
import GameTheoryExtensions.Analysis.Protocol.StoppedComposition

/-! # Conditional comparison under the actual selected immutable entry law -/

noncomputable section

namespace Vegas

open scoped ENNReal

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance phaseRecoveryValueComparisonPoolFintype : Fintype Pool := Fintype.ofFinite _

local notation "History" => ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (PhaseCount.onePacketMenu runtime leaks bounds)
    initial horizon scheduler)

private abbrev RecoveryValueMemories := (owner : Player) → ((p : Pool) → Parts p) ×
  (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy owner

local notation "Memory" => RecoveryValueMemories setup mode runtime leaks bounds runtimePlan
  horizon scheduler bound
local notation "Tag" => History × Memory



omit [Fintype ((menu).protocol initial horizon scheduler).History]
  [∀ owner, DecidableEq (((menu).information initial horizon scheduler).InfoState owner)] in
private theorem conditional_input_weights
    [Finite ((menu).protocol initial horizon scheduler).History]
    (who : Player) (site : (N).InformationSite who)
    (belief : PMF ((N).InformationHistory who site.1)) (hit reference : PMF History)
    (D : ℝ≥0∞) (DPositive : 0 < D) (Dfinite : D ≠ ∞)
    (total : (∑' history : (N).InformationHistory who site.1, hit history.1) = D)
    (atoms : ∀ history : (N).InformationHistory who site.1,
      belief history = hit history.1 / D)
    (a b : ℝ) (aPositive : 0 < a) (aBounded : a ≤ 1) (bAtLeastOne : 1 ≤ b)
    (error : (N).InformationHistory who site.1 → ℝ≥0∞)
    (aggregate : ∀ history : (N).InformationHistory who site.1,
      ENNReal.ofReal a * reference history.1 ≤ hit history.1 ∧
        hit history.1 ≤ ENNReal.ofReal b * reference history.1 + error history) :
    (∑' history : (N).InformationHistory who site.1, error history) < D →
      0 < ∑' history : (N).InformationHistory who site.1, (reference history.1).toReal ∧
      (∑' history : (N).InformationHistory who site.1,
        |(belief history).toReal - (reference history.1).toReal /
          ∑' other : (N).InformationHistory who site.1, (reference other.1).toReal|) ≤
        2 * ((b - a) / a +
          (∑' history : (N).InformationHistory who site.1, error history).toReal / D.toReal) := by
  classical
  have aNonnegative := aPositive.le
  have bNonnegative : 0 ≤ b := le_trans (by norm_num) bAtLeastOne
  intro smallError
  let Fiber := (N).InformationHistory who site.1
  let fiberFintype : Fintype Fiber := Fintype.ofFinite _
  let u := fun history : Fiber => (hit history.1).toReal
  let v := fun history : Fiber => (reference history.1).toReal
  let V := ∑ history : Fiber, v history
  let R := ∑' history : Fiber, error history
  let d := D.toReal
  have dPositive : 0 < d := ENNReal.toReal_pos DPositive.ne' Dfinite
  have Rfinite : R ≠ ∞ := ne_top_of_lt smallError
  have errorFinite (history : Fiber) : error history ≠ ∞ :=
    ne_top_of_le_ne_top Rfinite (ENNReal.le_tsum history)
  have realBounds (history : Fiber) : a * v history ≤ u history ∧
      u history ≤ b * v history + (error history).toReal := by
    have lower := ENNReal.toReal_mono (PMF.apply_ne_top hit history.1) (aggregate history).1
    have upperFinite : ENNReal.ofReal b * reference history.1 + error history ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (PMF.apply_ne_top reference history.1), errorFinite history⟩
    have upper := ENNReal.toReal_mono upperFinite (aggregate history).2
    constructor
    · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal aNonnegative] using lower
    · simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (PMF.apply_ne_top reference history.1)) (errorFinite history), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal bNonnegative] using upper
  have totalReal : (∑ history : Fiber, u history) = d := by
    dsimp only [d]
    rw [← total, tsum_fintype, ENNReal.toReal_sum (fun history _ => PMF.apply_ne_top hit history.1)]
  have errorReal : (∑ history : Fiber, (error history).toReal) = R.toReal := by
    dsimp only [R]
    rw [tsum_fintype, ENNReal.toReal_sum (fun history _ => errorFinite history)]
  have totalUpper : d ≤ b * V + R.toReal := by
    rw [← totalReal, ← errorReal, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun history _ => (realBounds history).2
  have smallReal : R.toReal < d := (ENNReal.toReal_lt_toReal Rfinite Dfinite).mpr smallError
  have vNonnegative (history : Fiber) : 0 ≤ v history := ENNReal.toReal_nonneg
  have VPositive : 0 < V := by
    have nonnegativeV : 0 ≤ V := Finset.sum_nonneg fun history _ => vNonnegative history
    by_contra notPositive
    have equal : V = 0 := le_antisymm (not_lt.mp notPositive) nonnegativeV
    rw [equal, mul_zero, zero_add] at totalUpper
    linarith
  have BA : 0 ≤ b - a := sub_nonneg.mpr (aBounded.trans bAtLeastOne)
  have pointGap (history : Fiber) : |u history - v history| ≤
      (b - a) * v history + (error history).toReal := by
    have low := (realBounds history).1
    have high := (realBounds history).2
    have eNonnegative : 0 ≤ (error history).toReal := ENNReal.toReal_nonneg
    have vb := mul_nonneg (sub_nonneg.mpr bAtLeastOne) (vNonnegative history)
    have va := mul_nonneg (sub_nonneg.mpr aBounded) (vNonnegative history)
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have gap : (∑ history : Fiber, |u history - v history|) ≤ (b - a) * V + R.toReal := by
    rw [← errorReal, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun history _ => pointGap history
  have retained : a * V ≤ d := by
    rw [← totalReal, Finset.mul_sum]
    exact Finset.sum_le_sum fun history _ => (realBounds history).1
  let gamma := (b - a) + R.toReal / V
  let lower := d / V
  have gammaEq : gamma * V = (b - a) * V + R.toReal := by
    dsimp only [gamma]
    field_simp [VPositive.ne', dPositive.ne']
  have lowerEq : lower * V = d := div_mul_cancel₀ d VPositive.ne'
  have normalized := sum_abs_div_sum_sub_div_sum_le vNonnegative VPositive
    (gammaEq.symm ▸ gap) (div_pos dPositive VPositive)
      (by rw [totalReal]; exact lowerEq.le)
  have normalizedEq : 2 * gamma / lower =
      2 * ((b - a) * V / d + R.toReal / d) := by
    dsimp only [gamma, lower]
    field_simp [VPositive.ne', dPositive.ne']
  have ratio : (b - a) * V / d ≤ (b - a) / a := by
    apply (div_le_div_iff₀ dPositive aPositive).mpr
    have multiplied := mul_le_mul_of_nonneg_left retained BA
    nlinarith
  refine ⟨by simpa only [tsum_fintype] using VPositive, ?_⟩
  have finalBound : (∑ history : Fiber,
      |u history / (∑ other : Fiber, u other) - v history / (∑ other : Fiber, v other)|) ≤
        2 * ((b - a) / a + R.toReal / d) :=
    normalized.trans (by rw [normalizedEq]; linarith [ratio])
  rw [totalReal] at finalBound
  have beliefReal (history : Fiber) : (belief history).toReal = u history / d := by
    rw [atoms, ENNReal.toReal_div]
  simpa only [tsum_fintype, beliefReal, u, v, R, d] using finalBound


omit [Fintype ((menu).protocol initial horizon scheduler).History]
  [∀ owner, DecidableEq (((menu).information initial horizon scheduler).InfoState owner)] in
private theorem actual_binding_fiber
    (who : Player) (site : (N).InformationSite who)
    (original : (app).Control)
    (originalTrace : ((menu).protocol initial horizon scheduler).Trace (some original))
    (atSite : (N).infoOf who originalTrace = site.1) (active : original.actor = some who)
    (clear : original.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId)
    (request : original.execution.application.SeedRequest who
      ⟨original.execution.application.attempt, event⟩) :
    ∀ history : (N).InformationHistory who site.1,
      ∃ current : (app).Control, history.1.state = some current ∧ current.actor = some who ∧
        current.execution.application.current.excluded = ∅ ∧
        current.execution.application.SeedRequest who
          ⟨current.execution.application.attempt, event⟩ := by
  let initialFlat := setup.initialLaw.map fun draw =>
    PhaseRuntimeState.initial runtimePlan (encodeInputs draw)
  have initialEq : initial = initialFlat := PMF.map_comp ..
  let property := fun law : PMF (app).State =>
    ∀ (reference : (app).Control)
      (trace : ((menu).protocol law horizon scheduler).Trace (some reference))
      (site : ((menu).information law horizon scheduler).InformationSite who),
      ((menu).information law horizon scheduler).infoOf who trace = site.1 →
      reference.actor = some who → reference.execution.application.current.excluded = ∅ →
      reference.execution.application.SeedRequest who
        ⟨reference.execution.application.attempt, event⟩ →
      ∀ history : ((menu).information law horizon scheduler).InformationHistory who site.1,
        ∃ current : (app).Control, history.1.state = some current ∧ current.actor = some who ∧
          current.execution.application.current.excluded = ∅ ∧
          current.execution.application.SeedRequest who
            ⟨current.execution.application.attempt, event⟩
  have flat : property initialFlat := by
    intro reference trace referenceSite atReference acting referenceClear requested
    exact phase_binding_fiber_genuine setup mode runtime leaks bounds runtimePlan horizon
      scheduler
      who referenceSite reference trace atReference acting event referenceClear requested
  have actualProperty : property initial := initialEq.symm ▸ flat
  exact actualProperty original originalTrace site atSite active clear request

omit [Fintype ((menu).protocol initial horizon scheduler).History]
  [∀ owner, DecidableEq (((menu).information initial horizon scheduler).InfoState owner)] in
private theorem actual_binding_entry
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (entryProfile profile : ∀ owner, (N).BehavioralPolicy owner)
    (who : Player) (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (current : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some current))
    (same : (N).infoOf who trace = site.1) (acting : current.actor = some who)
    (currentClear : current.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (entry : History)
    (entrySupported : entry ∈ ((N).runBehavioralUntil certificate entryProfile
      (fun history => phaseAttemptEntryStop runtime leaks view.application.2.attempt history.state)
        ((menu).protocol initial horizon scheduler).initHistory).support)
    (supported : ⟨some current, trace⟩ ∈ ((N).runBehavioralUntil certificate profile
      (fun history : History => match history.state with
        | none => False
        | some next => next.execution.application.current.excluded ≠ ∅ ∨
            next.execution.application.attempt ≠ view.application.2.attempt ∨
            (N).infoOf who history.trace = site.1) entry).support) :
    ∃ start : (app).Control, entry.state = some start ∧ ∃ phase remaining,
      start.execution.application.phases = phase :: remaining ∧
        phase.kind = .commitment ∧ event ∈ phase.events := by
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact PhaseRuntimeState.initial_ordered runtimePlan draw
  obtain ⟨start, startState, _idle, _startClear, _attempt, phases, _fresh⟩ :=
    phase_attempt_entry_of_supported_hit runtime leaks menu initial horizon scheduler initialized
      certificate entryProfile profile site past view observed current trace same acting
        currentClear
        entry entrySupported (by
          convert supported using 1; congr 2
          all_goals
            funext history
            rcases history with ⟨state, historyTrace⟩
            cases state <;> rfl)
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨phase, remaining, installed, kind, inside⟩ := phase_ready_binding_phase runtime leaks
    runtimePlan (serviceGraph_revealRelaxedOrdered setup mode) maximal
      (setup.initialLaw.map encodeInputs) horizon scheduler raw who event payload binding
        ready
  exact ⟨start, startState, phase, remaining, phases.trans installed, kind, inside⟩

private theorem actual_member_profile
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (base : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (replay : (N).BehavioralPolicy who) (memories : Memory) :
    let members := fun owner (memory : ((p : Pool) → Parts p) ×
        (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy owner) =>
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed base owner memory.2)
          noise noiseNonnegative noiseSmall slotWeight slotNonnegative slotBounded memory.1 owner
    let changed := Function.update members who (fun _ =>
      (app).decodePolicy ((menu).embedPolicy initial horizon scheduler who replay))
    (fun owner => (menu).restrictPolicy initial horizon scheduler
      owner (changed owner (memories owner))) = Function.update (fun owner =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed base
          owner (memories owner).2) noise noiseNonnegative noiseSmall slotWeight slotNonnegative
            slotBounded (fun owner => (memories owner).1) owner) who replay := by
  intro members changed
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [changed, Function.update_self]
    exact (menu).restrict_decode_embedPolicy initial horizon scheduler who replay
  · simp only [changed, Function.update_of_ne same, members]
    change (menu).restrictPolicy initial horizon scheduler owner
      ((menu).decodeProfile initial horizon scheduler
        (phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed
            base owner (memories owner).2) noise noiseNonnegative noiseSmall
              slotWeight slotNonnegative slotBounded (fun owner => (memories owner).1)) owner) = _
    exact (menu).restrict_decode_embedPolicy initial horizon scheduler owner _

omit [Fintype ((menu).protocol initial horizon scheduler).History]
  [∀ owner, DecidableEq (((menu).information initial horizon scheduler).InfoState owner)] in
/-- The intrinsic native RAW binding-send marks in the actual NEW response
suffix, retaining the same transition coefficient and all other noisy atoms. -/
def binding_marker_density (noise : ℝ) (focal : Player)
    (profile : ∀ owner, (N).BehavioralPolicy owner)
    (records : ∀ owner, List ((N).InfoState owner ×
      ((menu).protocol initial horizon scheduler).Action owner)) (chance : ℝ) : ℝ :=
  chance * ∑ index : (Σ owner, Fin (records owner).length),
    (if index.1 ≠ focal ∧ (records index.1)[index.2.val].2.transmission ≠ none
      then phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise index.1 (records index.1)[index.2.val] else 0) *
      ∏ other ∈ Finset.univ.erase index,
        (((profile other.1 (records other.1)[other.2.val].1).map Subtype.val)
          (some (records other.1)[other.2.val].2)).toReal

omit [Fintype ((menu).protocol initial horizon scheduler).History]
  [∀ owner, DecidableEq (((menu).information initial horizon scheduler).InfoState owner)] in
private theorem binding_marker_density_nonnegative (noise : ℝ) (nonnegative : 0 ≤ noise)
    (focal : Player) (profile : ∀ owner, (N).BehavioralPolicy owner)
    (records : ∀ owner, List ((N).InfoState owner ×
      ((menu).protocol initial horizon scheduler).Action owner))
    (chance : ℝ) (nonnegativeChance : 0 ≤ chance) :
    0 ≤ binding_marker_density setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise focal profile records chance := by
  apply mul_nonneg nonnegativeChance
  apply Finset.sum_nonneg
  intro index _member
  apply mul_nonneg _ (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
  split_ifs
  · exact mul_nonneg nonnegative ENNReal.toReal_nonneg
  · exact le_rfl

private theorem actual_supported_marker_bounds
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (n : Nat)
    (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (replay : (N).BehavioralPolicy who)
    (memories : Memory)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (site : (N).InformationSite who)
    (original : (app).Control)
    (originalTrace : ((menu).protocol initial horizon scheduler).Trace (some original))
    (atSite : (N).infoOf who originalTrace = site.1) (active : original.actor = some who)
    (originalClear : original.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId)
    (request : original.execution.application.SeedRequest who
      ⟨original.execution.application.attempt, event⟩)
    (current : (app).Control)
    (entryTrace : ((menu).protocol initial horizon scheduler).Trace (some current))
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : current.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment) (inside : event ∈ phase.events) :
    let noisy := Function.update (fun owner =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed
          (approximation.sequence n)
          owner (memories owner).2) noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
            slotBounded (fun owner => (memories owner).1) owner) who replay
    let zero := Function.update (fun owner =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed
          (approximation.sequence n)
          owner (memories owner).2) 0 (by norm_num) (by norm_num) slotWeight slotPositive.le
            slotBounded (fun owner => (memories owner).1) owner) who replay
    let stopped := fun history : History => match history.state with
      | none => False
      | some next => next.execution.application.current.excluded ≠ ∅ ∨
          next.execution.application.attempt ≠ original.execution.application.attempt ∨
          (N).infoOf who history.trace = site.1
    let K := Fintype.card Player * (2 * horizon + 1)
    let a := (1 - noise) ^ K
    let b := (1 + noise / (slotWeight * floor)) ^ K
    ∃ marker : (N).InformationHistory who site.1 → ℝ,
      (∀ history, 0 ≤ marker history) ∧
      (∀ history, ∃ records : ∀ owner, List ((N).InfoState owner ×
          ((menu).protocol initial horizon scheduler).Action owner),
        ∃ chance : ℝ, 0 ≤ chance ∧
        (chance ≠ 0 → TracePrefix (⟨some current, entryTrace⟩ : History).trace history.1.trace ∧
          (∀ owner, (N).ownPlay owner history.1.trace =
            records owner ++ (N).ownPlay owner (⟨some current, entryTrace⟩ : History).trace) ∧
          (∀ owner record, record ∈ records owner →
            ∃ (before : History)
              (joint : ∀ player, Option (((menu).protocol initial horizon scheduler).Action player))
              (legal : ((menu).protocol initial horizon scheduler).Legal before.state joint)
              (next : ((menu).protocol initial horizon scheduler).State)
              (realized : next ∈ (((menu).protocol initial horizon scheduler).step
                before.state ⟨joint, legal⟩).support),
              TracePrefix (⟨some current, entryTrace⟩ : History).trace before.trace ∧
              TracePrefix (before.trace.extend joint legal realized) history.1.trace ∧
              (N).infoOf owner before.trace = record.1 ∧ joint owner = some record.2) ∧
          (∀ profile : ∀ owner, (N).BehavioralPolicy owner,
            (((N).runBehavioralFrom profile (history.1.trace.length -
              (⟨some current, entryTrace⟩ : History).trace.length)
              (⟨some current, entryTrace⟩ : History)) history.1).toReal =
                chance * ∏ owner, (N).ownPlayReachProbability (profile owner) (records owner))) ∧
          (∀ owner record, record ∈ records owner → record.2.transmission ≠ none →
            phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
              owner record) ∧ marker history = chance *
            ∑ index : (Σ owner, Fin (records owner).length),
              (if index.1 ≠ who ∧ (records index.1)[index.2.val].2.transmission ≠ none
                then phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon
                  scheduler noise index.1 (records index.1)[index.2.val] else 0) *
                ∏ other ∈ Finset.univ.erase index,
                  (((noisy other.1 (records other.1)[other.2.val].1).map Subtype.val)
                    (some (records other.1)[other.2.val].2)).toReal) ∧
      (∀ history : (N).InformationHistory who site.1,
        a * (((N).runBehavioralUntil certificate zero stopped ⟨some current, entryTrace⟩)
          history.1).toReal ≤
          (((N).runBehavioralUntil certificate noisy stopped ⟨some current, entryTrace⟩)
          history.1).toReal ∧
        (((N).runBehavioralUntil certificate noisy stopped ⟨some current, entryTrace⟩)
          history.1).toReal ≤
          b * (((N).runBehavioralUntil certificate zero stopped ⟨some current, entryTrace⟩)
          history.1).toReal +
            marker history) := by
  classical
  intro noisy zero stopped K a b
  have initialEq : initial = setup.initialLaw.map (fun draw =>
      PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) := PMF.map_comp ..
  obtain ⟨records, chance, chanceNonnegative, bindingRecords, provenance, _finite, upper⟩ :=
    phase_timing_continuation_fiber_noise setup mode runtime leaks bounds runtimePlan initial
      initialEq horizon scheduler bound finite wellFormed target approximation maximal fallback
        n
        capacity floor positive floorBounded floored noise noiseNonnegative noiseSmall
          slotWeight
          slotPositive slotBounded (fun owner => (memories owner).1)
            (fun owner => (memories owner).2) who replay current original entryTrace
                originalTrace
              phase remaining installed committing event inside allValues originalClear request
                active certificate site atSite ∅
  let marker := fun history => binding_marker_density setup mode runtime leaks bounds
    runtimePlan horizon scheduler noise who noisy (records history) (chance history)
  have markerNonnegative (history) : 0 ≤ marker history :=
    binding_marker_density_nonnegative setup mode runtime leaks bounds runtimePlan horizon
      scheduler noise noiseNonnegative who noisy (records history) (chance history)
        (chanceNonnegative history)
  refine ⟨marker, markerNonnegative, ?_, ?_⟩
  · intro history
    exact ⟨records history, chance history, chanceNonnegative history,
      provenance history, bindingRecords history, rfl⟩
  · intro history
    have lower := phase_timing_continuation_fiber_lower setup mode runtime leaks bounds
      runtimePlan initial initialEq horizon scheduler bound fallback wellFormed
        (fun owner => setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n)
          owner (memories owner).2) noise noiseNonnegative noiseSmall.le slotWeight
            slotPositive.le slotBounded (fun owner => (memories owner).1) who replay current
              original entryTrace originalTrace phase remaining installed event inside
                originalClear request active certificate site atSite {history}
    simp only [Finset.sum_singleton] at lower
    dsimp only at upper lower
    constructor
    · convert lower using 1 <;> congr 5
      all_goals
        funext next
        rcases next with ⟨state, trace⟩
        cases state <;> rfl
    · have bounded := upper history
      convert bounded using 1 <;> congr 5
      all_goals
        funext next
        rcases next with ⟨state, trace⟩
        cases state <;> rfl

private theorem actual_entry_marker_bounds
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (n : Nat)
    (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (actual : (N).BehavioralAssessment)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (who : Player) (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (original : (app).Control)
    (originalTrace : ((menu).protocol initial horizon scheduler).Trace (some original))
    (atSite : (N).infoOf who originalTrace = site.1) (active : original.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : original.execution.application.SeedRequest who
      ⟨original.execution.application.attempt, event⟩) :
    let replay := (menu).recallReplayPolicy initial horizon scheduler who past (actual.strategy who)
    let selected := Function.update actual.strategy who replay
    let members := fun owner (memory : ((p : Pool) → Parts p) ×
        (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy owner) =>
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) owner memory.2)
          noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded memory.1 owner
    let changed := Function.update members who (fun _ =>
      (app).decodePolicy ((menu).embedPolicy initial horizon scheduler who replay))
    let entryStop := fun history : History =>
      phaseAttemptEntryStop runtime leaks view.application.2.attempt history.state
    let entryLaw := (N).runBehavioralUntil certificate selected entryStop
      ((menu).protocol initial horizon scheduler).initHistory
    let noisy := fun tag : Tag => fun owner => (menu).restrictPolicy initial horizon scheduler
      owner (changed owner (tag.2 owner))
    let zero := fun tag : Tag => Function.update (fun owner =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback
        wellFormed (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n)
          owner (tag.2 owner).2) 0 (by norm_num) (by norm_num) slotWeight slotPositive.le
            slotBounded
            (fun owner => (tag.2 owner).1) owner) who replay
    let stopped := fun history : History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ view.application.2.attempt ∨
          (N).infoOf who history.trace = site.1
    let K := Fintype.card Player * (2 * horizon + 1)
    let a := (1 - noise) ^ K
    let b := (1 + noise / (slotWeight * floor)) ^ K
    ∀ tag : Tag, ∃ marker : (N).InformationHistory who site.1 → ℝ,
      (∀ history, 0 ≤ marker history) ∧
      (∀ history, ∃ records : ∀ owner, List ((N).InfoState owner ×
          ((menu).protocol initial horizon scheduler).Action owner),
        ∃ chance : ℝ, 0 ≤ chance ∧
        (chance ≠ 0 → TracePrefix tag.1.trace history.1.trace ∧
          (∀ owner, (N).ownPlay owner history.1.trace =
            records owner ++ (N).ownPlay owner tag.1.trace) ∧
          (∀ owner record, record ∈ records owner →
            ∃ (before : History)
              (joint : ∀ player, Option (((menu).protocol initial horizon scheduler).Action player))
              (legal : ((menu).protocol initial horizon scheduler).Legal before.state joint)
              (next : ((menu).protocol initial horizon scheduler).State)
              (realized : next ∈ (((menu).protocol initial horizon scheduler).step
                before.state ⟨joint, legal⟩).support),
              TracePrefix tag.1.trace before.trace ∧
              TracePrefix (before.trace.extend joint legal realized) history.1.trace ∧
              (N).infoOf owner before.trace = record.1 ∧ joint owner = some record.2) ∧
          (∀ profile : ∀ owner, (N).BehavioralPolicy owner,
            (((N).runBehavioralFrom profile (history.1.trace.length - tag.1.trace.length)
              tag.1) history.1).toReal =
                chance * ∏ owner, (N).ownPlayReachProbability (profile owner) (records owner))) ∧
          (∀ owner record, record ∈ records owner → record.2.transmission ≠ none →
            phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
              owner record) ∧ marker history = chance *
            ∑ index : (Σ owner, Fin (records owner).length),
              (if index.1 ≠ who ∧ (records index.1)[index.2.val].2.transmission ≠ none
                then phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon
                  scheduler noise index.1 (records index.1)[index.2.val] else 0) *
                ∏ other ∈ Finset.univ.erase index,
                  ((((noisy tag) other.1 (records other.1)[other.2.val].1).map Subtype.val)
                    (some (records other.1)[other.2.val].2)).toReal) ∧
      (tag.1 ∈ entryLaw.support → ∀ history : (N).InformationHistory who site.1,
        a * (((N).runBehavioralUntil certificate (zero tag) stopped tag.1)
          history.1).toReal ≤
          (((N).runBehavioralUntil certificate (noisy tag) stopped tag.1)
          history.1).toReal ∧
        (((N).runBehavioralUntil certificate (noisy tag) stopped tag.1)
          history.1).toReal ≤
          b * (((N).runBehavioralUntil certificate (zero tag) stopped tag.1)
          history.1).toReal +
            marker history) := by
  intro replay selected members changed entryStop entryLaw noisy zero stopped K a b
  let E := (menu).protocol initial horizon scheduler
  let initialFlat := setup.initialLaw.map fun draw =>
    PhaseRuntimeState.initial runtimePlan (encodeInputs draw)
  have initialEq : initial = initialFlat := PMF.map_comp ..
  have originalView := phase_information_control_of_view runtime leaks menu initial horizon
    scheduler
    site past view observed ⟨⟨some original, originalTrace⟩, atSite⟩
  obtain ⟨visible, stateEq, visibleClear, originalAttempt⟩ := originalView
  cases Option.some.inj stateEq
  have originalClear : original.execution.application.current.excluded = ∅ :=
    visibleClear.trans clear
  have genuine := actual_binding_fiber setup mode runtime leaks bounds runtimePlan horizon
    scheduler who site original originalTrace atSite active originalClear event request
  let Good := fun entry : History => ∃ current : (app).Control, entry.state = some current ∧
    ∃ phase remaining, current.execution.application.phases = phase :: remaining ∧
      phase.kind = .commitment ∧ event ∈ phase.events
  have good_of_hit (entry : History) (profile : ∀ owner, (N).BehavioralPolicy owner)
      (entrySupported : entry ∈ entryLaw.support)
      (history : (N).InformationHistory who site.1)
      (supported : history.1 ∈ ((N).runBehavioralUntil certificate profile stopped entry).support) :
      Good entry := by
    obtain ⟨current, stateEq, acting, currentClear, currentRequest⟩ := genuine history
    rcases history with ⟨⟨state, trace⟩, same⟩
    cases stateEq
    apply actual_binding_entry setup mode runtime leaks bounds runtimePlan horizon scheduler
      maximal certificate selected profile who site past view observed current trace same acting
        currentClear event payload binding currentRequest.2.2.1 entry entrySupported
    exact supported
  have profileEq (tag : Tag) := actual_member_profile setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound fallback wellFormed (approximation.sequence n) noise
      noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded who replay tag.2
  have aNonnegative : 0 ≤ a := pow_nonneg (by linarith) _
  have aPositive : 0 < a := pow_pos (by linarith) _
  have aBounded : a ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have bAtLeastOne : 1 ≤ b := one_le_pow₀ (by
    have ratio := div_nonneg noiseNonnegative (mul_pos slotPositive positive).le
    linarith)
  have bNonnegative : 0 ≤ b := le_trans (by norm_num) bAtLeastOne
  let Error := fun tag : Tag => fun history : (N).InformationHistory who site.1 =>
    (N).runBehavioralUntil certificate (noisy tag) stopped tag.1 history.1
  intro tag
  by_cases usable : tag.1 ∈ entryLaw.support ∧ Good tag.1
  · obtain ⟨entrySupported, current, stateEq, phase, remaining, installed, committing, inside⟩ :=
      usable
    rcases tag with ⟨⟨state, entryTrace⟩, memories⟩
    cases stateEq
    have result := actual_supported_marker_bounds setup mode runtime leaks bounds runtimePlan
      horizon scheduler bound maximal fallback wellFormed finite target approximation n capacity
        floor positive floorBounded floored allValues noise noiseNonnegative noiseSmall slotWeight
          slotPositive slotBounded who replay memories certificate site original originalTrace
            atSite active originalClear event request current entryTrace phase remaining installed
              committing inside
    have equality := profileEq (⟨some current, entryTrace⟩, memories)
    change noisy (⟨some current, entryTrace⟩, memories) = _ at equality
    obtain ⟨marker, markerNonnegative, marked, bounded⟩ := result
    refine ⟨marker, markerNonnegative, ?_, ?_⟩
    · intro history
      obtain ⟨records, chance, nonnegative, provenance, bindings, definition⟩ := marked history
      refine ⟨records, chance, nonnegative, provenance, bindings, ?_⟩
      rw [equality]
      exact definition
    · intro _supported history
      have result := bounded history
      rw [equality]
      constructor
      · convert result.1 using 1 <;> congr 5
        all_goals
          funext next
          rcases next with ⟨state, trace⟩
          cases state <;> simp only [stopped, originalAttempt]
      · convert result.2 using 1 <;> congr 5
        all_goals
          funext next
          rcases next with ⟨state, trace⟩
          cases state <;> simp only [stopped, originalAttempt]
  · refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩
    · intro history
      exact ⟨fun _ => [], 0, le_rfl, by simp, by simp, by simp⟩
    · intro entrySupported history
      have absent (profile : ∀ owner, (N).BehavioralPolicy owner) :
          (N).runBehavioralUntil certificate profile stopped tag.1 history.1 = 0 := by
        apply (PMF.apply_eq_zero_iff _ _).mpr
        intro supported
        exact usable ⟨entrySupported, good_of_hit tag.1 profile entrySupported history supported⟩
      simp only [absent, ENNReal.toReal_zero, mul_zero, add_zero, le_refl,
        and_self]


omit [Fintype ((menu).protocol initial horizon scheduler).History]
  [∀ owner, DecidableEq (((menu).information initial horizon scheduler).InfoState owner)] in
private theorem mixture_input_bounds {Index : Type} (law : PMF Index)
    (noisy zero : Index → PMF History) (who : Player) (site : (N).InformationSite who)
    (a b : ℝ) (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (marker : Index → (N).InformationHistory who site.1 → ℝ)
    (nonnegative : ∀ index history, 0 ≤ marker index history)
    (bounded : ∀ index, index ∈ law.support → ∀ history : (N).InformationHistory who site.1,
      a * (zero index history.1).toReal ≤ (noisy index history.1).toReal ∧
      (noisy index history.1).toReal ≤ b * (zero index history.1).toReal + marker index history) :
    ∀ history : (N).InformationHistory who site.1,
      ENNReal.ofReal a * (law.bind zero) history.1 ≤ (law.bind noisy) history.1 ∧
      (law.bind noisy) history.1 ≤ ENNReal.ofReal b * (law.bind zero) history.1 +
        ∑' index, law index * ENNReal.ofReal (marker index history) := by
  classical
  intro history
  have each (index : Index) (supported : index ∈ law.support) := bounded index supported history
  have enn (index : Index) (supported : index ∈ law.support) :
      ENNReal.ofReal a * zero index history.1 ≤ noisy index history.1 ∧
      noisy index history.1 ≤ ENNReal.ofReal b * zero index history.1 +
        ENNReal.ofReal (marker index history) := by
    constructor
    · have lower := ENNReal.ofReal_le_ofReal (each index supported).1
      rw [ENNReal.ofReal_mul aNonnegative] at lower
      simpa only [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)] using lower
    · have upper := ENNReal.ofReal_le_ofReal (each index supported).2
      rw [ENNReal.ofReal_add (mul_nonneg bNonnegative ENNReal.toReal_nonneg)
        (nonnegative _ _), ENNReal.ofReal_mul bNonnegative] at upper
      simpa only [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)] using upper
  simp only [PMF.bind_apply]
  constructor
  · rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro index
    by_cases supported : index ∈ law.support
    · simpa only [mul_assoc, mul_left_comm] using
        mul_le_mul_right (enn index supported).1 (law index)
    · simp only [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul, mul_zero, le_refl]
  · rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro index
    by_cases supported : index ∈ law.support
    · simpa only [mul_add, mul_assoc, mul_left_comm] using
        mul_le_mul_right (enn index supported).2 (law index)
    · simp only [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul, mul_zero, add_zero, le_refl]

open Classical in
/-- The actual common full-input belief is close to the SAME selected noisy
entry/memory law followed by zero-RAW commitment continuations. The error is
its exact mixed foreign RAW-binding path marks, not a refreshed reference.
No positive uniform input-mass floor or source Bayes equality is assumed. -/
theorem phaseTimingPlanPolicy_value_replay_comparison
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (n : Nat) (mixed : (approximation.sequence n).IsFullyMixed)
    (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (actual : (N).BehavioralAssessment)
    (assembled : ∀ who (site : (N).InformationSite who),
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
      actual.strategy who site.1 = ((N).agentBehavior (N).playedInformation fallback
        (fun agent => (weights (pool agent)).bind
          (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
              slotPositive.le
              slotBounded agent))) who site.1)
    (actualMixed : actual.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent (N) actual
      ((menu).decisionInformationAntichain initial horizon scheduler))
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (who : Player) (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (original : (app).Control)
    (originalTrace : ((menu).protocol initial horizon scheduler).Trace (some original))
    (atSite : (N).infoOf who originalTrace = site.1) (active : original.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : original.execution.application.SeedRequest who
      ⟨original.execution.application.attempt, event⟩) :
    let replay := (menu).recallReplayPolicy initial horizon scheduler who past (actual.strategy who)
    let selected := Function.update actual.strategy who replay
    let priors := fun owner => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed
        (approximation.sequence n).strategy owner).map (Prod.mk plan)
    let members := fun owner (memory : ((p : Pool) → Parts p) ×
        (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy owner) =>
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) owner memory.2)
          noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded memory.1 owner
    let changed := Function.update members who (fun _ =>
      (app).decodePolicy ((menu).embedPolicy initial horizon scheduler who replay))
    let posteriors := fun history : History => independentProduct fun owner =>
      ((app).policyMixture (priors owner) (changed owner)).posterior
        ((app).recallAt owner history.state)
    let entryStop := fun history : History =>
      phaseAttemptEntryStop runtime leaks view.application.2.attempt history.state
    let entryLaw := (N).runBehavioralUntil certificate selected entryStop
      ((menu).protocol initial horizon scheduler).initHistory
    let tagLaw := entryLaw.bind fun entry => (posteriors entry).map (Prod.mk entry)
    let noisy := fun tag : Tag => fun owner => (menu).restrictPolicy initial horizon scheduler
      owner (changed owner (tag.2 owner))
    let zero := fun tag : Tag => Function.update (fun owner =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback
        wellFormed (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n)
          owner (tag.2 owner).2) 0 (by norm_num) (by norm_num) slotWeight slotPositive.le
            slotBounded
            (fun owner => (tag.2 owner).1) owner) who replay
    let stopped := fun history : History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ view.application.2.attempt ∨
          (N).infoOf who history.trace = site.1
    let hit := tagLaw.bind fun tag => (N).runBehavioralUntil certificate (noisy tag) stopped tag.1
    let reference := tagLaw.bind fun tag =>
      (N).runBehavioralUntil certificate (zero tag) stopped tag.1
    let D := (N).informationMass selected who site
    let K := Fintype.card Player * (2 * horizon + 1)
    let a := (1 - noise) ^ K
    let b := (1 + noise / (slotWeight * floor)) ^ K
    ∃ marker : Tag → (N).InformationHistory who site.1 → ℝ,
      (∀ tag history, 0 ≤ marker tag history) ∧
      (∀ tag history, ∃ records : ∀ owner, List ((N).InfoState owner ×
          ((menu).protocol initial horizon scheduler).Action owner), ∃ chance : ℝ,
        0 ≤ chance ∧
        (chance ≠ 0 → TracePrefix tag.1.trace history.1.trace ∧
          (∀ owner, (N).ownPlay owner history.1.trace =
            records owner ++ (N).ownPlay owner tag.1.trace) ∧
          (∀ owner record, record ∈ records owner →
            ∃ (before : History)
              (joint : ∀ player, Option (((menu).protocol initial horizon scheduler).Action player))
              (legal : ((menu).protocol initial horizon scheduler).Legal before.state joint)
              (next : ((menu).protocol initial horizon scheduler).State)
              (realized : next ∈ (((menu).protocol initial horizon scheduler).step
                before.state ⟨joint, legal⟩).support),
              TracePrefix tag.1.trace before.trace ∧
              TracePrefix (before.trace.extend joint legal realized) history.1.trace ∧
              (N).infoOf owner before.trace = record.1 ∧ joint owner = some record.2) ∧
          (∀ profile : ∀ owner, (N).BehavioralPolicy owner,
            (((N).runBehavioralFrom profile (history.1.trace.length - tag.1.trace.length)
              tag.1) history.1).toReal =
                chance * ∏ owner, (N).ownPlayReachProbability (profile owner) (records owner))) ∧
        (∀ owner record, record ∈ records owner → record.2.transmission ≠ none →
          phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
            owner record) ∧
        marker tag history = chance * ∑ index : (Σ owner, Fin (records owner).length),
          (if index.1 ≠ who ∧ (records index.1)[index.2.val].2.transmission ≠ none
            then phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler
              noise index.1 (records index.1)[index.2.val] else 0) *
            ∏ other ∈ Finset.univ.erase index,
              ((((noisy tag) other.1 (records other.1)[other.2.val].1).map Subtype.val)
                (some (records other.1)[other.2.val].2)).toReal) ∧
      let error := fun history => ∑' tag, tagLaw tag * ENNReal.ofReal (marker tag history)
      0 < D ∧ (∑' history : (N).InformationHistory who site.1, hit history.1) = D ∧
      (∀ history : (N).InformationHistory who site.1,
        actual.belief who site history = hit history.1 / D) ∧
      (∀ history : (N).InformationHistory who site.1,
        ENNReal.ofReal a * reference history.1 ≤ hit history.1 ∧
        hit history.1 ≤ ENNReal.ofReal b * reference history.1 + error history) ∧
      ((∑' history : (N).InformationHistory who site.1, error history) < D →
        0 < ∑' history : (N).InformationHistory who site.1, (reference history.1).toReal ∧
        (∑' history : (N).InformationHistory who site.1,
          |(actual.belief who site history).toReal - (reference history.1).toReal /
            ∑' other : (N).InformationHistory who site.1, (reference other.1).toReal|) ≤
          2 * ((b - a) / a +
            (∑' history : (N).InformationHistory who site.1, error history).toReal /
              D.toReal)) := by
  classical
  intro replay selected priors members changed posteriors entryStop entryLaw tagLaw noisy zero
    stopped hit reference D K a b
  have aNonnegative : 0 ≤ a := pow_nonneg (by linarith) _
  have aPositive : 0 < a := pow_pos (by linarith) _
  have aBounded : a ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have bAtLeastOne : 1 ≤ b := one_le_pow₀ (by
    have ratio := div_nonneg noiseNonnegative (mul_pos slotPositive positive).le
    linarith)
  have bNonnegative : 0 ≤ b := le_trans (by norm_num) bAtLeastOne
  let Error := fun tag : Tag => fun history : (N).InformationHistory who site.1 =>
    (N).runBehavioralUntil certificate (noisy tag) stopped tag.1 history.1
  have each := actual_entry_marker_bounds setup mode runtime leaks bounds runtimePlan horizon
    scheduler bound maximal fallback wellFormed finite target approximation n capacity floor
      positive floorBounded floored allValues noise noiseNonnegative noiseSmall slotWeight
        slotPositive slotBounded actual certificate who site past view
          observed clear original originalTrace atSite active event payload binding request
  choose marker nonnegative marked bounded using each
  refine ⟨marker, nonnegative, marked, ?_⟩
  intro error
  obtain ⟨ownFactor, _ownPositive, DPositive, _factor, total, belief⟩ :=
    phaseTimingPlanPolicy_value_replay_input_weights setup mode runtime leaks bounds runtimePlan
      horizon scheduler bound maximal fallback wellFormed (approximation.sequence n) mixed finite
        weights noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded actual
          assembled actualMixed bayes certificate who site past view observed clear
  have hitEq : hit = entryLaw.bind fun entry => (posteriors entry).bind fun memories =>
      (N).runBehavioralUntil certificate (noisy (entry, memories)) stopped entry := by
    simp only [hit, tagLaw, PMF.bind_bind, PMF.bind_map]
    rfl
  change (∑' history : (N).InformationHistory who site.1, _) = D at total
  change ∀ history : (N).InformationHistory who site.1, _ = _ / D at belief
  have totalHit : (∑' history : (N).InformationHistory who site.1, hit history.1) = D := by
    rw [hitEq]
    convert total using 1; congr 2
  have beliefHit : ∀ history : (N).InformationHistory who site.1,
      actual.belief who site history = hit history.1 / D := by
    intro history
    rw [hitEq]
    convert belief history using 1; congr 2
  clear total belief
  have total := totalHit
  have belief := beliefHit
  have tagBounds (tag : Tag) (supported : tag ∈ tagLaw.support) :
      ∀ history : (N).InformationHistory who site.1,
        a * (((N).runBehavioralUntil certificate (zero tag) stopped tag.1) history.1).toReal ≤
          (((N).runBehavioralUntil certificate (noisy tag) stopped tag.1) history.1).toReal ∧
        (((N).runBehavioralUntil certificate (noisy tag) stopped tag.1) history.1).toReal ≤
          b * (((N).runBehavioralUntil certificate (zero tag) stopped tag.1) history.1).toReal +
            marker tag history := by
    obtain ⟨entry, entrySupported, rowSupported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨memories, _supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp rowSupported
    cases same
    exact bounded (entry, memories) entrySupported
  have aggregate := mixture_input_bounds setup mode runtime leaks bounds runtimePlan horizon
    scheduler tagLaw
      (fun tag => (N).runBehavioralUntil certificate (noisy tag) stopped tag.1)
      (fun tag => (N).runBehavioralUntil certificate (zero tag) stopped tag.1)
      who site a b aNonnegative bNonnegative marker nonnegative tagBounds
  refine ⟨DPositive, total, belief, aggregate, ?_⟩
  have Dfinite : D ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((N).informationMass_le_one selected who site
      ((menu).decisionInformationAntichain initial horizon scheduler who site))
  exact conditional_input_weights setup mode runtime leaks bounds runtimePlan horizon scheduler
    who site (actual.belief who site) hit reference D DPositive Dfinite total belief a b
      aPositive aBounded bAtLeastOne error aggregate

end Vegas
