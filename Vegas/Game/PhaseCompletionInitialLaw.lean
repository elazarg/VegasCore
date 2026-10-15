/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCanonicalCompletion
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Compile.EventGraphInputs
import Vegas.EventGraph.PrivateInputs

/-! # Original setup parameters in completed physical outcomes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement Filter

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- On an actual history initialized at a fixed source draw, complete typed
readout recovers precisely that original draw. This uses immutable input cells,
not an injectivity assumption or a conclusion about mixed marginal laws. -/
theorem phaseSourceReadout_initialState_eq_of_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (initial : State L setup.context)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (PMF.pure (PhaseRuntimeState.initial plan (setup.eventInputs initial)))
        horizon scheduler).Trace (some current))
    (terminal : State L setup.program.terminalCtx)
    (decoded : phaseSourceReadout setup mode runtime leaks (some current) = some terminal) :
    initialState setup.program terminal = initial := by
  have valid := (phaseApplication_invariant runtime leaks (setup.eventInputs initial)).history
    (PMF.pure (PhaseRuntimeState.initial plan (setup.eventInputs initial))) horizon scheduler
    (fun state member => by
      cases (PMF.mem_support_pure_iff _ _).mp member
      exact PhaseRuntimeState.settle_invariant _ _ _ _ _
        (EventGraphRuntime.State.initial_invariant _) (EventGraphRuntime.State.initial_invariant _))
    trace
  have inputs := valid.active.reachable.inputs_eq
  have sourceDecoded : decodeState? (terminalRefs setup.program)
      current.execution.application.current.native.config.store = some terminal := by
    unfold phaseSourceReadout at decoded
    simp only [Option.bind_some] at decoded
    split at decoded
    · exact decoded
    · cases decoded
  have first : (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees
      (initialState setup.program terminal)
        current.execution.application.current.native.config.store :=
    terminalRefsWith_initial_agrees setup.program _ _ _ terminal
      (decodeState?_agrees _ _ _ sourceDecoded)
  have second : (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees initial
      current.execution.application.current.native.config.store := by
    apply ContextRefs.initial_agrees
    intro input
    change some (current.execution.application.current.native.config.inputs input) = _
    rw [inputs]
    rfl
  funext name cell ref
  have same := Option.some.inj ((first ref).symm.trans (second ref))
  cases cell <;> exact same

private theorem source_initial_map
    (setup : Setup (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile setup.program) {Outcome : Type}
    (readout : State L setup.context → State L setup.program.terminalCtx → Outcome) :
    (setup.initialLaw.bind (SourceProgram.run setup.program profile)).map
      (fun terminal => readout (initialState setup.program terminal) terminal) =
      setup.initialLaw.bind (fun initial =>
        (SourceProgram.run setup.program profile initial).map (readout initial)) := by
  rw [PMF.map_bind]
  apply bind_congr_on_support
  intro initial _
  apply map_congr_on_support
  intro terminal supported
  rw [initialState_runFrom setup.program profile
    ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩ terminal supported]

variable [Fintype Player]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat)
  (scheduler : (phaseApplication (serviceRuntime setup mode deadline) leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (sourceLimit : setup.commitRecoveryModel.BehavioralAssessment)
  (sourceConvergence : BehavioralAssessmentConvergesPointwise sourceSequence sourceLimit)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source sourceLimit.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (sourceLimit.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)

local notation "R" => serviceRuntime setup mode deadline
local notation "app" => phaseApplication R leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu R leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu R leaks bounds) (start) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu R leaks bounds) (start) horizon scheduler
local notation "canonical" => phaseSourceStrategy setup mode R leaks bounds wellFormed
  sourceLimit (start) horizon scheduler
local notation "structural" => setup.decodeBehavioralProfile
  (CommitmentInterface.values setup.program) (setup.openingExtension source)

variable (delay bound : (serviceGraph setup mode).EventId → Nat)
  (asyncService : PhaseService.AsyncContract (serviceRuntime setup mode deadline) leaks
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler delay bound)
  (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
  (values : ∀ event who payload,
    ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

include maximal capacity sourceConvergence copies continuing asyncService timely values

open Classical in
/-- The same completed sequence and limit preserve the original setup draw
jointly with typed source readout and realized settlement. The tag is recovered
from the immutable source cells; no unencoded tag is inferred from a marginal. -/
theorem exists_phase_source_completion_with_initial_law
    [Finite (E).History]
    (noise : ℕ → ℝ) (positive : ∀ n, 0 < noise n) (small : ∀ n, noise n < 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff deposit : Player → ℝ)
    (report : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup mode))) :
    let certificate := ((menu).bounded (start) horizon scheduler).wellFoundedHistories
    let payoff := fun who (final : (E).History) =>
      phaseExclusionBase setup mode R leaks utility excludedPayoff final.state who
    ∃ (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n who (site : (N).InformationSite who),
        ¬ PhasePublicExclusion setup mode R leaks site.1 →
          (sequence n).strategy who site.1 =
            phaseSourcePerturbedStrategy setup mode R leaks bounds (start) horizon scheduler
              wellFormed (sourceSequence n) (noise n) (positive n).le (small n).le
                (slotWeight n) (slotNonnegative n) (slotBounded n) who site.1) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent (N) (sequence n)
        ((menu).decisionRecall (start) horizon scheduler).decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent
        ((menu).decisionRecall (start) horizon scheduler).decisionInformationAntichain ∧
      (∀ who (site : (N).InformationSite who),
        PhasePublicExclusion setup mode R leaks site.1 →
          ∀ alternative : (N).BehavioralPolicy who,
            (limit.continuationContext certificate site (payoff who)).value alternative ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who)) ∧
      (N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory =
        (N).runBehavioralTerminalFrom certificate canonical (E).initHistory ∧
      ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).map
        (fun final => ((phaseSourceReadout setup mode R leaks final.state).map
          (initialState setup.program), phaseSourceReadout setup mode R leaks final.state)) =
        setup.initialLaw.bind (fun initial =>
          (SourceProgram.run setup.program structural initial).map
            (fun terminal => (some initial, some terminal))) ∧
      ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).map
        (fun final => ((phaseSourceReadout setup mode R leaks final.state).map
          (initialState setup.program), phaseSourceReadout setup mode R leaks final.state,
            phaseExclusionBase setup mode R leaks utility excludedPayoff final.state)) =
        setup.initialLaw.bind (fun initial =>
          (SourceProgram.run setup.program structural initial).map
            (fun terminal => (some initial, some terminal, utility terminal))) ∧
      ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).bind
        (fun final =>
          (TerminalAudit.settlement (phaseExclusionBase setup mode R leaks utility excludedPayoff)
            (app).stateTraffic (PhaseCount.audit R leaks report.sample) deposit final.state).map
              (fun payoffs => ((phaseSourceReadout setup mode R leaks final.state).map
                (initialState setup.program), phaseSourceReadout setup mode R leaks final.state,
                  payoffs))) =
        setup.initialLaw.bind (fun initial =>
          (SourceProgram.run setup.program structural initial).map
            (fun terminal => (some initial, some terminal, utility terminal))) ∧
      ∀ final ∈ ((N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory).support,
        ∃ current : (app).Control, final.state = some current ∧
          current.execution.application.current.excluded = ∅ ∧
          ∀ who, TerminalAudit.charge (app).stateTraffic
            (PhaseCount.audit R leaks report.sample) final.state who = 0 := by
  intro certificate payoff
  obtain ⟨sequence, limit, index, recipe, mixed, bayes, increasing, converges, consistent,
      optimal, historyLaw, readoutLaw, payoffLaw, settlementLaw, clean⟩ :=
    exists_phase_source_completion_with_source_law setup mode deadline leaks bounds wellFormed
      source plan maximal horizon scheduler capacity sourceSequence sourceLimit sourceConvergence
        copies continuing delay bound asyncService timely values noise positive small vanishes
          slotWeight slotNonnegative slotBounded slotVanishes utility excludedPayoff deposit report
  refine ⟨sequence, limit, index, recipe, mixed, bayes, increasing, converges, consistent,
    optimal, historyLaw, ?_, ?_, ?_, clean⟩
  · have tagged := congrArg (PMF.map (fun result : Option (State L setup.program.terminalCtx) =>
        (result.map (initialState setup.program), result))) readoutLaw
    simp only [PMF.map_comp, Function.comp_def, Option.map_some] at tagged
    rw [source_initial_map setup structural (fun initial terminal =>
      (some initial, some terminal))] at tagged
    exact tagged
  · have tagged := congrArg (PMF.map (fun result :
        Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
          (result.1.map (initialState setup.program), result.1, result.2))) payoffLaw
    simp only [PMF.map_comp, Function.comp_def, Option.map_some] at tagged
    rw [source_initial_map setup structural (fun initial terminal =>
      (some initial, some terminal, utility terminal))] at tagged
    exact tagged
  · have tagged := congrArg (PMF.map (fun result :
        Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
          (result.1.map (initialState setup.program), result.1, result.2))) settlementLaw
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some] at tagged
    have initialized := source_initial_map setup structural (fun initial terminal =>
      (some initial, some terminal, utility terminal))
    rw [PMF.map_bind] at initialized
    exact tagged.trans initialized

end Vegas
