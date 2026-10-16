/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPlanStoppedLaw

/-! # Original word-independent operational channels from authentic full entries -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

include maximal

open Classical in
/-- At one authentic full entry, every latent owner word has the SAME complete
stopped operational channel under one original timing plan. Empty memory is
instantiated internally and all subsequent no-fresh updates are derived. -/
theorem phase_timing_plan_word_channel_of_history
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p)
    (opponents : (who : Player) → (N).BehavioralPolicy who) (owner : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (firstWord secondWord : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (app).Control) (history : (E).History)
    (current : history.state = some control)
    (clear : control.execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : control.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (certificate : (E).WellFoundedHistories) (focal : Player) (different : focal ≠ owner)
    (wanted : (N).InfoState focal) :
    let firstProfile := GameTheory.Profile.update (sig := (N).behavioralSignature) opponents owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight
            slotNonnegative slotBounded parts owner firstWord))
    let secondProfile := GameTheory.Profile.update (sig := (N).behavioralSignature) opponents owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight
            slotNonnegative slotBounded parts owner secondWord))
    let exits : (E).History → Prop := fun history => match history.state with
      | none => True
      | some control => control.execution.application.current.excluded ≠ ∅ ∨
          control.execution.application.phases ≠ phase :: remaining
    let stopped : (E).History → Prop := fun history => exits history ∨
      ((app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted)
    let readout := fun history : (E).History =>
      @ite _ (exits history) (Classical.propDecidable (exits history)) none
        (history.state.map fun control =>
        (control.remaining, control.actor,
          phaseExternalObservation runtime leaks owner control.execution,
          phaseOperationalView runtime leaks (control.execution.observe app owner),
          (control.execution.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)),
          (N).infoOf focal history.trace))
    ((N).runBehavioralUntil certificate firstProfile stopped history).map readout =
      ((N).runBehavioralUntil certificate secondProfile stopped history).map readout := by
  classical
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have counted : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact current ▸ history.trace
  have zero : control.execution.application.generation = 0 :=
    (phase_clear_history runtime leaks plan inputs horizon scheduler control
      ((menu).toRawTrace _ horizon scheduler counted) clear).1
  have address : control.execution.application.attempt = ⟨low, 0⟩ := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some, lower, zero]
  exact phase_timing_plan_stopped_word_law setup mode runtime leaks bounds plan maximal horizon
    scheduler bound finite wellFormed target approximation n fallback parts opponents owner block
      low 0 firstWord secondWord slotWeight slotNonnegative slotBounded control control history
        history current current rfl rfl BindingShadow.empty (BindingShadow.ownBindings_empty owner)
          (BindingShadow.empty_candidates_not_fresh) (BindingShadow.phased_empty owner _).symm
            rfl rfl rfl (fun _ _ => rfl) rfl clear phase remaining committing lower upper
              values capacity address certificate focal different wanted

end Vegas
