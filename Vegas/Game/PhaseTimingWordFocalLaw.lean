/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPlanWordChannel
import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.ConditionalObservation

/-! # Actual focal full-input channels of original complete source-word profiles -/

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

/-- Restrict the globally menu-legal member policies to the actual original
finite game. Every owner uses the SAME original timing plan and its own word. -/
def phaseTimingWordPlanProfile {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (words : (who : Player) → DecisionView who Δ) :
    (who : Player) → (N).BehavioralPolicy who := fun who =>
  (menu).restrictPolicy initial horizon scheduler who
    (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
      fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
        parts who (words who))

open Classical in
/-- The actual original finite game is played from its full entry history
until exclusion, commitment exit or the specified focal callback. The absent
result includes stopped exits and nonactive terminal controls. -/
def phaseTimingWordFocalLaw {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (words : (who : Player) → DecisionView who Δ)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (certificate : (E).WellFoundedHistories) (focal : Player) (wanted : (N).InfoState focal)
    (entry : (E).History) : PMF ((N).InfoState focal) :=
  let exits : (E).History → Prop := fun history => match history.state with
    | none => True
    | some control => control.execution.application.current.excluded ≠ ∅ ∨
        control.execution.application.phases ≠ phase :: remaining
  let stopped : (E).History → Prop := fun history => exits history ∨
    ((app).actor history.state = some focal ∧ (N).infoOf focal history.trace = wanted)
  ((N).runBehavioralUntil certificate
    (phaseTimingWordPlanProfile setup mode runtime leaks bounds plan horizon scheduler bound
      fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
        parts words) stopped entry).map fun history =>
    @ite _ (exits history) (Classical.propDecidable (exits history)) none
      ((N).infoOf focal history.trace)

include maximal

open Classical in
/-- A single foreign complete-word change preserves the entire actual focal
input law, under the original finite profile and full entry history. -/
theorem phaseTimingWordFocalLaw_update_foreign
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (words : (who : Player) → DecisionView who Δ) (owner : Player)
    (replacement : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (app).Control) (entry : (E).History) (current : entry.state = some control)
    (clear : control.execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : control.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (certificate : (E).WellFoundedHistories) (focal : Player) (different : focal ≠ owner)
    (wanted : (N).InfoState focal) :
    phaseTimingWordFocalLaw setup mode runtime leaks bounds plan horizon scheduler bound fallback
      wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative slotBounded
        parts words phase remaining certificate focal wanted entry =
    phaseTimingWordFocalLaw setup mode runtime leaks bounds plan horizon scheduler bound fallback
      wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative slotBounded
        parts (Function.update words owner replacement) phase remaining certificate focal wanted
          entry := by
  classical
  let profile := phaseTimingWordPlanProfile setup mode runtime leaks bounds plan horizon scheduler
    bound fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
      slotBounded parts words
  have changed : GameTheory.Profile.update (sig := (N).behavioralSignature) profile owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded parts owner replacement)) =
      phaseTimingWordPlanProfile setup mode runtime leaks bounds plan horizon scheduler bound
        fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
          slotBounded parts (Function.update words owner replacement) := by
    funext who info
    by_cases same : who = owner
    · subst who
      simp only [GameTheory.Profile.update_same, phaseTimingWordPlanProfile, Function.update_self]
    · simp only [GameTheory.Profile.update, Function.update_of_ne same, profile,
        phaseTimingWordPlanProfile]
  have original : GameTheory.Profile.update (sig := (N).behavioralSignature) profile owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low 0 slotWeight slotNonnegative
            slotBounded parts owner (words owner))) = profile :=
    GameTheory.Profile.update_eq_self _ _
  have channel := phase_timing_plan_word_channel_of_history setup mode runtime leaks bounds plan
    maximal horizon scheduler bound finite wellFormed target approximation n fallback parts profile
      owner block low (words owner) replacement slotWeight slotNonnegative slotBounded control entry
        current clear phase remaining installed committing lower upper values capacity certificate
          focal different wanted
  dsimp only at channel
  rw [original, changed] at channel
  have projected := congrArg
    (PMF.map (fun observed => observed.bind fun row => row.2.2.2.2.2)) channel
  simp only [PMF.map_comp, Function.comp_def] at projected
  have flatten (history : (E).History) :
      ((if (match history.state with
          | none => True
          | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
              actual.execution.application.phases ≠ phase :: remaining) then none else
        history.state.map fun actual : (app).Control =>
          (actual.remaining, actual.actor, phaseExternalObservation runtime leaks owner
            actual.execution,
            phaseOperationalView runtime leaks (actual.execution.observe app owner),
            (actual.execution.recall owner).map (fun record : (app).PlayerEntry =>
              (phaseOperationalView runtime leaks record.beforeView, record.emitted)),
            (N).infoOf focal history.trace)).bind fun row => row.2.2.2.2.2) =
        if (match history.state with
          | none => True
          | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
              actual.execution.application.phases ≠ phase :: remaining) then none else
          (N).infoOf focal history.trace := by
    by_cases exits : match history.state with
      | none => True
      | some actual => actual.execution.application.current.excluded ≠ ∅ ∨
          actual.execution.application.phases ≠ phase :: remaining
    · simp only [exits, ite_true, Option.bind_none]
    · have nonempty : history.state ≠ none := by
        intro absent
        apply exits
        simp only [absent]
      obtain ⟨actual, state⟩ := Option.ne_none_iff_exists'.mp nonempty
      have notExit : ¬(actual.execution.application.current.excluded ≠ ∅ ∨
          actual.execution.application.phases ≠ phase :: remaining) := by
        simpa only [state] using exits
      simp only [state, notExit, ite_false, Option.map_some, Option.bind_some]
  exact (map_congr_on_support _ (fun history _ => flatten history)).symm.trans
    (projected.trans (map_congr_on_support _ (fun history _ => flatten history)))

end Vegas
