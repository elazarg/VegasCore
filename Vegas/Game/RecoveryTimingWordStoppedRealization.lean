/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryTimingWordCallback
import Interaction.ReactiveMixtureSupport
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import Vegas.Pending.PhaseClearHistory
import Vegas.Pending.PhaseBindingMemoryCallback
import Interaction.ReactiveAnchoredMixture
import Vegas.Game.RecoveryFixedCommitGeometry
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingReadiness

/-! # Actual stopped physical laws from anchored complete source words -/

noncomputable section

namespace Vegas

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
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial runtimePlan)
variable [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).InfoState who)]

local notation "N" => ReactiveApplication.ResponseMenu.information (menu) initial horizon scheduler
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

local instance timingWordStoppedRealizationPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- The existing stopped physical runner under the original anchored complete
word implementations has the SAME law as the actual zero-RAW timing strategy,
against an arbitrary focal intervention. The entire entry history is retained. -/
theorem RecoverySourceCheckpoint.timing_word_anchored_stopped_law
    {anchor : (app).Control}
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (clearEntry : anchor.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point,
      (residual owner).protocolAction checkpoint.residual.tail
          (ProtocolState.observe owner checkpoint.residual.tail point) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (some (ProtocolState.observe owner setup.program
              (checkpoint.residual.lift point))))).map
                (fun choice => CommitRecoveryMove.underlying choice.1))
    {Ξ : SourceCtx Player L} {Q : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (positive : 0 < block.length) (boundary : IsCommitBoundary suffix)
    (fallback : (who : Player) → (N).Policy who)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (entryFresh : ∀ owner, ∀ record ∈ anchor.execution.recall owner,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (extra : ((menu).protocol initial horizon scheduler).History → Prop) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let wordLaw := block.prefixLaw suffix typed checkpoint.source
    let priors := fun owner => (independentProduct weights).bind fun plan =>
      (wordLaw.map (SourceProgram.Config.view owner)).map (Prod.mk plan)
    let members := fun owner (memory : ((p : Pool) → Parts p) × DecisionView owner Ξ) =>
      ReactiveApplication.anchoredPolicy anchor.execution
        (fun _ => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
          scheduler
          bound fallback wellFormed assessment block anchor.execution.application.attempt.phase
            anchor.execution.application.generation slotWeight slotNonnegative slotBounded
              memory.1 owner memory.2) owner
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound
        agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative
            slotBounded agent))
    let focalPolicy := (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal
      intervention)
    let players := Function.update (fun who => ((app).policyMixture (priors who)
      (members who)).policy) focal focalPolicy
    let first := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      extra history ∨ match history.state with
        | none => True
        | some current => current.execution.application.current.excluded ≠ ∅ ∨
            current.execution.application.phases ≠ phase :: remaining
    (N).runBehavioralUntil certificate first stopped ⟨some anchor, anchorTrace⟩ =
      (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) profile focal intervention) stopped
          ⟨some anchor, anchorTrace⟩ := by
  intro typed wordLaw priors members profile focalPolicy players first stopped
  let target := Function.update ((menu).decodeProfile initial horizon scheduler profile)
    focal focalPolicy
  let second := fun who => (menu).restrictPolicy initial horizon scheduler who (target who)
  let predicate := fun execution : (app).Execution => ∀ who, who ≠ focal →
    (((app).policyMixture (priors who) (members who)).policy).Consistent (execution.recall who)
  have membersCovered (who : Player) (memory : ((p : Pool) → Parts p) × DecisionView who Ξ) :
      ∀ past view action, action ∈ (members who memory past view).support →
        action ∈ (menu).actions who past view := by
    exact (menu).anchoredPolicy_covered initial horizon scheduler anchor anchorTrace _ who
      (fun past view action supported => (menu).decode_embedPolicy_covered initial horizon
        scheduler who _ past view action supported)
  have covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (menu).actions who past view := by
    intro who past view action supported
    by_cases own : who = focal
    · subst who
      simp only [players, Function.update_self] at supported
      exact (menu).decode_embedPolicy_covered initial horizon scheduler focal intervention
        past view action supported
    · simp only [players, Function.update_of_ne own,
        ReactiveApplication.policyMixture_policy] at supported
      obtain ⟨memory, _present, chosen⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      exact membersCovered who memory past view action chosen
  have invariant : (app).PolicyInvariant players predicate := by
    constructor
    · intro execution actor action faithful supported who foreign
      by_cases active : who = actor
      · subst actor
        have sampled : action ∈
            (((app).policyMixture (priors who) (members who)).policy
              (execution.recall who) (execution.observe (app) who)).support := by
          simpa only [players, Function.update_of_ne foreign] using supported
        obtain ⟨emitted, recalled⟩ := (app).respond_recall_entry execution who action
        rw [recalled]
        exact .snoc _ (faithful who foreign) sampled
      · rw [(app).respond_recall_other execution actor who active action]
        exact faithful who foreign
    · intro execution next command faithful reached who foreign
      rw [(app).environmentStep_recall execution next command reached]
      exact faithful who foreign
  have initialFaithful : predicate anchor.execution := by
    intro who _foreign
    obtain ⟨memory, present⟩ := (priors who).support_nonempty
    exact ((app).policyMixture_consistent_of_supported_member (priors who) (members who)
      memory present (anchor.execution.recall who)
        (ReactiveApplication.anchoredPolicy_consistent anchor.execution _ who)).1
  let E := (menu).protocol initial horizon scheduler
  let related := fun left right : E.History => left = right ∧
    TracePrefix anchorTrace left.trace ∧ ReactiveApplication.executionInvariant predicate left.state
  have callbacks : ∀ history : E.History, TracePrefix anchorTrace history.trace →
      ReactiveApplication.executionInvariant predicate history.state → ¬ stopped history →
      ∀ who, first who ((N).infoOf who history.trace) =
        second who ((N).infoOf who history.trace) := by
    rintro ⟨state, history⟩ kept faithful running who
    cases state with
    | none => exact (running (Or.inr trivial)).elim
    | some current =>
      have clear : current.execution.application.current.excluded = ∅ := by
        by_contra bad
        exact running (Or.inr (Or.inl bad))
      have installedCurrent : current.execution.application.phases = phase :: remaining := by
        by_contra bad
        exact running (Or.inr (Or.inr bad))
      have anchorGeneration := (phase_clear_history runtime leaks runtimePlan inputs horizon
        scheduler anchor ((menu).toRawTrace initial horizon scheduler anchorTrace) clearEntry).1
      have currentGeneration := (phase_clear_history runtime leaks runtimePlan inputs horizon
        scheduler current ((menu).toRawTrace initial horizon scheduler history) clear).1
      have same : anchor.execution.application.attempt = current.execution.application.attempt := by
        simp only [PhaseRuntimeState.attempt, installed, installedCurrent, List.head?_cons,
          Option.map_some, Option.getD_some, anchorGeneration, currentGeneration]
      let currentCheckpoint := checkpoint.transfer_of_same_attempt_prefix runtime leaks runtimePlan
        inputs horizon scheduler (menu) anchor current anchorTrace history kept same
      have observed := (menu).info initial horizon scheduler who history
      change (N).infoOf who history = (app).observe who (some current) at observed
      by_cases active : current.actor = some who
      · have info : (N).infoOf who history = some (current.execution.recall who,
            current.execution.observe (app) who) := by
          simpa only [ReactiveApplication.observe, active, ite_true] using observed
        rw [info]
        by_cases own : who = focal
        · subst who
          simp only [first, second, players, target, Function.update_self]
        · have freshCurrent : ∀ record ∈ anchor.execution.recall who,
              record.beforeView.application.2.attempt ≠ current.execution.application.attempt := by
            simpa only [← same] using entryFresh who
          have response := RecoverySourceCheckpoint.timing_word_anchored_policy_at_callback setup
            mode runtime leaks bounds runtimePlan inputs horizon scheduler bound history maximal
              clear currentCheckpoint wellFormed assessment residual raw block suffix reconstruct
                phase remaining installedCurrent positive boundary who active fallback slotWeight
                  slotNonnegative slotBounded weights capacity values anchor anchorTrace
                    freshCurrent
          have compatible :
              (((app).policyMixture (priors who) (members who)).policy).Consistent
                (current.execution.recall who) := faithful who own
          have law : players who (current.execution.recall who)
                (current.execution.observe (app) who) =
              target who (current.execution.recall who) (current.execution.observe (app) who) := by
            simp only [players, target, Function.update_of_ne own]
            have offset := congrArg CommitAttemptId.phase same
            have generation := congrArg CommitAttemptId.generation same
            change anchor.execution.application.generation =
              current.execution.application.generation at generation
            rw [← offset, ← generation] at response
            change ((((app).policyMixture (priors who) (members who)).policy).Consistent
                (current.execution.recall who) →
              (((app).policyMixture (priors who) (members who)).policy)
                (current.execution.recall who) (current.execution.observe (app) who) =
              ((menu).decodeProfile initial horizon scheduler profile) who
                (current.execution.recall who) (current.execution.observe (app) who)) at response
            exact response compatible
          change (menu).restrictPolicy initial horizon scheduler who (players who)
              (some (current.execution.recall who, current.execution.observe (app) who)) =
            (menu).restrictPolicy initial horizon scheduler who (target who)
              (some (current.execution.recall who, current.execution.observe (app) who))
          apply pmf_map_injective Subtype.val_injective
          rw [(menu).restrictPolicy_map_val initial horizon scheduler who (players who) _ _
            (covered who _ _),
            (menu).restrictPolicy_map_val initial horizon scheduler who (target who) _ _
              (fun action supported => covered who _ _ action (law.symm ▸ supported))]
          exact congrArg (PMF.map some) law
      · have info : (N).infoOf who history = none := by
          simpa only [ReactiveApplication.observe, active, ite_false] using observed
        rw [info]
        rfl
  have step : ∀ left right, related left right → ¬ stopped left → ¬ E.terminal left.state →
      ∃ joint : PMF (E.History × E.History),
        joint.map Prod.fst = (N).runBehavioralFrom first 1 left ∧
        joint.map Prod.snd = (N).runBehavioralFrom second 1 right ∧
        ∀ next ∈ joint.support, related next.1 next.2 := by
    rintro left right ⟨rfl, kept, faithful⟩ running notTerminal
    have agree := (N).behavioralJoint_congr left.trace notTerminal
      (callbacks left kept faithful running)
    have laws : (N).runBehavioralFrom first 1 left = (N).runBehavioralFrom second 1 left := by
      rw [(N).runBehavioralFrom_succ_of_not_terminal first 0 notTerminal,
        (N).runBehavioralFrom_succ_of_not_terminal second 0 notTerminal, agree]
      rfl
    refine ⟨((N).runBehavioralFrom first 1 left).map (fun next => (next, next)), ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      exact PMF.map_id _
    · rw [PMF.map_comp]
      exact (PMF.map_id _).trans laws
    · intro pair member
      obtain ⟨next, actual, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
      have nextFaithful : ReactiveApplication.executionInvariant predicate next.state := by
        have mapped := (menu).run_restrict_control_steps initial horizon scheduler players
          ((menu).admissible_of_covered initial horizon scheduler players covered) 1 left
        simp only [Function.iterate_one, PMF.pure_bind] at mapped
        have supported : next.state ∈
            (((N).runBehavioralFrom first 1 left).map History.state).support :=
          (PMF.mem_support_map_iff ..).mpr ⟨next, actual, rfl⟩
        rw [mapped] at supported
        exact invariant.controlStep initial horizon scheduler (fun _ _ _ _ => .nil)
          left.state next.state faithful supported
      rw [(N).runBehavioralFrom_succ_of_not_terminal first 0 notTerminal,
        PMF.mem_support_bind_iff] at actual
      obtain ⟨draw, _chosen, extended⟩ := actual
      rw [PMF.mem_support_bindOnSupport_iff] at extended
      obtain ⟨targetState, realized, finished⟩ := extended
      change next ∈ (PMF.pure _).support at finished
      cases (PMF.mem_support_pure_iff _ _).mp finished
      exact ⟨rfl, .extend kept draw.1 draw.2 realized, nextFaithful⟩
  have result := (N).runBehavioralUntil_map_eq_of_paired_steps (N) certificate certificate
    first second stopped stopped id id related (by rintro _ _ ⟨rfl, _⟩; rfl)
      (by rintro _ _ ⟨rfl, _⟩ _; rfl) step
      ⟨some anchor, anchorTrace⟩ ⟨some anchor, anchorTrace⟩ ⟨rfl, .refl, initialFaithful⟩
  have original : second = Profile.update (sig := (N).behavioralSignature) profile focal
      intervention := by
    funext who
    by_cases own : who = focal
    · subst who
      simp only [second, target, Function.update_self, Profile.update_same]
      exact (menu).restrict_decode_embedPolicy initial horizon scheduler focal intervention
    · simp only [second, target, Function.update_of_ne own, Profile.update_of_ne _ _ own]
      exact (menu).restrict_decode_embedPolicy initial horizon scheduler who (profile who)
  rw [← original]
  simpa only [PMF.map_id] using result

end Vegas
