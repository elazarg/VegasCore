/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPlanActorCoupling
import Vegas.Pending.PhaseBindingStoppedCommandCoupling

/-! # Actual control-step laws of one finite timing plan under hidden word changes -/

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

/-- Both original complete control-step laws have a concrete coupling. The
physical memory is derived on clear branches; first exclusion is paired as an exit. -/
theorem phase_timing_plan_control_word_coupling
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p)
    (opponents : Player → (app).Policy) (owner : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (firstWord secondWord : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (left right : (app).Control)
    (leftTrace : (E).Trace (some left)) (rightTrace : (E).Trace (some right))
    (sameRemaining : left.remaining = right.remaining) (sameActor : left.actor = right.actor)
    (running : ¬(left.remaining = 0 ∧ left.actor = none))
    (memory : BindingShadow (graph)) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.execution.application = memory.phased owner right.execution.application)
    (network : left.execution.network = right.execution.network)
    (receipts : left.execution.receipts = right.execution.receipts)
    (service : left.execution.environmentRecall = right.execution.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.execution.recall who = right.execution.recall who)
    (past : (left.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (clear : right.execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : right.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (address : right.execution.application.attempt = ⟨low, generation⟩) :
    ∃ paired : PMF ((app).ProtocolState × (app).ProtocolState),
      paired.map Prod.fst = (app).controlStep initial horizon scheduler
        (Function.update opponents owner (phaseTimingWordPlanPolicy setup mode runtime leaks bounds
          initial horizon scheduler bound fallback wellFormed (approximation.sequence n) block low
            generation slotWeight slotNonnegative slotBounded parts owner firstWord)) (some left) ∧
      paired.map Prod.snd = (app).controlStep initial horizon scheduler
        (Function.update opponents owner (phaseTimingWordPlanPolicy setup mode runtime leaks bounds
          initial horizon scheduler bound fallback wellFormed (approximation.sequence n) block low
            generation slotWeight slotNonnegative slotBounded parts owner secondWord))
              (some right) ∧
      ∀ pair ∈ paired.support, ∃ count actor first second,
        pair = (some ⟨count, actor, first⟩, some ⟨count, actor, second⟩) ∧
        ((first.application.current.excluded ≠ ∅ ∧ second.application.current.excluded ≠ ∅) ∨
          ∃ nextMemory : BindingShadow graph,
            nextMemory.OwnBindings owner ∧
            (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
            first.application = nextMemory.phased owner second.application ∧
            first.network = second.network ∧ first.receipts = second.receipts ∧
            first.environmentRecall = second.environmentRecall ∧
            (∀ who, who ≠ owner → first.recall who = second.recall who) ∧
            (first.recall owner).map (fun entry =>
                (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
              (second.recall owner).map (fun entry =>
                (phaseOperationalView runtime leaks entry.beforeView, entry.emitted))) := by
  classical
  let firstPlayers := Function.update opponents owner (phaseTimingWordPlanPolicy setup mode
    runtime leaks bounds initial horizon scheduler bound fallback wellFormed
      (approximation.sequence n) block low generation slotWeight slotNonnegative slotBounded parts
        owner firstWord)
  let secondPlayers := Function.update opponents owner (phaseTimingWordPlanPolicy setup mode
    runtime leaks bounds initial horizon scheduler bound fallback wellFormed
      (approximation.sequence n) block low generation slotWeight slotNonnegative slotBounded parts
        owner secondWord)
  rcases left with ⟨firstCount, firstActor, first⟩
  rcases right with ⟨secondCount, secondActor, second⟩
  dsimp only at sameRemaining sameActor
  subst secondCount
  subst secondActor
  change second.application.phases = phase :: remaining at installed
  have before : first.observeEnvironment app = second.observeEnvironment app := by
    change (⟨first.network.publicView, first.application.publicView, first.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application, BindingShadow.phased_publicView owned]
    rfl
  cases firstActor with
  | none =>
      cases firstCount with
      | zero => exact (running ⟨rfl, rfl⟩).elim
      | succ count =>
          let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
          have countedLeft : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan))
              horizon scheduler).Trace (some ⟨count + 1, none, first⟩) := by
            dsimp only [inputs]
            rw [PMF.map_comp]
            exact leftTrace
          have countedRight : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan))
              horizon scheduler).Trace (some ⟨count + 1, none, second⟩) := by
            dsimp only [inputs]
            rw [PMF.map_comp]
            exact rightTrace
          have opaquePhase : ∀ current ∈ second.application.phases.head?,
              current.kind = .commitment := by
            intro current present
            have same : current = phase := by
              simpa only [installed, List.head?_cons, Option.mem_def, Option.some.injEq]
                using present.symm
            subst current
            exact committing
          let choices := scheduler first.environmentRecall (first.observeEnvironment app)
          have available (command : (app).Command) (selected : command ∈ choices.support) :=
            BindingShadow.environment_command_stopped_coupling runtime leaks bounds plan inputs
              horizon scheduler count first second countedLeft countedRight memory owner owned
                valid application network receipts service recalled
                  (phaseOperationalView runtime leaks) past clear opaquePhase command selected
          let image (command : (app).Command) (pair : (app).Execution × (app).Execution) :
              (app).ProtocolState × (app).ProtocolState :=
            (some ⟨count, command.actor? app, pair.1⟩,
              some ⟨count, command.actor? app, pair.2⟩)
          let paired := choices.bindOnSupport fun command selected =>
            (available command selected).choose.map (image command)
          refine ⟨paired, ?_, ?_, ?_⟩
          · change paired.map Prod.fst = (app).controlStep initial horizon scheduler
              firstPlayers (some ⟨count + 1, none, first⟩)
            simp only [paired, map_bindOnSupport]
            simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
              Option.bind_some, ReactiveApplication.transition]
            apply bindOnSupport_eq_bind_of_eq_on_support
            intro command selected
            rw [PMF.map_comp]
            change (available command selected).choose.map
              ((fun physical : (app).Execution => some
                (⟨count, command.actor? app, physical⟩ : (app).Control)) ∘ Prod.fst) = _
            rw [← PMF.map_comp, (available command selected).choose_spec.1]
          · change paired.map Prod.snd = (app).controlStep initial horizon scheduler
              secondPlayers (some ⟨count + 1, none, second⟩)
            simp only [paired, map_bindOnSupport]
            simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
              Option.bind_some, ReactiveApplication.transition]
            rw [← before, ← service]
            apply bindOnSupport_eq_bind_of_eq_on_support
            intro command selected
            rw [PMF.map_comp]
            change (available command selected).choose.map
              ((fun physical : (app).Execution => some
                (⟨count, command.actor? app, physical⟩ : (app).Control)) ∘ Prod.snd) = _
            rw [← PMF.map_comp, (available command selected).choose_spec.2.1]
          · intro pair supported
            obtain ⟨command, selected, branch⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
            obtain ⟨actual, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp branch
            exact ⟨count, command.actor? app, actual.1, actual.2, rfl,
              (available command selected).choose_spec.2.2 actual drawn⟩
  | some actor =>
      obtain ⟨paired, firstLaw, secondLaw, related⟩ := phase_timing_plan_actor_word_coupling setup
        mode runtime leaks bounds plan maximal horizon scheduler bound finite wellFormed target
          approximation n fallback parts opponents owner actor block low generation firstWord
            secondWord slotWeight slotNonnegative slotBounded ⟨firstCount, some actor, first⟩
              ⟨firstCount, some actor, second⟩ leftTrace rightTrace rfl rfl memory owned valid
                application network receipts service recalled past clear phase remaining installed
                  committing lower upper values capacity address
      let image (pair : (app).Execution × (app).Execution) :
          (app).ProtocolState × (app).ProtocolState :=
        (some ⟨firstCount, none, pair.1⟩, some ⟨firstCount, none, pair.2⟩)
      refine ⟨paired.map image, ?_, ?_, ?_⟩
      · change (paired.map image).map Prod.fst = (app).controlStep initial horizon scheduler
          firstPlayers (some ⟨firstCount, some actor, first⟩)
        rw [PMF.map_comp]
        change paired.map ((fun physical : (app).Execution =>
          some (⟨firstCount, none, physical⟩ : (app).Control)) ∘ Prod.fst) = _
        rw [← PMF.map_comp, firstLaw, PMF.map_comp]
        simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
          ReactiveApplication.transition, ite_true, Option.getD_some]
        exact (PMF.bind_pure_comp _ _).symm
      · change (paired.map image).map Prod.snd = (app).controlStep initial horizon scheduler
          secondPlayers (some ⟨firstCount, some actor, second⟩)
        rw [PMF.map_comp]
        change paired.map ((fun physical : (app).Execution =>
          some (⟨firstCount, none, physical⟩ : (app).Control)) ∘ Prod.snd) = _
        rw [← PMF.map_comp, secondLaw, PMF.map_comp]
        simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
          ReactiveApplication.transition, ite_true, Option.getD_some]
        exact (PMF.bind_pure_comp _ _).symm
      · intro pair supported
        obtain ⟨actual, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        exact ⟨firstCount, none, actual.1, actual.2, rfl, Or.inr (related actual drawn)⟩

end Vegas
