/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTableRun
import Interaction.ReactiveProfileMixture
import Interaction.ReactiveResponseConditioning
import Interaction.ReactiveControlOccupation
import Interaction.ReactiveRoundTrace
import Vegas.Game.PhaseCountServiceTableNative

/-! # Original primitive tags and complete timing tables at native command inputs -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player Tag : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

variable
  (values : Tag → ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (tagLaw : PMF Tag) (input : Tag → (serviceGraph setup mode).Inputs)
  (scheduler : Tag → (phaseApplication runtime leaks).Scheduler)

local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))
local notation "members" => fun (tag : Tag) (owner : Player)
  (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) =>
    phaseCountServiceTapePolicy setup mode runtime leaks bounds (values tag) choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon table owner
local notation "players" => fun (tag : Tag) (owner : Player) =>
  ReactiveApplication.Implementation.policy
    (ReactiveApplication.policyMixture (phaseApplication runtime leaks) original
      (members tag owner))
local notation "factors" => fun (tag : Tag)
  (state : ReactiveApplication.ProtocolState (phaseApplication runtime leaks)) (owner : Player) =>
  ReactiveApplication.Implementation.posterior
    (ReactiveApplication.policyMixture (phaseApplication runtime leaks) original
      (members tag owner))
      (ReactiveApplication.recallAt (phaseApplication runtime leaks) owner state)

local notation "literal" => fun tag => phaseCountServicePolicy setup mode runtime leaks bounds
  (values tag) choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
  slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded

/-- At actual initialized command boundaries the original table implementation
has exactly the selected normalized physical policy law, retaining all recalls. -/
theorem phaseCountServiceTapePolicy_command_literal
    (tag : Tag) (remaining count : Nat) (bounded : count ≤ horizon) :
    (app).commandControlLaw (scheduler tag) (players tag)
        (PMF.pure (PhaseRuntimeState.initial plan (input tag))) remaining count =
      (app).commandControlLaw (scheduler tag) (literal tag)
        (PMF.pure (PhaseRuntimeState.initial plan (input tag))) remaining count := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := (PMF.pure (input tag)).map (PhaseRuntimeState.initial plan)
  have covered : ∀ owner past view action,
      action ∈ (players tag owner past view).support →
        action ∈ menu.actions owner past view := by
    intro owner past view action supported
    change action ∈ (((app).policyMixture original (members tag owner)).policy past view).support
      at supported
    rw [ReactiveApplication.policyMixture_policy] at supported
    obtain ⟨table, _possible, offered⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    exact phaseCountServiceTapePolicy_covered setup mode runtime leaks bounds (values tag) choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon table owner
      past view action offered
  have rounds : ∀ count rest execution,
      (menu.protocol initial horizon (scheduler tag)).Trace
        (some ⟨rest + count, none, execution⟩) →
      (app).runRounds (scheduler tag) (players tag) count execution =
        (app).runRounds (scheduler tag) (literal tag) count execution := by
    intro count
    induction count with
    | zero => intro rest execution trace; rfl
    | succ count ih =>
        intro rest execution trace
        have trace' : (menu.protocol initial horizon (scheduler tag)).Trace
            (some ⟨(rest + count) + 1, none, execution⟩) := by
          simpa only [Nat.add_assoc] using trace
        have oneRound : (app).round (scheduler tag) (players tag) execution =
            (app).round (scheduler tag) (literal tag) execution := by
          simp only [ReactiveApplication.round, ReactiveApplication.dispatch]
          apply bind_congr_on_support
          intro command selected
          apply bind_congr_on_support
          intro middle moved
          obtain ⟨pending⟩ := menu.trace_environment initial horizon (scheduler tag)
            (rest + count) execution middle command trace' selected moved
          cases actor : command.actor? app with
          | none => rfl
          | some owner =>
              have same := phaseCountServiceTapePolicy_table_policy_of_history setup mode runtime
                leaks bounds (values tag) choose failure timing firstNonnegative firstBounded
                timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
                rawNonnegative rawBounded horizon plan (PMF.pure (input tag)) (scheduler tag)
                ⟨rest + count, command.actor? app, middle⟩ pending owner actor
              simp only [ReactiveApplication.resume, ReactiveApplication.invoke, same]
        simp only [ReactiveApplication.runRounds]
        rw [← oneRound]
        apply bind_congr_on_support
        intro next supported
        obtain ⟨nextTrace⟩ := menu.trace_round initial horizon (scheduler tag) (players tag) covered
          (rest + count) execution next trace' supported
        exact ih rest next nextTrace
  obtain ⟨initialTrace⟩ := menu.trace_initial initial horizon (scheduler tag)
    (PhaseRuntimeState.initial plan (input tag)) (by simp [initial])
  have roundsEq := rounds count (horizon - count)
    (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan (input tag)))
      (by simpa only [Nat.sub_add_cancel bounded] using initialTrace)
  simp only [ReactiveApplication.commandControlLaw, PMF.pure_bind]
  rw [roundsEq]

variable [NeZero horizon]

/-- The physical marginal of the ORIGINAL tag/table occupation joint is the
literal normalized native law at the original command index and primitive tag. -/
theorem phaseCountServiceTapePolicy_occupation_literal :
    (phaseCountServiceTableOccupation setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon plan tagLaw input scheduler).map
        Prod.fst =
      (PMF.uniformOfFintype (Fin horizon)).bind (fun time => tagLaw.bind fun tag =>
        ((app).commandControlLaw (scheduler tag) (literal tag)
          (PMF.pure (PhaseRuntimeState.initial plan (input tag))) (horizon - time.val - 1)
            time.val).map (fun state => ((time, tag), state))) := by
  rw [phaseCountServiceTapePolicy_occupation_tables_joint]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  have constants (branch : (Fin horizon × Tag) × (app).ProtocolState) :
      (independentProduct (factors branch.1.2 branch.2)).map
      (fun _ => branch) = PMF.pure branch := PMF.map_const _ _
  simp_rw [constants]
  rw [PMF.bind_pure]
  apply bind_congr_on_support
  intro time _timeSupported
  apply bind_congr_on_support
  intro tag _tagSupported
  rw [phaseCountServiceTapePolicy_command_literal setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon plan input scheduler
    tag (horizon - time.val - 1) time.val time.isLt.le]

end Vegas
