/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalInitial
import Vegas.Game.PhaseProposalRespond
import Vegas.Game.PhaseProposalEnvironment
import Interaction.ReactiveMenuInvariant

/-! # Actual counted executions have their full consumed enriched source archive -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Prefix

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) setup.initialLaw

/-- A supplied full source witness follows the actual native prefix using the
same transition producers, retaining its full source path and proposal archive. -/
theorem RecoverySourceWitness.prefix_archived_source
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    {state : ((menu).protocol initial horizon scheduler).State}
    (trace : ((menu).protocol initial horizon scheduler).Trace state)
    (kept : TracePrefix anchorTrace trace) :
    ∃ current : (app).Control, state = some current ∧
      ∃ next : RecoverySourceWitness setup mode plan current.execution.application,
        next.checkpoint.ArchivedProposals current.execution.network.inputs ∧
        ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩ := by
  induction kept with
  | refl => exact ⟨anchor, rfl, witness, archived, 0, .refl 0 _⟩
  | @extend source target prior retained actions legal supported ih =>
      obtain ⟨before, sourceEq, current, currentArchived, previousFuel, previousPath⟩ := ih
      subst source
      change target ∈ ((app).transition initial horizon scheduler (some before) actions).support
        at supported
      rcases before with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner =>
          have offered := legal.2 owner
          cases selected : actions owner with
          | none =>
              simp [selected, ReactiveApplication.ResponseMenu.protocol,
                ReactiveApplication.actor] at offered
          | some action =>
              simp only [ReactiveApplication.transition, selected, Option.getD_some] at supported
              cases (PMF.mem_support_pure_iff _ _).mp supported
              obtain ⟨next, nextArchived, nextFuel, nextPath⟩ :=
                current.respond_archived_source runtime leaks execution currentArchived owner action
              refine ⟨_, rfl, next, ?_, previousFuel + nextFuel, ?_⟩
              · simpa only [selected, Option.getD_some] using nextArchived
              · simpa only [selected, Option.getD_some] using previousPath.trans nextPath
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp supported
              exact ⟨_, rfl, current, currentArchived, previousFuel, previousPath⟩
          | succ remaining =>
              obtain ⟨command, _selected, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
              obtain ⟨nextExecution, reached, rfl⟩ := PMF.support_map .. ▸ moved
              have counted : ((menu).protocol
                  (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan
                    (encodeInputs draw)) horizon scheduler).Trace
                    (some ⟨remaining + 1, none, execution⟩) := by
                simpa only [PMF.map_comp, Function.comp_def] using prior
              obtain ⟨next, nextArchived, nextFuel, nextPath⟩ :=
                current.environment_archived_source runtime leaks bounds plan maximal horizon
                  scheduler ⟨remaining + 1, none, execution⟩ counted currentArchived command
                    nextExecution reached
              exact ⟨_, rfl, next, nextArchived, previousFuel + nextFuel,
                previousPath.trans nextPath⟩

end Prefix

/-- This folds the actual counted history using the shared source transition
producer. It starts from the original setup law, retains every submitted proposal
by every author, and requires no archive or source counterpart hypothesis. -/
theorem recoverySourceCheckpoint_proposalArchive_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control)) :
    ∃ witness : RecoverySourceWitness setup mode plan control.execution.application,
      witness.checkpoint.ArchivedProposals control.execution.network.inputs := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)
  let final : (menu.protocol initial horizon scheduler).History := ⟨some control, trace⟩
  have reached := (menu.protocol initial horizon scheduler).reachesWithin_from_init final
  rcases reached.eq_or_step with same | ⟨actions, legal, state, realized, fuel, rest⟩
  · have impossible := congrArg History.state same
    change none = some control at impossible
    cases impossible
  · change state ∈ (app.transition initial horizon scheduler none actions).support at realized
    obtain ⟨physical, physicalSupport, rfl⟩ := PMF.support_map .. ▸ realized
    obtain ⟨draw, drawSupport, rfl⟩ := PMF.support_map .. ▸ physicalSupport
    let witness := RecoverySourceWitness.initialized setup mode plan draw drawSupport
    have archived := RecoverySourceWitness.initialized_archivedProposals setup mode plan draw
      drawSupport
    obtain ⟨last, stateEq, next, nextArchived, _sourceFuel, _sourcePath⟩ :=
      witness.prefix_archived_source setup mode runtime leaks bounds plan maximal horizon scheduler
        _ (Trace.start.extend actions legal realized) archived trace rest.tracePrefix
    cases Option.some.inj stateEq
    exact ⟨next, nextArchived⟩

end Vegas
