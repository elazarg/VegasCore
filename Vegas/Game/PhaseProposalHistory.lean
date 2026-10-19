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
  let predicate : app.ProtocolState → Prop
    | none => True
    | some current => ∃ witness : RecoverySourceWitness setup mode plan
      current.execution.application,
        witness.checkpoint.ArchivedProposals current.execution.network.inputs
  have tracked : ∀ {state} (historyTrace : (menu.protocol initial horizon scheduler).Trace state),
      predicate state := by
    intro state historyTrace
    induction historyTrace with
    | start => trivial
    | @extend before after prior joint legal supported ih =>
        change after ∈ (app.transition initial horizon scheduler before joint).support at supported
        cases before with
        | none =>
            obtain ⟨state, stateSupport, rfl⟩ := PMF.support_map .. ▸ supported
            obtain ⟨draw, drawSupport, rfl⟩ := PMF.support_map .. ▸ stateSupport
            exact ⟨RecoverySourceWitness.initialized setup mode plan draw drawSupport,
              RecoverySourceWitness.initialized_archivedProposals setup mode plan draw drawSupport⟩
        | some current =>
            obtain ⟨witness, archived⟩ := ih
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some owner =>
                have localLegal := legal.2 owner
                cases selected : joint owner with
                | none =>
                    simp [selected, ReactiveApplication.ResponseMenu.protocol,
                      ReactiveApplication.actor, menu] at localLegal
                | some action =>
                    rw [selected] at localLegal
                    cases (PMF.mem_support_pure_iff _ _).mp supported
                    simpa only [predicate, selected, Option.getD_some] using
                      RecoverySourceWitness.respond_archivedProposals runtime leaks execution
                        witness
                        archived owner action
            | none =>
                cases remaining with
                | zero =>
                    cases (PMF.mem_support_pure_iff _ _).mp supported
                    exact ⟨witness, archived⟩
                | succ remaining =>
                    obtain ⟨command, _selected, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
                    obtain ⟨next, reached, rfl⟩ := PMF.support_map .. ▸ moved
                    exact RecoverySourceWitness.environment_archivedProposals runtime leaks bounds
                      plan maximal horizon scheduler ⟨remaining + 1, none, execution⟩ prior witness
                      archived command next reached
  exact tracked trace

end Vegas
