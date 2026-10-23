/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixWordAction
import Vegas.Compile.CommitPhaseLayout
import Vegas.Compile.CommitPrefixWordReadout
import Vegas.Game.PhaseBindingRecallWord
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseClearNativeProgress
import Interaction.ReactiveRecordedResponse
import Vegas.Game.PhaseBindingRecallMeaning
import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseBindingReadiness
import Vegas.EventGraph.RelaxedRecall
import Vegas.Game.CommitPrefixReadyRecall
import Vegas.Source.CommitPrefixWordProjection

/-! # Actual accepted bindings identify the earlier complete source view -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- The actual whole-program decoder recovers precisely the addressed
original source action chosen from an owned complete word. -/
theorem phaseCommitWordAction_decode
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (who : Player) (index : Fin (eventCount (block.prepend suffix)))
    (inside : index.val < block.length) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout (embedding.event index) =
      .binding who payload) (word : DecisionView who Δ) :
    decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventField.Action binding.symm)
        (phaseRecoveryBindingData setup mode (embedding.event index) who payload binding
          (CommitRecoveryMove.lift (block.wordAction who index.val word))).1) =
      block.wordAction who index.val word := by
  have owned : eventOwner? (block.prepend suffix) index = some who := by
    rw [eventOwner?_eq_actor]
    exact EventGraph.actor?_of_outputLayout_binding (toEventGraph (block.prepend suffix))
      ((embedding.layout_eq index).symm.trans binding)
  obtain ⟨action, native, read, decoded⟩ := compiledCommitPrefix_wordAction_decodable
    block suffix who index inside owned word
  let graphAction : EventField.Action (outputLayout setup.program (embedding.event index)) :=
    cast (congrArg EventField.Action (embedding.layout_eq index).symm) native
  have actual : decodeEventAction setup.program (embedding.event index) graphAction =
      some action := by
    rw [actions]
    simpa only [graphAction, cast_cast, cast_eq] using decoded
  have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program
    (embedding.event index) graphAction action actual
  rw [read]
  simpa only [phaseRecoveryBindingData, CommitRecoveryMove.lift, Option.map_some,
    Option.elim_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoded,
    Option.getD_some, cast_cast, cast_eq] using actual

/-- At an actual compiled owned slot, the complete-word result encoder is
injective on its genuine original source actions. Failed accepted values are
included, and arbitrary complete words need no support premise. -/
theorem phaseCommitWordAction_eq_iff_result
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (who : Player) (index : Fin (eventCount (block.prepend suffix)))
    (inside : index.val < block.length) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout (embedding.event index) =
      .binding who payload) (left right : DecisionView who Δ) :
    block.wordAction who index.val left = block.wordAction who index.val right ↔
      (phaseRecoveryBindingData setup mode (embedding.event index) who payload binding
        (CommitRecoveryMove.lift (block.wordAction who index.val left))).1 =
      (phaseRecoveryBindingData setup mode (embedding.event index) who payload binding
        (CommitRecoveryMove.lift (block.wordAction who index.val right))).1 := by
  constructor
  · intro same
    rw [same]
  · intro same
    have compared := congrArg (fun result => decodeEventAction setup.program
      (embedding.event index) (cast (congrArg EventField.Action binding.symm) result)) same
    simpa only [phaseCommitWordAction_decode setup mode block suffix embedding actions who index
      inside payload binding] using compared

end Vegas
