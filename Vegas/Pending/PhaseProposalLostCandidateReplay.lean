/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ValueSwapPairs
import Vegas.Pending.PhaseSwapTransition
import Vegas.Pending.PhaseProposalForeignEvidence
import Vegas.Pending.PhaseProposalLostHandle

/-! # Actual environment replay of one unaccepted private preparation

The existing hidden swap changes only one permanent prepared handle. Logical
fields, actions, original inputs and every public packet remain literal;
expiry and restoration use the existing phase application equivariance.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace HiddenSwap

open Classical in
/-- Transpose two private raw preparations at one physical handle. Every
logical field and completed action is fixed, including canceled producers. -/
def preparationOnly (candidate : Handle graph) (first second : Raw L) : HiddenSwap graph :=
  { values :=
      { value := fun _ => id
        action := fun _ => id
        value_involutive := fun _ _ => rfl
        action_involutive := fun _ _ => rfl
        value_public := fun _ _ => rfl
        action_publication := fun _ _ _ => rfl
        action_binding := fun _ _ _ _ _ => by simp only [id_eq, cast_cast, cast_eq] }
    raw := fun query => if query = candidate then Equiv.swap first second else id
    raw_involutive := by
      intro query value
      split
      · exact Equiv.swap_apply_self first second value
      · rfl }

@[simp] theorem preparationOnly_value (candidate : Handle graph) (first second : Raw L)
    (field : graph.Field) :
    (preparationOnly candidate first second).values.value field = id := rfl

@[simp] theorem preparationOnly_action (candidate : Handle graph) (first second : Raw L)
    (event : graph.EventId) :
    (preparationOnly candidate first second).values.action event = id := rfl

/-- Other physical handles keep their complete raw meanings. -/
theorem preparationOnly_raw_of_ne (candidate query : Handle graph) (first second : Raw L)
    (different : query ≠ candidate) :
    (preparationOnly candidate first second).raw query = id := by
  classical
  simp only [preparationOnly, different, ↓reduceIte]

/-- Every expiry is fixed without an additional cleanliness premise. -/
theorem preparationOnly_expiry (candidate : Handle graph) (first second : Raw L)
    (event : graph.EventId) : (preparationOnly candidate first second).values.ExpiryFixed event :=
  fun _ _ _ => rfl

/-- Any actually accepted handle other than the selected lost one is
compatible with its literal unchanged typed candidate result. -/
theorem preparationOnly_compatible (candidate query : Handle graph) (first second : Raw L)
    (different : query ≠ candidate) (event : graph.EventId) :
    BindCompatible (preparationOnly candidate first second) event query := by
  intro owner payload outputEq meaning
  rw [preparationOnly_raw_of_ne candidate query first second different]
  cases meaning <;> rfl

/-- A genuinely unassociated handle cannot be used by an admitted opening.
All guard reads and the successful bound value stay literal. -/
theorem preparationOnly_reveal_fixed (candidate : Handle graph) (first second : Raw L)
    (state : State graph) (unused : state.HandleUnused candidate) (event : graph.EventId) :
    RevealFixed (preparationOnly candidate first second) state event := by
  unfold RevealFixed
  cases nodeView graph event with
  | bind => trivial
  | sample => trivial
  | resolve owner payload binding checks outputEq codeEq =>
      refine ⟨rfl, ?_⟩
      intro query accepted
      apply preparationOnly_raw_of_ne candidate query first second
      intro same
      subst query
      exact unused binding.field accepted

/-- The actual original phase gate and rejected lost packet supply every
primitive native inclusion guard. No target acceptance or rejection is assumed. -/
theorem preparationOnly_inclusion_fixed
    (runtime : EventGraphRuntime graph) (candidate : Handle graph) (first second : Raw L)
    (state : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (unused : state.current.native.HandleUnused candidate)
    (lostRejected : ∀ event, message.payload.packet.call = .commitment event candidate →
      state.handle runtime message = none)
    (admitted : (message.payload.tokenValid state.attempt &&
      state.allows message.payload.packet.call &&
      !state.current.excludedCall message.payload.packet.call) = true) :
    InclusionFixed runtime (preparationOnly candidate first second) state.current.native
      ⟨message.id, message.payload.packet.call⟩ := by
  constructor
  · intro native event query accepted call
    change message.payload.packet.call = .commitment event query at call
    apply preparationOnly_compatible candidate query first second _ event
    intro same
    subst query
    have actual : state.handle runtime message = some
        ({ state with current := state.current.inclusionResult message.payload.packet.call native }
          : PhaseRuntimeState graph).normalize := by
      unfold PhaseRuntimeState.handle
      rw [admitted]
      simp only [↓reduceIte, accepted, Option.map_some]
    rw [lostRejected event call] at actual
    cases actual
  · intro event _named _ready
    exact preparationOnly_reveal_fixed candidate first second state.current.native unused event

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- The whole actual physical environment kernel preserves original Nature
atoms, occupied slots, headers, receipts and clocks through a lost-value swap.
The original lost-packet rejection is a factual trace obligation; its image
is constructed by the existing handler, expiry, drain and restore laws. -/
theorem environmentStep_preparationOnly
    (candidate : Handle graph) (first second : Raw L)
    (current : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command)
    (unused : current.application.current.native.HandleUnused candidate)
    (lostRejected : ∀ id message event, command = .include id →
      current.network.lookup id = some message →
      message.payload.packet.call = .commitment event candidate →
        current.application.handle runtime message = none) :
    ((preparationOnly candidate first second).phaseExecution current).environmentStep
        (phaseApplication runtime leaks) command =
      (current.environmentStep (phaseApplication runtime leaks) command).map
        (preparationOnly candidate first second).phaseExecution := by
  apply (preparationOnly candidate first second).environmentStep_phaseExecution_of_admitted
    current command (preparationOnly_expiry candidate first second)
  intro id message selected found admitted
  exact preparationOnly_inclusion_fixed runtime candidate first second current.application message
    unused (fun event call => lostRejected id message event selected found call) admitted

end HiddenSwap

end Vegas.EventGraphRuntime
