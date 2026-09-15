/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.Observation
import Vegas.Graph.MessageInvariant
import Interaction.MessageApplicationLocality

/-! # Observation laws for hidden native preparation and commitment admission

These are local noninterference laws, not whole-run deviation simulation.
They concern the actual player/environment projections, including the owner's
private candidate catalogue; no claim equates complete native states.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L] {Γ Δ : VCtx Player L}

/-- A private command cannot change another principal's application view. -/
theorem privateStep_other_playerView (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (actor observer : Player) (different : observer ≠ actor)
    (command : PrivateCommand L) :
    (runtime.privateStep state actor command).playerView observer = state.playerView observer := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases command with
      | rememberDisclosure disclose => rfl
      | prepare slot raw =>
          have unchanged :
              (fun serial => (candidates.prepare actor (.prepared slot) raw).lookup
                (observer, .prepared serial)) =
              (fun serial => candidates.lookup (observer, .prepared serial)) := by
            funext serial
            exact candidates.lookup_prepare_other actor (.prepared slot) raw
              (observer, .prepared serial) (fun same => different (congrArg Prod.fst same))
          change PlayerView.mk observer _ _ _ = PlayerView.mk observer _ _ _
          rw [unchanged]

/-- Before delivery or inclusion, arbitrary other-player polling preserves
the observer's entire actual policy input, not only its graph observation. -/
theorem runPolicies_other_player_input (runtime : GraphRuntime Player L Δ)
    (observer : Player) (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (noEnvironment : MessageApplication.Invocation.environment ∉ schedule)
    (noObserver : MessageApplication.Invocation.player observer ∉ schedule)
    (execution next : runtime.application.PolicyExecution)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    (next.principalHistory observer,
        MessageApplication.State.observe runtime.application next.native observer) =
      (execution.principalHistory observer,
        MessageApplication.State.observe runtime.application execution.native observer) := by
  exact runtime.application.runPolicies_other_input observer
    (fun state actor command different =>
      runtime.privateStep_other_playerView state actor observer different command)
    players environment schedule noEnvironment noObserver execution next supported

/-- A non-owner sees the same accepted binding step for any hidden candidate
meanings, provided its previous observation and own prepared candidates agree.
The public handle and inclusion time are retained, not erased. -/
theorem advanceBind_other_playerView_congr
    (observer owner : Player) (different : owner ≠ observer)
    (name : VarId) (payload : L.Ty)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (leftIdeal rightIdeal : VEnv L Γ)
    (visible : observe observer leftIdeal = observe observer rightIdeal)
    (values : PublicValues Γ) (bindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (ownCandidates : ∀ serial, leftCandidates.lookup (observer, .prepared serial) =
      rightCandidates.lookup (observer, .prepared serial))
    (pc clock : Nat) (handle : Handle Player) (handleOwner : handle.1 = owner) :
    (advanceBind next leftIdeal values bindings leftCandidates pc clock handle).playerView
        observer =
      (advanceBind next rightIdeal values bindings rightCandidates pc clock handle).playerView
        observer := by
  have unchanged (catalog : CommitmentCandidates Player Slot (Raw L)) (serial : Nat) :
      (catalog.accept handle).lookup (observer, .prepared serial) =
        catalog.lookup (observer, .prepared serial) := by
    apply catalog.lookup_accept_other
    intro same
    exact different (handleOwner.symm.trans (congrArg Prod.fst same).symm)
  have own : (fun serial => (leftCandidates.accept handle).lookup (observer, .prepared serial)) =
      (fun serial => (rightCandidates.accept handle).lookup (observer, .prepared serial)) := by
    funext serial
    rw [unchanged, unchanged, ownCandidates]
  dsimp only [advanceBind, State.playerView]
  rw [Graph.observe_cons_sealed_congr observer owner different name (R.result payload)
    _ _ leftIdeal rightIdeal visible, own]

end Vegas.GraphRuntime
