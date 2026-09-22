/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ResponseProtocol

/-! # Native policies and protocol policies

A native response policy takes only own recall and the current native view.
The equivalence covers all information-local protocol policies; neither
translation can inspect service epochs, the unconsumed plan, or hidden inputs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def encodeResponsePolicy (runtime : EventGraphRuntime graph)
    (policy : runtime.application.ResponsePolicy) (info : ResponseInfo runtime) :
    FinDist {choice : Option runtime.application.PlayerResponse // choice.isSome = info.isSome} :=
  match info with
  | none => FinDist.pure ⟨none, rfl⟩
  | some (history, view) => (policy history view).map fun response => ⟨some response, rfl⟩

def decodeResponsePolicy (runtime : EventGraphRuntime graph)
    (policy : (info : ResponseInfo runtime) →
      FinDist {choice : Option runtime.application.PlayerResponse // choice.isSome = info.isSome}) :
    runtime.application.ResponsePolicy :=
  fun history view => (policy (some (history, view))).map
    (fun selected => selected.1.getD runtime.idleResponse)

theorem decode_encodeResponsePolicy (runtime : EventGraphRuntime graph)
    (policy : runtime.application.ResponsePolicy) :
    runtime.decodeResponsePolicy (runtime.encodeResponsePolicy policy) = policy := by
  funext history view
  simp only [decodeResponsePolicy, encodeResponsePolicy, FinDist.map_comp,
    Function.comp_def, Option.getD_some]
  exact FinDist.map_id _

theorem encode_decodeResponsePolicy (runtime : EventGraphRuntime graph)
    (policy : (info : ResponseInfo runtime) →
      FinDist {choice : Option runtime.application.PlayerResponse // choice.isSome = info.isSome}) :
    runtime.encodeResponsePolicy (runtime.decodeResponsePolicy policy) = policy := by
  funext info
  cases info with
  | none =>
      have unique (choice : {choice : Option runtime.application.PlayerResponse //
          choice.isSome = (none : ResponseInfo runtime).isSome}) : choice = ⟨none, rfl⟩ := by
        apply Subtype.ext
        have valid := choice.2
        cases selected : choice.1 with
        | none => rfl
        | some response => simp [selected] at valid
      change FinDist.pure _ = policy none
      symm
      calc
        _ = (policy none).map id := (FinDist.map_id _).symm
        _ = (policy none).map (fun _ => ⟨none, rfl⟩) :=
          FinDist.map_congr_of_eq_on_support (fun choice _ => unique choice)
        _ = _ := by simp [FinDist.map_eq_bind]
  | some arguments =>
      rcases arguments with ⟨history, view⟩
      rw [encodeResponsePolicy, decodeResponsePolicy, FinDist.map_comp]
      calc
        _ = (policy (some (history, view))).map id := by
          apply FinDist.map_congr_of_eq_on_support
          intro selected _
          apply Subtype.ext
          have present := selected.2
          cases chosen : selected.1 with
          | none => simp [chosen] at present
          | some response => simp [chosen]
        _ = _ := FinDist.map_id _

/-- One fixed playerwise equivalence, uniform across all prefixes and all
private setup draws. Every protocol deviation has a native response policy. -/
def responsePolicyEquiv (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) (who : Player) :
    runtime.application.ResponsePolicy ≃
      (runtime.responseInformation inputs roster reactionRounds wire order).BehavioralPolicy who
    where
  toFun := runtime.encodeResponsePolicy
  invFun := runtime.decodeResponsePolicy
  left_inv := runtime.decode_encodeResponsePolicy
  right_inv := runtime.encode_decodeResponsePolicy

theorem encodeResponsePolicy_some (runtime : EventGraphRuntime graph)
    (policy : runtime.application.ResponsePolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View) :
    (runtime.encodeResponsePolicy policy (some (history, view))).map Subtype.val =
      (policy history view).map some := by
  rw [encodeResponsePolicy, FinDist.map_comp]
  rfl

/-- Changing a hidden service suffix or epoch counter does not change the
information supplied at this player's response site. -/
theorem responseObserve_player (runtime : EventGraphRuntime graph)
    (who : Player) (epochs : Nat) (rest : List (ServiceInstruction graph))
    (execution : runtime.application.PolicyExecution) :
    runtime.responseObserve who (some ⟨epochs, .player who :: rest, execution⟩) =
      some (execution.principalHistory who,
        MessageApplication.State.observe runtime.application execution.native who) := by
  simp [responseObserve, responseActor]

end Vegas.EventGraphRuntime
