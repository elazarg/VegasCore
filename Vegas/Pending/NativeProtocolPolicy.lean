/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeProtocol

/-! # Native policies and protocol policies

A native policy takes only own recall and the current native view.
The equivalence covers all information-local protocol policies; neither
translation can inspect service epochs, the unconsumed plan, or hidden inputs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def encodeNativePolicy
    (policy : NativePolicy graph) (info : NativeInfo graph) :
    FinDist {choice : Option (PlayerAction graph) // choice.isSome = info.isSome} :=
  match info with
  | none => FinDist.pure ⟨none, rfl⟩
  | some (history, view) => (policy history view).map fun native => ⟨some native, rfl⟩

def decodeNativePolicy
    (policy : (info : NativeInfo graph) →
      FinDist {choice : Option (PlayerAction graph) // choice.isSome = info.isSome}) :
    NativePolicy graph :=
  fun history view => (policy (some (history, view))).map
    (fun selected => selected.1.getD PlayerAction.wait)

omit [DecidableEq Player] in
theorem decode_encodeNativePolicy
    (policy : NativePolicy graph) :
    decodeNativePolicy (encodeNativePolicy policy) = policy := by
  funext history view
  simp only [decodeNativePolicy, encodeNativePolicy, FinDist.map_comp,
    Function.comp_def, Option.getD_some]
  exact FinDist.map_id _

omit [DecidableEq Player] in
theorem encode_decodeNativePolicy
    (policy : (info : NativeInfo graph) →
      FinDist {choice : Option (PlayerAction graph) // choice.isSome = info.isSome}) :
    encodeNativePolicy (decodeNativePolicy policy) = policy := by
  funext info
  cases info with
  | none =>
      have unique (choice : {choice : Option (PlayerAction graph) //
          choice.isSome = (none : NativeInfo graph).isSome}) : choice = ⟨none, rfl⟩ := by
        apply Subtype.ext
        have valid := choice.2
        cases selected : choice.1 with
        | none => rfl
        | some native => simp [selected] at valid
      change FinDist.pure _ = policy none
      symm
      calc
        _ = (policy none).map id := (FinDist.map_id _).symm
        _ = (policy none).map (fun _ => ⟨none, rfl⟩) :=
          FinDist.map_congr_of_eq_on_support (fun choice _ => unique choice)
        _ = _ := by simp [FinDist.map_eq_bind]
  | some arguments =>
      rcases arguments with ⟨history, view⟩
      rw [encodeNativePolicy, decodeNativePolicy, FinDist.map_comp]
      calc
        _ = (policy (some (history, view))).map id := by
          apply FinDist.map_congr_of_eq_on_support
          intro selected _
          apply Subtype.ext
          have present := selected.2
          cases chosen : selected.1 with
          | none => simp [chosen] at present
          | some native => simp [chosen]
        _ = _ := FinDist.map_id _

/-- One fixed playerwise equivalence, uniform across all prefixes and all
private setup draws. Every protocol deviation has a native policy. -/
def nativePolicyEquiv (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) (who : Player) :
    NativePolicy graph ≃
      (runtime.nativeInformation inputs roster reactionRounds wire order).BehavioralPolicy who
    where
  toFun := encodeNativePolicy
  invFun := decodeNativePolicy
  left_inv := decode_encodeNativePolicy
  right_inv := encode_decodeNativePolicy

omit [DecidableEq Player] in
theorem encodeNativePolicy_some
    (policy : NativePolicy graph)
    (history : List (NativeEntry graph)) (view : NativeView graph) :
    (encodeNativePolicy policy (some (history, view))).map Subtype.val =
      (policy history view).map some := by
  rw [encodeNativePolicy, FinDist.map_comp]
  rfl

/-- Changing a hidden service suffix or epoch counter does not change the
information supplied at this player's decision. -/
theorem nativeObserve_player (runtime : EventGraphRuntime graph)
    (who : Player) (epochs : Nat) (rest : List (ServiceInstruction graph))
    (execution : NativeExecution runtime) :
    runtime.nativeObserve who (some ⟨epochs, .player who :: rest, execution⟩) =
      some (execution.principalHistory who,
        runtime.nativeView execution.native who) := by
  simp [nativeObserve, nativeActor]

end Vegas.EventGraphRuntime
