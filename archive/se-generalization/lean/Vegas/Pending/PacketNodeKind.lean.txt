/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication

/-! # Packet constructors admitted by event nodes

Commitments can be accepted only at binding nodes. Openings and withholding
can be accepted only at resolution nodes. This immutable public graph check
uses no source compiler, private candidate state or scheduler contract.

Malformed packets are rejected by the handler separately. They satisfy the
node matcher so a constructor-breach classifier can handle them directly.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Public constructor compatibility. Malformed packets are handled by their
own constructor check rather than this graph-address check. -/
def Payload.MatchesNode (call : Payload graph) : Prop :=
  match call with
  | .commitment event _ =>
      match nodeView graph event with
      | .bind .. => True
      | .resolve .. | .sample .. => False
  | .opening event _ _ | .withhold event =>
      match nodeView graph event with
      | .resolve .. => True
      | .bind .. | .sample .. => False
  | .malformed _ => True

/-- Every accepting handler branch has the constructor expected by its
public event node. Readiness, timing and all private state remain arbitrary. -/
theorem handle_matchesNode (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    message.payload.MatchesNode := by
  cases call : message.payload with
  | malformed raw => simp only [Payload.MatchesNode]
  | commitment event candidate =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases node : nodeView graph event with
          | bind owner payload outputEq codeEq => simp only [Payload.MatchesNode, node]
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [handle, call, dite_eq_left ready, dite_eq_left timely, node] at accepted
              cases accepted
          | sample payload law outputEq codeEq =>
              simp only [handle, call, dite_eq_left ready, dite_eq_left timely, node] at accepted
              cases accepted
        · simp only [handle, call, dite_eq_left ready, dite_eq_right timely] at accepted
          cases accepted
      · simp only [handle, call, dite_eq_right ready] at accepted
        cases accepted
  | opening event candidate raw | withhold event =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases node : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [Payload.MatchesNode, node]
          | bind owner payload outputEq codeEq =>
              simp only [handle, call, dite_eq_left ready, dite_eq_left timely, node] at accepted
              cases accepted
          | sample payload law outputEq codeEq =>
              simp only [handle, call, dite_eq_left ready, dite_eq_left timely, node] at accepted
              cases accepted
        · simp only [handle, call, dite_eq_left ready, dite_eq_right timely] at accepted
          cases accepted
      · simp only [handle, call, dite_eq_right ready] at accepted
        cases accepted

end Vegas.EventGraphRuntime
