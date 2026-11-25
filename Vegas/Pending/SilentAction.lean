module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCanonicalResolution

@[expose] public section

/-! # Graph actions realized by silence -/

namespace Vegas
open EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Silence realizes public binding omission or a disclosure of `false`. -/
def SilentAction (event : graph.EventId)
    (action : graph.Action event) : Prop :=
  match nodeView graph event with
  | .bind _ _ outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action) = none
  | .resolve _ _ _ _ outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = false
  | _ => False


variable {timeouts : EventTimeouts graph}
  {leaks : Interaction.MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- Public binding omission and false disclosure compile to silence at every view. -/
theorem canonicalServiceDecision_silent (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId)
    (action : graph.Action event) (silent : SilentAction event action) :
    ((canonicalServiceDecision timeouts) leaks who past view event
        action).transmission = none := by
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      simp only [SilentAction, node] at silent
  | bind owner payload outputEq codeEq =>
      have withheld : cast (congrArg EventGraph.EventField.Action outputEq) action = none := by
        simpa only [SilentAction, node] using silent
      have castBack :=
        congrArg (cast (congrArg EventGraph.EventField.Action outputEq.symm)) withheld
      simp only [cast_cast, cast_eq] at castBack
      rw [castBack]
      exact congrArg ReactiveApplication.Action.transmission
        ((canonicalServiceDecision_binding_none timeouts) leaks who
          past view event owner payload outputEq codeEq node)
  | resolve owner payload binding checks outputEq codeEq =>
      have withheld : cast (congrArg EventGraph.EventField.Action outputEq) action = false := by
        simpa only [SilentAction, node] using silent
      have castBack :=
        congrArg (cast (congrArg EventGraph.EventField.Action outputEq.symm)) withheld
      simp only [cast_cast, cast_eq] at castBack
      rw [castBack]
      exact congrArg ReactiveApplication.Action.transmission
        ((canonicalServiceDecision_resolution_false timeouts) leaks who
          past view event owner payload binding checks outputEq codeEq node)

end Vegas
