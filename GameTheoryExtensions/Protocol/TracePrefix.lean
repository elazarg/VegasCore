/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.History

/-! # Prefixes of histories

A history is a *prefix* of another when the other extends it by finitely many
realized transitions (`GameTheory.Protocol.ExecutionProtocol.TracePrefix`).
A prefix is no longer than the history it is a prefix of
(`GameTheory.Protocol.ExecutionProtocol.TracePrefix.length_le`).
-/

namespace GameTheory.Protocol

variable {ι : Type*}

namespace ExecutionProtocol

variable {E : ExecutionProtocol ι}

/-- **A prefix of a history**: the history itself, or a prefix of the history
it extends. -/
inductive TracePrefix {first : E.State} (prefixTrace : E.Trace first) :
    {second : E.State} → E.Trace second → Prop
  | refl : TracePrefix prefixTrace prefixTrace
  | extend {source target : E.State} {prior : E.Trace source}
      (earlier : TracePrefix prefixTrace prior) (joint : ∀ i, Option (E.Action i))
      (isLegal : E.Legal source joint)
      (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
      TracePrefix prefixTrace (prior.extend joint isLegal realized)

theorem TracePrefix.length_le {first second : E.State} {prefixTrace : E.Trace first}
    {trace : E.Trace second} (isPrefix : TracePrefix prefixTrace trace) :
    prefixTrace.length ≤ trace.length := by
  induction isPrefix with
  | refl => exact le_rfl
  | extend _ _ _ _ ih => exact ih.trans (Nat.le_succ _)

theorem TracePrefix.trans {first second third : E.State} {firstTrace : E.Trace first}
    {secondTrace : E.Trace second} {thirdTrace : E.Trace third}
    (left : TracePrefix firstTrace secondTrace) (right : TracePrefix secondTrace thirdTrace) :
    TracePrefix firstTrace thirdTrace := by
  induction right with
  | refl => exact left
  | extend _ joint isLegal realized ih => exact .extend ih joint isLegal realized

theorem TracePrefix.start : ∀ {state : E.State} (trace : E.Trace state),
    TracePrefix (Trace.start : E.Trace E.init) trace
  | _, .start => .refl
  | _, .extend prior joint isLegal realized =>
      .extend (TracePrefix.start prior) joint isLegal realized

end ExecutionProtocol

end GameTheory.Protocol
