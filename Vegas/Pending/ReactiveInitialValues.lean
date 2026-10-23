/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveFiniteResponses

/-! # Covering initialized commitment values in finite response bounds

A finite initial law and finitely many initial handles supply a finite set of
opening values, even when their source types are infinite. Extending a declared
message alphabet with this set retains its other signaling values and prepared
handle bound. No equilibrium or prescribed policy enters the construction.

This proves coverage of initialized values, not a bound on fresh commitments or
all later computed source values. A reveal-only compiler must separately prove
that its openings retain these initialized meanings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
/-- The opening values of the initialized handles across a finitely supported
initial law. A law of infinite support contributes none; coverage below assumes
finite support. -/
def initialValues (initial : PMF (State graph)) : Finset (Raw L) :=
  if finite : initial.support.Finite then
    finite.toFinset.biUnion fun state => Finset.univ.biUnion fun who =>
      Finset.univ.biUnion fun input : graph.InputId =>
        ((state.candidates.lookup (who, .initial input)).opening?).toList.toFinset
  else ∅

end Vegas.EventGraphRuntime.MessageBounds
