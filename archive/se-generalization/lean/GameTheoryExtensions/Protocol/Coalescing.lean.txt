/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.SequentialSampling

/-! # Coalescing a response with no incoming information

A deterministic response can be sampled as a complete action transcript when
each local observation is computable from the previous observation and the
player's action. A local response packages that data; the transcript sampler
and its endpoint-law equalities are
`GameTheory.Math.Probability.SequentialSampling.transcript`,
`GameTheory.Math.Probability.SequentialSampling.transcript_eq_iteration` and
`GameTheory.Math.Probability.SequentialSampling.continuation_eq`.

These are execution equalities. They do not identify the SPE predicates of the
split and coalesced games: the latter has no internal decision roots.
-/

noncomputable section

namespace GameTheory.Protocol

universe us uv ua

/-- A local response has no incoming information between its constituent
choices. `observe` may include private memory and own-action recall. -/
structure LocalResponse (State : Type us) (View : Type uv) (Action : Type ua) where
  observe : State → View
  step : State → Action → State
  update : View → Action → View
  observe_step : ∀ state action, observe (step state action) = update (observe state) action

end GameTheory.Protocol
