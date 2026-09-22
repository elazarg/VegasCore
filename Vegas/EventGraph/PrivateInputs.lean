/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Information

/-! # Owner-visible immutable graph inputs -/

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
/-- Every reachable graph configuration retains its complete initial environment. -/
theorem Config.Reachable.inputs_eq {graph : Vegas.EventGraph Player L}
    {inputs : graph.Inputs} {config : graph.Config} (reachable : config.Reachable inputs) :
    config.inputs = inputs := by
  induction reachable with
  | initial => rfl
  | step _ _ _ _ _ member ih =>
      rw [Config.step, FinDist.support_map] at member
      obtain ⟨_, _, rfl⟩ := member
      exact ih

omit [DecidableEq Player] in
/-- Private inputs are supplied at setup; no graph node produces one. -/
theorem EventCode.output_ne_privateInput {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (owner : Player) (payload : L.Ty) :
    output ≠ .privateInput owner payload := by
  cases code <;> intro same <;> cases same

omit [DecidableEq Player] in
/-- The public store never contains a private input value. -/
theorem publicStore_privateInput (graph : Vegas.EventGraph Player L)
    (store : Store graph.layout) (field : graph.Field) (owner : Player) (payload : L.Ty)
    (kind : graph.layout field = .privateInput owner payload) :
    graph.publicStore store field = none := by
  apply graph.publicStore_of_private
  simp [fieldPublic, kind, EventField.IsPublic]

/-- A private input is available to its owner in the actual player projection. -/
theorem playerStore_own_privateInput (graph : Vegas.EventGraph Player L)
    (store : Store graph.layout) (field : graph.Field) (owner : Player) (payload : L.Ty)
    (kind : graph.layout field = .privateInput owner payload) :
    graph.playerStore owner store field = store field := by
  apply graph.playerStore_of_visible
  simp [fieldVisibleTo, kind, EventField.VisibleTo]

/-- Another player's input is absent from a player's store projection. -/
theorem playerStore_foreign_privateInput (graph : Vegas.EventGraph Player L)
    (store : Store graph.layout) (field : graph.Field) (owner who : Player) (payload : L.Ty)
    (kind : graph.layout field = .privateInput owner payload) (different : owner ≠ who) :
    graph.playerStore who store field = none := by
  apply graph.playerStore_of_hidden
  simpa [fieldVisibleTo, kind, EventField.VisibleTo] using different

end Vegas.EventGraph
