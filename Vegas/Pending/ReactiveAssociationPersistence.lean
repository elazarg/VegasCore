/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosureStability

/-! # A recipient retains certified named bindings -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveAssociationInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (field : graph.Field) (candidate : Handle graph) :
    (runtime.reactiveApplication leaks).Invariant (fun state =>
      state.BindingInvariant ∧ state.accepted field = some candidate) where
  submit state who material valid := by
    refine ⟨(runtime.reactiveBindingInvariant leaks).submit state who material valid.1, ?_⟩
    have same := runtime.reactive_respond_application leaks
      (.initial (runtime.reactiveApplication leaks) state) who ⟨some material⟩
    exact (congrFun (congrArg PublicView.accepted same.2) field).trans valid.2
  handle state message next valid accepted := by
    refine ⟨(runtime.reactiveBindingInvariant leaks).handle
      state message next valid.1 accepted, ?_⟩
    exact (handle_accepted_of_present runtime state next field
      (valid.1.accepted_present field candidate valid.2)
      ⟨message.id, message.payload.call⟩
        (reactiveHandle_call accepted)).trans valid.2
  environment state command next valid reached := by
    refine ⟨(runtime.reactiveBindingInvariant leaks).environment
      state command next valid.1 reached, ?_⟩
    rw [(environmentStep_tables runtime state next command reached).1]
    exact valid.2

end Vegas.EventGraphRuntime
