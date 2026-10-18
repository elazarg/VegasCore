/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationService
import Vegas.Game.PhaseCountServicePolicy
import Vegas.Pending.PhaseBindingMenuShape

/-! # Truthful prepared continuations in the hidden-input timing runtime -/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

theorem binding_payload_bool (owner : Player) (event : graph.EventId)
    (payload : simpleExpr.Ty) (binding : graph.outputLayout event = .binding owner payload) :
    payload = .bool := by
  fin_cases event
  · have same : EventField.binding (L := simpleExpr) alice .bool = .binding owner payload := binding
    exact (EventField.binding.inj same).2.symm
  · have same : EventField.binding (L := simpleExpr) bob .bool = .binding owner payload := binding
    exact (EventField.binding.inj same).2.symm
  · have same : EventField.publication (L := simpleExpr) .bool = .binding owner payload := binding
    cases same
  · have same : EventField.publication (L := simpleExpr) .bool = .binding owner payload := binding
    cases same

def constantBindingLaw (value : Bool) (owner : Player) (event : graph.EventId)
    (payload : simpleExpr.Ty) (binding : graph.outputLayout event = .binding owner payload)
    (_ : List app.PlayerEntry) (_ : app.PlayerView) : PMF (simpleExpr.Val payload) := by
  have same := binding_payload_bool owner event payload binding
  subst payload
  exact PMF.pure value

/-- The existing native constructor prepares a typed value in a fresh slot and
opens the accepted handle truthfully. The rule only selects binding timing. -/
def properPolicy (value : Bool)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player) : app.Policy :=
  phaseCountServicePolicy setup .concurrentReveals runtime leaks bounds
    (constantBindingLaw value) rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num) owner

theorem properPolicy_counted (value : Bool)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (properPolicy value rule owner past view).support) :
    response ∈ countedMenu.actions owner past view := by
  exact phaseCountServicePolicy_covered setup .concurrentReveals runtime leaks bounds
    (constantBindingLaw value) rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    owner past view response supported

end Vegas.Examples.CommitTimingInformation
