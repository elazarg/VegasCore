/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryBindingComponent
import Vegas.Pending.PhaseOpeningPolicy

/-! # Globally legal source-policy dispatch at phased physical inputs -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

open Classical in
def requestedEvent (who : Player) (view : PhasePublicView (serviceGraph setup mode)) :
    Option (serviceGraph setup mode).EventId :=
  if offered : ∃ event, PhaseRuntimeState.requests view who ⟨view.attempt, event⟩ then
    some offered.choose else none

omit [Fintype Player] in
private theorem requestedEvent_of_request
    (state : PhaseRuntimeState (serviceGraph setup mode)) {inputs}
    (valid : state.Invariant inputs) (who : Player) (event : (serviceGraph setup mode).EventId)
    (request : state.SeedRequest who ⟨state.attempt, event⟩) :
    requestedEvent setup mode who state.publicView = some event := by
  classical
  have offered := (state.requests_publicView valid who ⟨state.attempt, event⟩).mpr request
  have possible : ∃ other, PhaseRuntimeState.requests state.publicView who
      ⟨state.publicView.attempt, other⟩ := ⟨event, offered⟩
  unfold requestedEvent
  rw [dite_eq_left possible]
  have selected := (state.requests_publicView valid who
    ⟨state.publicView.attempt, possible.choose⟩).mp possible.choose_spec
  have same := (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
    state.current.native.config.cut request.2.2.1 selected.2.2.1 request.2.2.2.1 selected.2.2.2.1
  exact congrArg some same

open Classical in
def eventPolicyDispatch
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player)
    (event : (serviceGraph setup mode).EventId) : (phaseApplication runtime leaks).Policy :=
  match nodeView (serviceGraph setup mode) event with
  | .bind owner payload outputEq _ =>
      if owner = who then
        bindings owner event payload outputEq
      else fun _ _ => PMF.pure ⟨none⟩
  | .resolve owner payload binding _checks _outputEq _codeEq =>
      if owner = who then
        openings owner event payload binding
      else fun _ _ => PMF.pure ⟨none⟩
  | .sample _ _ _ _ => fun _ _ => PMF.pure ⟨none⟩

private theorem eventPolicyDispatch_covered
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (opened : ∀ owner event payload binding past view response,
      response ∈ (openings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (covered : ∀ owner event payload binding past view response,
      response ∈ (bindings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (eventPolicyDispatch setup mode runtime leaks openings bindings who
        event
      past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  cases node : nodeView (serviceGraph setup mode) event with
  | bind owner payload outputEq codeEq =>
      simp only [eventPolicyDispatch, node] at supported
      split at supported
      · rename_i same
        subst owner
        exact covered who event payload outputEq past view response supported
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [eventPolicyDispatch, node] at supported
      split at supported
      · rename_i same
        subst owner
        exact opened who event payload binding past view response supported
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | sample payload law outputEq codeEq =>
      simp only [eventPolicyDispatch, node] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact PhaseCount.silence_onePacket runtime leaks bounds who past view

/-- The current public request selects the event. Binding choices use the supplied
local recipe; openings use the supplied opening component. Coverage follows
from the two component families; selecting pinned sites is separate. -/
def phasePolicyDispatch
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  match requestedEvent setup mode who view.application.2 with
  | none => PMF.pure ⟨none⟩
  | some event => eventPolicyDispatch setup mode runtime leaks openings bindings who
      event past view

omit [Fintype Player] in
/-- The request dispatcher preserves equality of its actual component laws
at two recalls with the same current observation. -/
theorem phasePolicyDispatch_congr_input
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (who : Player) (first second : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (opened : ∀ owner event payload binding,
      openings owner event payload binding first view =
        openings owner event payload binding second view)
    (bound : ∀ owner event payload binding,
      bindings owner event payload binding first view =
        bindings owner event payload binding second view) :
    phasePolicyDispatch setup mode runtime leaks openings bindings who first view =
      phasePolicyDispatch setup mode runtime leaks openings bindings who second view := by
  unfold phasePolicyDispatch
  split
  · rfl
  · rename_i event _selected
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner payload outputEq codeEq =>
        simp only [eventPolicyDispatch, node]
        split
        · exact bound owner event payload outputEq
        · rfl
    | resolve owner payload binding checks outputEq codeEq =>
        simp only [eventPolicyDispatch, node]
        split
        · exact opened owner event payload binding
        · rfl
    | sample payload law outputEq codeEq => simp only [eventPolicyDispatch, node]

/-- Even malformed or unrealized inputs receive a law supported by the actual
bounded authenticated one-packet menu. -/
theorem phasePolicyDispatch_covered
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (opened : ∀ owner event payload binding past view response,
      response ∈ (openings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (covered : ∀ owner event payload binding past view response,
      response ∈ (bindings owner event payload binding past view).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phasePolicyDispatch setup mode runtime leaks openings bindings who
      past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  unfold phasePolicyDispatch at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  · exact eventPolicyDispatch_covered (opened := opened) setup mode runtime leaks bounds openings
      bindings covered who
      _ past view response supported

omit [Fintype Player] in
private theorem eventPolicyDispatch_binding
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload) :
    eventPolicyDispatch setup mode runtime leaks openings bindings who event =
      bindings who event payload binding := by
  classical
  cases node : nodeView (serviceGraph setup mode) event with
  | bind owner actual outputEq codeEq =>
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj (outputEq.symm.trans binding)
      simp only [eventPolicyDispatch, node, ite_true]
  | resolve owner actual ref checks outputEq codeEq => cases outputEq.symm.trans binding
  | sample actual law outputEq codeEq => cases outputEq.symm.trans binding

omit [Fintype Player] in
/-- A genuine current request selects its actual binding branch, independently
of the choice made by the public selector on impossible inputs. -/
theorem phasePolicyDispatch_binding
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phasePolicyDispatch setup mode runtime leaks openings bindings who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      bindings who event payload binding (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) := by
  have selected := requestedEvent_of_request setup mode execution.application valid who event
    request
  change (match requestedEvent setup mode who execution.application.publicView with
    | none => PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
    | some selected => eventPolicyDispatch setup mode runtime leaks openings bindings
        who selected (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)) = _
  rw [selected]
  change eventPolicyDispatch setup mode runtime leaks openings bindings who event
    (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) = _
  rw [eventPolicyDispatch_binding setup mode runtime leaks openings bindings who event
    payload binding]

omit [Fintype Player] in
/-- Every genuine resolve request selects its supplied opening component;
no source opening-view decoder is used. -/
theorem phasePolicyDispatch_opening
    (openings : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (bindings : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phasePolicyDispatch setup mode runtime leaks openings bindings who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      openings who event payload binding (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) := by
  classical
  have selected := requestedEvent_of_request setup mode execution.application valid who event
    request
  unfold phasePolicyDispatch
  change (match requestedEvent setup mode who execution.application.publicView with
    | none => PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
    | some selected => eventPolicyDispatch setup mode runtime leaks openings bindings
        who selected (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)) = _
  rw [selected]
  simp only [eventPolicyDispatch, nodeView_eq_resolve outputEq codeEq, ite_true]


omit [Fintype Player] in
/-- Pointwise component domination passes through the SAME actual public
request dispatcher. Forced silence needs only that the retained mass is at
most one; no source query, reach, or qualification premise is involved. -/
theorem phasePolicyDispatch_probability_domination
    (firstOpen secondOpen : ∀ (owner : Player) (_event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), FieldRef (serviceGraph setup mode).layout (.binding owner payload) →
      (phaseApplication runtime leaks).Policy)
    (firstBind secondBind : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId)
      (payload : L.Ty), (serviceGraph setup mode).outputLayout event = .binding owner payload →
      (phaseApplication runtime leaks).Policy)
    (factor : ℝ) (bounded : factor ≤ 1) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (openLower : ∀ owner event payload binding response,
      factor * (firstOpen owner event payload binding past view response).toReal ≤
        (secondOpen owner event payload binding past view response).toReal)
    (bindLower : ∀ owner event payload binding response,
      factor * (firstBind owner event payload binding past view response).toReal ≤
        (secondBind owner event payload binding past view response).toReal)
    (response : (phaseApplication runtime leaks).Action) :
    factor * (phasePolicyDispatch setup mode runtime leaks firstOpen firstBind who
      past view response).toReal ≤
      (phasePolicyDispatch setup mode runtime leaks secondOpen secondBind who
        past view response).toReal := by
  classical
  have silent : factor * ((PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action))
      response).toReal ≤ (PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action)
        response).toReal :=
    mul_le_of_le_one_left ENNReal.toReal_nonneg bounded
  cases offered : requestedEvent setup mode who view.application.2 with
  | none => simpa only [phasePolicyDispatch, offered] using silent
  | some event =>
      cases node : nodeView (serviceGraph setup mode) event with
      | bind owner payload binding code =>
          simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node]
          split
          · exact bindLower owner event payload binding response
          · exact silent
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [phasePolicyDispatch, offered, eventPolicyDispatch, node]
          split
          · exact openLower owner event payload binding response
          · exact silent
      | sample payload law outputEq codeEq =>
          simpa only [phasePolicyDispatch, offered, eventPolicyDispatch, node] using silent

end Vegas
