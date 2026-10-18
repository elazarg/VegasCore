/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAudit
import Vegas.Examples.CommitSeedBroadcastInitialQuiet
import Vegas.Game.PhaseCountServicePolicy
import Vegas.Pending.PhaseBindingMenuShape

/-! # Actual truthful one-packet continuations for the three-owner game -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem initial_eq_compiled :
    initial = (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) := by
  change PMF.pure initialState = ((PMF.pure (Env.empty (CellVal simpleExpr))).map
    encodeInputs).map (PhaseRuntimeState.initial plan)
  simp only [PMF.pure_map]
  rfl

theorem binding_payload_bool (owner : Player) (event : graph.EventId)
    (payload : simpleExpr.Ty) (binding : graph.outputLayout event = .binding owner payload) :
    payload = .bool := by
  fin_cases event
  · have same : EventField.binding (L := simpleExpr) alice .bool = .binding owner payload := binding
    exact (EventField.binding.inj same).2.symm
  · have same : EventField.binding (L := simpleExpr) bob .bool = .binding owner payload := binding
    exact (EventField.binding.inj same).2.symm
  · have same : EventField.binding (L := simpleExpr) carol .bool = .binding owner payload := binding
    exact (EventField.binding.inj same).2.symm
  · have same : EventField.publication (L := simpleExpr) .bool = .binding owner payload := binding
    cases same
  · have same : EventField.publication (L := simpleExpr) .bool = .binding owner payload := binding
    cases same
  · have same : EventField.publication (L := simpleExpr) .bool = .binding owner payload := binding
    cases same

def trueBindingLaw (owner : Player) (event : graph.EventId) (payload : simpleExpr.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (_ : List app.PlayerEntry) (_ : app.PlayerView) : PMF (simpleExpr.Val payload) := by
  have same := binding_payload_bool owner event payload binding
  subst payload
  exact PMF.pure true

/-- The source-independent policy chooses fresh slots and truthful openings
through the existing bounded native service constructor. -/
def properPolicy
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player) :
    app.Policy :=
  phaseCountServicePolicy setup .concurrentReveals runtime leaks bounds trueBindingLaw rule
    0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num) owner

def lateAtRule (clock : Nat) (_owner : Player) (coordinate : CommitAttemptEvent graph)
    (clocks : List Nat) : Bool :=
  if coordinate.attempt = originalAttempt then decide (clocks.getLastD 0 = clock) else true

open Classical in
/-- The original first opportunity is skipped; the first packet is emitted
at clock two. Every later attempt uses its protected first opportunity. -/
def fixedLatePolicy (owner : Player) : app.Policy := fun past view =>
  if view.application.2.attempt = originalAttempt ∧ view.application.2.native.clock = 0 then
    PMF.pure ⟨none⟩
  else properPolicy (lateAtRule 2) owner past view

theorem properPolicy_counted
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (properPolicy rule owner past view).support) :
    response ∈ countedMenu.actions owner past view := by
  exact phaseCountServicePolicy_covered setup .concurrentReveals runtime leaks bounds
    trueBindingLaw rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    owner past view response supported

theorem fixedLatePolicy_counted (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (fixedLatePolicy owner past view).support) :
    response ∈ countedMenu.actions owner past view := by
  classical
  unfold fixedLatePolicy at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds owner past view
  · exact properPolicy_counted (lateAtRule 2) owner past view response supported

def properContinuation
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player) :
    rawModel.BehavioralPolicy owner :=
  rawMenu.restrictPolicy initial horizon scheduler owner (properPolicy rule owner)

def fixedLateContinuation (owner : Player) : rawModel.BehavioralPolicy owner :=
  rawMenu.restrictPolicy initial horizon scheduler owner (fixedLatePolicy owner)

theorem decode_properContinuation
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool) (owner : Player) :
    app.decodePolicy (rawMenu.embedPolicy initial horizon scheduler owner
      (properContinuation rule owner)) = properPolicy rule owner := by
  apply rawMenu.decode_restrictPolicy_of_covered
  intro past view action supported
  exact countedInRaw owner past view
    (properPolicy_counted rule owner past view action supported)

theorem decode_fixedLateContinuation (owner : Player) :
    app.decodePolicy (rawMenu.embedPolicy initial horizon scheduler owner
      (fixedLateContinuation owner)) = fixedLatePolicy owner := by
  apply rawMenu.decode_restrictPolicy_of_covered
  intro past view action supported
  exact countedInRaw owner past view
    (fixedLatePolicy_counted owner past view action supported)

/-- The concrete late deviation is silent at every actual original initial
callback, with its literal recalled word and view. -/
theorem fixedLatePolicy_initial (owner : Player) :
    fixedLatePolicy owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩ := by
  classical
  unfold fixedLatePolicy
  apply ite_eq_left
  have application : (initialCallback owner).application = initialState := by
    fin_cases owner <;> rfl
  change (initialCallback owner).application.attempt = originalAttempt ∧
    (initialCallback owner).application.current.native.clock = 0
  rw [application]
  exact ⟨initialState_attempt, initialState_clock⟩

end Vegas.Examples.CommitSeedBroadcast
