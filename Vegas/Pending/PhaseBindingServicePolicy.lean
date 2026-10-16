/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingWordKernel
import Vegas.Pending.PhaseSeedHistoryInput
import Vegas.Pending.PhaseCurrentTokens

/-! # Own-service binding choices in the actual phased counted menu -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

namespace PhaseSeedScheduler

/-- The complete activation-clock word for this exact physical attempt. The
current clock is appended before the current response has entered own recall. -/
def serviceClocks (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) : List Nat :=
  let input := informationInput runtime leaks coordinate owner past view
  input.activationClocks ++ [input.elapsed]

omit [Fintype Player] in
/-- At a genuine active callback this local rule reads exactly the scheduler's
preceding event-local query, with no foreign traffic or private source value. -/
theorem serviceClocks_of_trace (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (phaseApplication runtime leaks).Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩)) (coordinate : CommitAttemptEvent graph) :
    ∃ before : (phaseApplication runtime leaks).Execution,
      (.activate owner : (phaseApplication runtime leaks).Command) ∈
        (scheduler before.environmentRecall
          (before.observeEnvironment (phaseApplication runtime leaks))).support ∧
      execution ∈
        (before.environmentStep (phaseApplication runtime leaks) (.activate owner)).support ∧
      serviceClocks runtime leaks coordinate owner (execution.recall owner)
          (execution.observe (phaseApplication runtime leaks) owner) =
        let input := localInput runtime leaks coordinate owner before.environmentRecall
          (before.observeEnvironment (phaseApplication runtime leaks))
        input.activationClocks ++ [input.elapsed] := by
  obtain ⟨before, _recall, selected, reached, query⟩ := active_informationInput_of_trace
    runtime leaks menu initial horizon scheduler remaining owner execution trace coordinate
  exact ⟨before, selected, reached, congrArg
    (fun input : PhaseSeedInput graph => input.activationClocks ++ [input.elapsed]) query.symm⟩

end PhaseSeedScheduler

namespace PhaseCount

variable (bounds : MessageBounds graph)

open Classical in
/-- Choose WAIT or a prepared slot from this event's own activation clocks.
The source result is fixed separately. Existing word-policy guards supply
global menu legality, including at fabricated inputs and old namespaces. -/
def phaseBindingServicePolicy (owner : Player) (coordinate : CommitAttemptEvent graph)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat) : (phaseApplication runtime leaks).Policy := fun past view =>
  if PhaseRuntimeState.requests view.application.2 owner coordinate then
    match choose (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view) with
    | none => PMF.pure ⟨none⟩
    | some slot => phaseBindingWordPolicy runtime leaks bounds owner coordinate.event payload
        (fun _ _ => PMF.pure false) (fun _ _ => slot) 0 (by norm_num) (by norm_num)
        (fun _ : Unit => result) () past view
  else PMF.pure ⟨none⟩

/-- The existing counted-menu legality certificate covers the entire service
policy, not merely the particular execution used to select a rule. -/
theorem phaseBindingServicePolicy_covered (owner : Player)
    (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseBindingServicePolicy runtime leaks bounds owner coordinate
      payload result choose past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  classical
  unfold phaseBindingServicePolicy at supported
  split at supported
  · split at supported
    · cases (PMF.mem_support_pure_iff ..).mp supported
      exact silence_onePacket runtime leaks bounds owner past view
    · exact phaseBindingWordPolicy_covered runtime leaks bounds (supported := supported)
  · cases (PMF.mem_support_pure_iff ..).mp supported
    exact silence_onePacket runtime leaks bounds owner past view

/-- Two service rules agreeing on the current local clock word have identical
actual menu laws. Source result, native guards and the whole physical input are
retained, so the statement makes no independent posterior assertion. -/
theorem phaseBindingServicePolicy_eq_of_clocks (owner : Player)
    (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (first second : List Nat → Option Nat)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (same : first (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view) =
      second (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view)) :
    phaseBindingServicePolicy runtime leaks bounds owner coordinate payload result first past view =
      phaseBindingServicePolicy runtime leaks bounds owner coordinate payload result second
        past view := by
  classical
  unfold phaseBindingServicePolicy
  rw [same]

/-- At an actual unsent callback the requested fresh bounded slot transmits
exactly the fixed source result. The global guard is discharged from original
raw-history invariants rather than supplied as a legality hypothesis. -/
theorem phaseBindingServicePolicy_send_of_history (owner : Player)
    (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control))
    (output : graph.outputLayout coordinate.event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner coordinate)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall owner),
      event? message.payload ≠ some coordinate)
    (slot : Nat) (selected : choose (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
      (control.execution.recall owner)
      (control.execution.observe (phaseApplication runtime leaks) owner)) = some slot)
    (bounded : slot < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (owner, .prepared slot) = .fresh)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    phaseBindingServicePolicy runtime leaks bounds owner coordinate payload result choose
        (control.execution.recall owner)
        (control.execution.observe (phaseApplication runtime leaks) owner) =
      PMF.pure (phaseBindingResponse runtime leaks owner coordinate.event payload result slot) := by
  classical
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks _ horizon scheduler raw
  have recalled := countRecall_history runtime leaks raw
  obtain ⟨input, valid, _, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  have publicRequest : PhaseRuntimeState.requests
      (control.execution.observe (phaseApplication runtime leaks) owner).application.2
      owner coordinate :=
    (PhaseRuntimeState.requests_publicView _ valid owner coordinate).mpr request
  have same : coordinate = ⟨control.execution.application.attempt, coordinate.event⟩ := by
    cases coordinate with
    | mk attempt event =>
      exact congrArg (fun attempt : CommitAttemptId =>
        (⟨attempt, event⟩ : CommitAttemptEvent graph)) request.1
  have admissible (choice : PublicationResult (L.Val payload)) :
      phaseBindingResponse runtime leaks owner coordinate.event payload choice slot ∈
        onePacketActions runtime leaks bounds owner (control.execution.recall owner)
          (control.execution.observe (phaseApplication runtime leaks) owner) := by
    rw [mem_onePacketActions]
    refine ⟨phaseBindingResponse_available runtime leaks bounds owner _ _ coordinate.event payload
      values choice slot bounded, Or.inr ?_⟩
    apply phaseBindingResponse_permitted runtime leaks control.execution recalled fixed owner
      coordinate.event payload output (same ▸ request)
    · simpa only [← same] using unsent
    · exact fresh
  rw [phaseBindingServicePolicy, ite_eq_left publicRequest, selected]
  dsimp only
  unfold phaseBindingWordPolicy
  rw [ite_eq_left admissible]
  simp only [phaseBindingWordResponse, PMF.pure_bind, Bool.false_eq_true, ↓reduceIte]
  ext response
  simp only [mix_apply]
  norm_num

end PhaseCount

end Vegas.EventGraphRuntime
