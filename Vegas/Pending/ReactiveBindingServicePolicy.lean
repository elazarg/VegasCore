/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecordedResponse
import Vegas.Pending.ReactiveBindingServiceRule
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ReactiveCandidateBudget
import Vegas.Pending.ReactiveEmissionTokens
import Vegas.Pending.ReactiveSignedCommitments

/-! # Globally legal realizations of local binding rules -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- Realize a local clock/handle rule in the finite game. Impossible inputs use
silence; agreement at genuine unsent callbacks is proved from their operational
freshness, bounds and signed traffic. -/
def guardedBindingServiceResponse (bounds : MessageBounds graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) : (app).Action := by
  classical
  let response := runtime.bindingServiceResponse leaks owner event payload result choose past view
  exact if response ∈ bounds.onePacketActions runtime leaks owner past view then response
    else ⟨none⟩

/-- The realization remains legal even at arbitrary fabricated private inputs. -/
theorem guardedBindingServiceResponse_available (bounds : MessageBounds graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose past view ∈
      bounds.onePacketActions runtime leaks owner past view := by
  classical
  unfold guardedBindingServiceResponse
  dsimp only
  split
  · assumption
  · exact bounds.silence_onePacket runtime leaks owner past view

/-- The menu guard has no effect where the original response is admissible. -/
theorem guardedBindingServiceResponse_eq (bounds : MessageBounds graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (permitted : runtime.bindingServiceResponse leaks owner event payload result choose past view ∈
      bounds.onePacketActions runtime leaks owner past view) :
    runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose past view =
      runtime.bindingServiceResponse leaks owner event payload result choose past view := by
  classical
  exact ite_eq_left permitted

/-- Bounded fresh canonical bindings are admitted at every genuine unsent
callback, including after unrelated concurrent traffic. -/
theorem binding_onePacket_of_fresh_unsent
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : bindingOwnedBy graph owner event = true)
    (view : (app).PlayerView)
    (sameApp : view.application = (control.execution.observe app owner).application)
    (ready : control.execution.application.publicView.EventReady event)
    (result : PublicationResult (L.Val payload)) (slot : Nat)
    (fresh : control.execution.application.candidates.lookup (owner, .prepared slot) = .fresh)
    (capacity : slot < bounds.candidateCount)
    (bounded : ∀ value, result = .success value → (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (unsent : ((app).outputs (control.execution.recall owner)).filter
      (fun message => message.payload.call.event? graph = some event) = []) :
    runtime.reactiveBinding leaks owner event payload result slot ∈ bounds.onePacketActions
      runtime leaks owner (control.execution.recall owner)
        view := by
  classical
  let material : (app).Submission :=
    ⟨⟨.commitment event (owner, .prepared slot), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  have freshView : view.application.candidates (.prepared slot) = .fresh := by
    rw [sameApp]
    exact fresh
  have effective : runtime.reactiveBinding leaks owner event payload result slot ∈
      (bounds.menu runtime leaks).actions owner (control.execution.recall owner)
        view := by
    rw [← runtime.reactiveBinding_normal_of_fresh leaks owner (control.execution.recall owner)
      view event payload result slot freshView]
    exact bounds.binding_normalized_available runtime leaks owner (control.execution.recall owner)
      view event payload result slot capacity bounded
  refine (bounds.mem_onePacketActions runtime leaks owner (control.execution.recall owner)
    view _).mpr ⟨effective, Or.inr ⟨material, ?_, ?_⟩⟩
  · cases result <;> rfl
  have token : view.application.publicView.tokenFor
      (.commitment event (owner, .prepared slot)) = some ⟨event⟩ := by
    rw [sameApp]
    exact control.execution.application.publicView.tokenFor_of_eventReady
      (.commitment event (owner, .prepared slot)) event rfl ready
  have envelope : runtime.localEnvelope leaks owner (control.execution.recall owner)
      view material =
      ⟨(owner, (app).submissionCount (control.execution.recall owner)),
        ⟨.commitment event (owner, .prepared slot), none, some ⟨event⟩⟩⟩ := by
    change Message.mk _ (WitnessedPacket.mk _ none _) = _
    rw [token]
  have signed := runtime.signedCommitments_history leaks (inputs.map State.initial)
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨initial, rfl⟩) horizon scheduler trace
  apply (countPermits_eq_true_iff _ _).mpr
  rw [envelope]
  refine ⟨WitnessedPacket.tokenValid_commitment _ _ _, ?_, ?_⟩
  · refine ⟨?_, rfl, rfl, ⟨slot, rfl⟩, ?_⟩
    · exact binding
    · intro other earlier named call
      exact signed.ownFixed owner other earlier.1 named (.prepared slot) call fresh
  · intro other earlier named
    change other.payload.call.event? graph = some event at named
    have present : other ∈ ((app).outputs (control.execution.recall owner)).filter
        (fun message => message.payload.call.event? graph = some event) :=
      List.mem_filter.mpr ⟨earlier.1, by simpa only [decide_eq_true_eq] using named⟩
    rw [unsent] at present
    cases present

/-- Every response of the legal realization is silent or carries the fixed
selected-event binding result at its chosen handle. -/
theorem guardedBindingServiceResponse_cases (bounds : MessageBounds graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (choose : List Nat → Option Nat)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose past view =
        ⟨none⟩ ∨
      ∃ slot, runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose
        past view = runtime.reactiveBinding leaks owner event payload result slot := by
  classical
  unfold guardedBindingServiceResponse
  dsimp only
  split
  · unfold bindingServiceResponse
    split
    · cases choice : choose _ with
      | none => exact Or.inl rfl
      | some slot => exact Or.inr ⟨slot, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- The actual owner recall extends its fixed starting recall using only
silence or the selected event's canonical binding responses. -/
def BindingServiceEpisode (reference : List (app).PlayerEntry)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (execution : (app).Execution) : Prop :=
  ∃ suffix, execution.recall owner = reference ++ suffix ∧
    ∀ entry ∈ suffix, entry.action.transmission = none ∨
      ∃ slot, entry.action = runtime.reactiveBinding leaks owner event payload result slot

omit [Fintype Player] in
/-- The fixed starting recall initializes the concrete episode invariant. -/
theorem bindingServiceEpisode_initial
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (execution : (app).Execution) :
    runtime.BindingServiceEpisode leaks (execution.recall owner) owner event payload result
      execution :=
  ⟨[], (List.append_nil _).symm, fun _ member => False.elim (List.not_mem_nil member)⟩

/-- The guarded globally legal implementation preserves its real owner episode
against arbitrary foreign policies and environment commands. -/
theorem bindingServiceEpisode_policyInvariant (bounds : MessageBounds graph)
    (reference : List (app).PlayerEntry) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat) (players : Player → (app).Policy)
    (focal : players owner = fun past view => PMF.pure
      (runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose
        past view)) :
    (app).PolicyInvariant players
      (runtime.BindingServiceEpisode leaks reference owner event payload result) := by
  refine ⟨?_, ?_⟩
  · intro execution who response episode chosen
    obtain ⟨suffix, recalled, grammar⟩ := episode
    by_cases same : owner = who
    · subst who
      have responseEq : response = runtime.guardedBindingServiceResponse leaks bounds owner event
          payload result choose (execution.recall owner) (execution.observe app owner) := by
        rw [focal] at chosen
        exact (PMF.mem_support_pure_iff _ _).mp chosen
      obtain ⟨emitted, extended⟩ := (app).respond_recall_entry execution owner response
      refine ⟨suffix ++ [⟨execution.observe app owner, response, emitted⟩], ?_, ?_⟩
      · rw [extended, recalled, List.append_assoc]
      · intro entry member
        rcases List.mem_append.mp member with earlier | new
        · exact grammar entry earlier
        · cases List.mem_singleton.mp new
          rcases runtime.guardedBindingServiceResponse_cases leaks bounds owner event payload result
              choose (execution.recall owner) (execution.observe app owner) with silent | binding
          · exact Or.inl (congrArg ReactiveApplication.Action.transmission
              (responseEq.trans silent))
          · obtain ⟨slot, binding⟩ := binding
            exact Or.inr ⟨slot, responseEq.trans binding⟩
    · refine ⟨suffix, ?_, grammar⟩
      rw [(app).respond_recall_other execution who owner same response]
      exact recalled
  · intro execution next command episode moved
    obtain ⟨suffix, recalled, grammar⟩ := episode
    refine ⟨suffix, ?_, grammar⟩
    rw [(app).environmentStep_recall execution next command moved]
    exact recalled

omit [Fintype Player] in
/-- Until the selected packet is emitted, the episode uses no prepared slot
beyond those already named in its starting recall. This is an actual-history
statement, using faithful emission rather than an assumed delivery law. -/
theorem BindingServiceEpisode.slot_absent_of_unsent
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace (some control))
    (reference : List (app).PlayerEntry) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (episode : runtime.BindingServiceEpisode leaks reference owner event payload result
      control.execution)
    (slot : Nat) (available : slot ∉ runtime.submittedCandidateSlots leaks reference)
    (unsent : ((app).outputs (control.execution.recall owner)).filter
      (fun message => message.payload.call.event? graph = some event) = []) :
    slot ∉ runtime.submittedCandidateSlots leaks (control.execution.recall owner) := by
  obtain ⟨suffix, recalled, grammar⟩ := episode
  intro used
  unfold submittedCandidateSlots at used
  rw [recalled, List.map_append, List.filterMap_append, List.mem_append] at used
  rcases used with earlier | later
  · exact available earlier
  · obtain ⟨action, member, selected⟩ := List.mem_filterMap.mp later
    obtain ⟨entry, retained, rfl⟩ := List.mem_map.mp member
    rcases grammar entry retained with silent | binding
    · simp only [responseCandidateSlot, silent, reduceCtorEq] at selected
    · obtain ⟨chosenSlot, declared⟩ := binding
      have recorded : entry ∈ control.execution.recall owner := by
        rw [recalled]
        exact List.mem_append_right _ retained
      let material : (app).Submission :=
        ⟨⟨.commitment event (owner, .prepared chosenSlot), match result with
          | .failure => none
          | .success value => some ⟨payload, value⟩⟩, .none⟩
      have transmission : entry.action.transmission = some material := by
        rw [declared]
        cases result <;> rfl
      obtain ⟨message, emitted, call⟩ := (runtime.reactiveEmission_history leaks
        (inputs.map State.initial) horizon scheduler control trace owner).2 entry recorded material
          transmission
      have output : message ∈ (app).outputs (control.execution.recall owner) :=
        List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
      have named : message.payload.call.event? graph = some event := by rw [call]; rfl
      have present : message ∈ ((app).outputs (control.execution.recall owner)).filter
          (fun packet => packet.payload.call.event? graph = some event) :=
        List.mem_filter.mpr ⟨output, by simpa only [decide_eq_true_eq] using named⟩
      rw [unsent] at present
      cases present

/-- The globally legal realization agrees with its raw local rule at every
actual callback in the selected episode. Allowed handles are bounded and were
unmentioned in the fixed starting recall; their ongoing freshness is derived
from the episode and the actual native history. -/
theorem guardedBindingServiceResponse_eq_at_history
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace (some control))
    (reference : List (app).PlayerEntry) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat)
    (binding : bindingOwnedBy graph owner event = true)
    (bounded : ∀ value, result = .success value → (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (admissible : ∀ clocks slot, choose clocks = some slot → slot < bounds.candidateCount ∧
      slot ∉ runtime.submittedCandidateSlots leaks reference)
    (episode : runtime.BindingServiceEpisode leaks reference owner event payload result
      control.execution)
    (view : (app).PlayerView)
    (sameApp : view.application = (control.execution.observe app owner).application) :
    runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose
        (control.execution.recall owner) view =
      runtime.bindingServiceResponse leaks owner event payload result choose
        (control.execution.recall owner) view := by
  apply runtime.guardedBindingServiceResponse_eq leaks bounds owner event payload result choose
  unfold bindingServiceResponse
  split
  · rename_i active
    cases selected : choose _ with
    | none => exact bounds.silence_onePacket runtime leaks owner _ _
    | some slot =>
        obtain ⟨capacity, available⟩ := admissible _ slot selected
        have ready : control.execution.application.publicView.EventReady event := by
          have beforeReady := active.1
          rw [sameApp] at beforeReady
          exact beforeReady
        have unsent : ((app).outputs (control.execution.recall owner)).filter
            (fun message => message.payload.call.event? graph = some event) = [] := active.2
        have unused := episode.slot_absent_of_unsent runtime leaks inputs horizon scheduler control
          trace reference owner event payload result slot available unsent
        have fresh := (runtime.candidateRecall_history leaks inputs horizon scheduler trace) owner
          slot unused
        exact runtime.binding_onePacket_of_fresh_unsent leaks bounds inputs horizon scheduler
          control trace owner event payload binding view sameApp ready result slot fresh capacity
            bounded unsent
  · exact bounds.silence_onePacket runtime leaks owner _ _

end Vegas.EventGraphRuntime

end
