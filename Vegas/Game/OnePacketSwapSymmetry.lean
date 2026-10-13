/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketAcceptedTable
import Vegas.Pending.OnePacketValueSwap
import GameTheoryExtensions.Protocol.StateSymmetry

/-! # Hidden swaps as symmetries of the one-packet game

A hidden swap acts on the protocol states of the default runtime, keeping the
round counter and the actor (`Vegas.EventGraphRuntime.HiddenSwap.protocolState`),
and on joint actions, swapping each response
(`Vegas.EventGraphRuntime.HiddenSwap.joint`).

**The guard.** At a guarded execution every accepted binding handle is
compatible with the swap at its event, the swap fixes every resolution that is
ready or completed (its binding and the handles accepted for it), and every
recalled response has an evidence request the swap fixes
(`Vegas.SwapGuard`). The guard reaches back along every transition
(`Vegas.swapGuard_of_transition`).

**The symmetry.** When the initial law and the bounded values are closed under
the swap, every realized transition into a guarded state is sent to a realized
transition with swapped responses, which are one-packet responses again. So the
swap is a guarded state symmetry of the one-packet game
(`Vegas.onePacketSwapSymmetry`), and it is involutive
(`Vegas.onePacketSwapSymmetry_involutive`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {allowed : Set (graph setup).Inputs}

namespace EventGraphRuntime.HiddenSwap

variable (swap : HiddenSwap (graph setup))

/-- The swap of a control state: of its execution. -/
def control (current : (application setup leaks).Control) : (application setup leaks).Control :=
  ⟨current.remaining, current.actor, swap.execution current.execution⟩

/-- **The swap of a protocol state.** -/
def protocolState : (application setup leaks).ProtocolState →
    (application setup leaks).ProtocolState :=
  Option.map swap.control

/-- **The swap of a joint action**: of every response. -/
def joint (responses : Player → Option (application setup leaks).Action) :
    Player → Option (application setup leaks).Action :=
  fun who => (responses who).map swap.action

theorem control_involutive :
    Function.Involutive (swap.control (setup := setup) (leaks := leaks)) := by
  rintro ⟨remaining, actor, current⟩
  change (⟨remaining, actor, swap.execution (swap.execution current)⟩ :
    (application setup leaks).Control) = _
  rw [swap.execution_involutive]

theorem protocolState_involutive :
    Function.Involutive (swap.protocolState (setup := setup) (leaks := leaks)) := by
  intro state
  cases state with
  | none => rfl
  | some current => exact congrArg some (swap.control_involutive current)

theorem joint_involutive :
    Function.Involutive (swap.joint (setup := setup) (leaks := leaks)) := by
  intro responses
  funext who
  simp only [joint, Option.map_map]
  cases responses who with
  | none => rfl
  | some response => exact congrArg some (swap.action_involutive response)

theorem getD_joint (responses : Player → Option (application setup leaks).Action)
    (who : Player) :
    (swap.joint responses who).getD ⟨none⟩ = swap.action ((responses who).getD ⟨none⟩) := by
  simp only [joint]
  cases responses who <;> rfl

theorem requestFixed_action (response : (application setup leaks).Action) :
    swap.RequestFixed (swap.action response) ↔ swap.RequestFixed response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      constructor <;> intro _ submission sent <;> cases sent
  | some submission =>
      constructor
      · intro fixed other sent
        cases sent
        exact fixed (submission.swap swap) rfl
      · intro fixed other sent
        cases sent
        exact fixed submission rfl

end EventGraphRuntime.HiddenSwap

variable (setup) in
/-- **The swap guard** at an execution of the default runtime. -/
structure SwapGuard (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs)
    (current : (application setup leaks).Execution) : Prop where
  inputs : current.application.config.inputs ∈ allowed
  compatible : ∀ event candidate,
    current.application.accepted (.inr event) = some candidate →
      BindCompatible swap event candidate
  reveals : ∀ event, current.application.config.cut.Ready event ∨
      event ∈ current.application.config.cut.completed →
    RevealFixed swap current.application event
  requests : ∀ who, ∀ recalled ∈ current.recall who, swap.RequestFixed recalled.action

variable (setup) in
/-- The swap guard at a protocol state; nothing is asked before setup. -/
def SwapGuardState (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs) :
    (application setup leaks).ProtocolState → Prop
  | none => True
  | some current => SwapGuard setup swap allowed current.execution

/-- Accepted handles are never removed. -/
def AcceptedGrows (before after : EventGraphRuntime.State (graph setup)) : Prop :=
  ∀ field candidate, before.accepted field = some candidate → after.accepted field = some candidate

variable (leaks) in
theorem acceptedGrows_step :
    ((runtime setup).reactiveApplication leaks).StepRelation (AcceptedGrows (setup := setup)) where
  refl _ _ _ held := held
  submit state who material field candidate held := by
    change (submitStep (material.call.register state who) who
      material.call.packet).accepted field = _
    rw [submitStep_accepted, Submission.register_accepted]
    exact held
  handle state message next accepted field candidate held := by
    have call := reactiveHandle_call accepted
    cases packet : message.payload.call with
    | malformed raw =>
        rw [packet] at call
        simp [handle] at call
    | opening named other raw =>
        rw [packet] at call
        have tables := handle_resolution_tables (runtime setup) state next _
          (fun _ _ same => by cases same) call
        rw [tables.1]
        exact held
    | commitment named other =>
        rw [packet] at call
        obtain ⟨_, vacant, table, _⟩ :=
          handle_commitment_accepted state next message.id named other call
        rw [table]
        by_cases same : field = .inr named
        · subst same
          rw [vacant] at held
          cases held
        · rw [Function.update_of_ne same]
          exact held
  environment state command next reached field candidate held := by
    rw [(environmentStep_tables (runtime setup) state next command reached).1]
    exact held

/-- A ready or completed event stays ready or completed. -/
theorem readyOrCompleted_of_configStep {before after : (graph setup).Config}
    (step : ConfigStep setup before after) (event : (graph setup).EventId)
    (held : before.cut.Ready event ∨ event ∈ before.cut.completed) :
    after.cut.Ready event ∨ event ∈ after.cut.completed := by
  rcases step with same | ⟨other, ready, action, member⟩
  · rw [same]
    exact held
  · rw [before.step_cut other ready action after member]
    by_cases equal : event = other
    · subst equal
      exact Or.inr ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl))
    · rcases held with eventReady | completed
      · left
        refine ⟨fun member => ?_, fun predecessor member =>
          (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inr (eventReady.2 member))⟩
        rcases (EventOrder.Cut.mem_complete _ _ _ _).mp member with same | old
        · exact equal same
        · exact eventReady.1 old
      · exact Or.inr ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inr completed))

/-- A resolution fixed at a later state was fixed earlier. -/
theorem revealFixed_of_grows (swap : HiddenSwap (graph setup))
    {before after : EventGraphRuntime.State (graph setup)} (grows : AcceptedGrows before after)
    (event : (graph setup).EventId) (fixed : RevealFixed swap after event) :
    RevealFixed swap before event := by
  unfold RevealFixed at fixed ⊢
  cases view : nodeView (graph setup) event with
  | bind | sample => trivial
  | resolve owner payload binding checks outputEq codeEq =>
      rw [view] at fixed
      exact ⟨fixed.1, fun candidate held => fixed.2 candidate (grows _ _ held)⟩

/-- **The swap guard reaches back** along every transition. -/
theorem swapGuard_of_transition (swap : HiddenSwap (graph setup))
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (before after : (application setup leaks).Control)
    (joint : Player → Option (application setup leaks).Action)
    (reached : some after ∈ ((application setup leaks).transition initial horizon scheduler
      (some before) joint).support)
    (guarded : SwapGuard setup swap allowed after.execution) :
    SwapGuard setup swap allowed before.execution := by
  have grows := (acceptedGrows_step leaks).transition initial horizon scheduler before after joint
    reached
  have step := transition_configStep initial horizon scheduler before after joint reached
  obtain ⟨next, nextEq, prefixes⟩ := (application setup leaks).transition_recall_prefix initial
    horizon scheduler before (some after) joint reached
  cases Option.some.inj nextEq
  refine ⟨?_, fun event candidate held => guarded.compatible event candidate (grows _ _ held),
    fun event held => revealFixed_of_grows swap grows event
      (guarded.reveals event (readyOrCompleted_of_configStep step event held)),
    fun who recalled member => guarded.requests who recalled ((prefixes who).subset member)⟩
  rcases step with same | ⟨other, ready, action, member⟩
  · rw [← same]
    exact guarded.inputs
  · rw [EventGraph.Config.step, PMF.support_map] at member
    obtain ⟨_, _, completed⟩ := member
    have inputsEq := congrArg EventGraph.Config.inputs completed
    change before.execution.application.config.inputs = _ at inputsEq
    rw [inputsEq]
    exact guarded.inputs


/-- Including a packet with a valid token satisfies the inclusion conditions
when the source is guarded and the accepted handles after inclusion are
compatible. -/
theorem inclusionFixed_of_guard (swap : HiddenSwap (graph setup))
    (current : (application setup leaks).Execution) (id : MessageId Player)
    (envelope : Message Player (WitnessedPacket (graph setup)))
    (found : current.network.lookup id = some envelope)
    (valid : envelope.payload.tokenValid = true)
    (sourceGuard : SwapGuard setup swap allowed current)
    (targetCompatible : ∀ event candidate,
      (current.includePending (application setup leaks) id).application.accepted (.inr event) =
        some candidate → BindCompatible swap event candidate) :
    InclusionFixed (runtime setup) swap current.application
      ⟨envelope.id, envelope.payload.call⟩ := by
  refine ⟨fun next event candidate handled call => ?_,
    fun event _ ready => sourceGuard.reveals event (Or.inl ready)⟩
  have applicationEq :
      (current.includePending (application setup leaks) id).application = next := by
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change ((application setup leaks).handle current.application envelope).getD
      current.application = next
    rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ envelope valid, handled]
    rfl
  have accepted := handle_commitment_accepted current.application next envelope.id event candidate
    (by rw [← call]; exact handled)
  apply targetCompatible event candidate
  rw [applicationEq, accepted.2.2.1, Function.update_self]

/-- **Transitions into guarded states commute with the swap.** -/
theorem transition_swap (swap : HiddenSwap (graph setup))
    (initial : PMF (application setup leaks).State)
    (initialClosed : ∀ state ∈ initial.support, state.config.inputs ∈ allowed →
      state.swap swap ∈ initial.support)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (source target : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (reached : target ∈ ((application setup leaks).transition initial horizon scheduler source
      joint).support)
    (guarded : SwapGuardState setup swap allowed target) :
    swap.protocolState target ∈ ((application setup leaks).transition initial horizon scheduler
      (swap.protocolState source) (swap.joint joint)).support := by
  cases source with
  | none =>
      rw [ReactiveApplication.transition, PMF.support_map] at reached
      obtain ⟨state, member, rfl⟩ := reached
      change some (swap.control ⟨horizon, none, ReactiveApplication.Execution.initial _ state⟩) ∈
        ((application setup leaks).transition initial horizon scheduler none _).support
      rw [ReactiveApplication.transition, PMF.support_map]
      exact ⟨state.swap swap, initialClosed state member guarded.inputs, rfl⟩
  | some before =>
      rcases before with ⟨remaining, actor, current⟩
      cases target with
      | none =>
          exfalso
          obtain ⟨next, nextEq, _⟩ := (application setup leaks).transition_recall_prefix initial
            horizon scheduler ⟨remaining, actor, current⟩ none joint reached
          cases nextEq
      | some after =>
      have sourceGuard := swapGuard_of_transition swap initial horizon scheduler
        ⟨remaining, actor, current⟩ after joint reached guarded
      cases actor with
      | some who =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          change some (swap.control ⟨remaining, none, current.respond _ who _⟩) ∈
            ((application setup leaks).transition initial horizon scheduler
              (some ⟨remaining, some who, swap.execution current⟩) _).support
          rw [ReactiveApplication.transition, PMF.mem_support_pure_iff]
          change _ = some (⟨remaining, none, (swap.execution current).respond _ who
            ((swap.joint joint who).getD ⟨none⟩)⟩ : (application setup leaks).Control)
          rw [swap.getD_joint, swap.respond_execution]
          · rfl
          · change SwapGuard setup swap allowed (current.respond (application setup leaks) who
              ((joint who).getD ⟨none⟩)) at guarded
            generalize (joint who).getD ⟨none⟩ = response at guarded ⊢
            have member : ∃ recalled ∈ (current.respond (application setup leaks) who
                response).recall who, recalled.action = response := by
              rcases response with ⟨transmission⟩
              cases transmission <;>
              · simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
                exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
            obtain ⟨recalled, recalledMember, actionEq⟩ := member
            rw [← actionEq]
            exact guarded.requests who recalled recalledMember
      | none =>
          cases remaining with
          | zero =>
              cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
              exact (PMF.mem_support_pure_iff _ _).mpr rfl
          | succ remaining =>
              rw [ReactiveApplication.transition, PMF.mem_support_bind_iff] at reached
              obtain ⟨command, scheduled, moved⟩ := reached
              rw [PMF.support_map] at moved
              obtain ⟨next, stepped, nextEq⟩ := moved
              cases Option.some.inj nextEq
              change some (swap.control ⟨remaining, _, next⟩) ∈
                ((application setup leaks).transition initial horizon scheduler
                  (some ⟨remaining + 1, none, swap.execution current⟩) _).support
              rw [ReactiveApplication.transition, PMF.mem_support_bind_iff]
              refine ⟨command, ?_, ?_⟩
              · rw [swap.execution_environmentRecall, swap.observeEnvironment_execution]
                exact scheduled
              · rw [swap.environmentStep_execution current command, PMF.map_comp,
                  PMF.support_map]
                · exact ⟨next, stepped, rfl⟩
                · intro id envelope commandEq found valid
                  subst commandEq
                  refine inclusionFixed_of_guard swap current id envelope found valid sourceGuard
                    fun event candidate held => guarded.compatible event candidate ?_
                  unfold ReactiveApplication.Execution.environmentStep at stepped
                  rw [PMF.support_map] at stepped
                  obtain ⟨included, member, rfl⟩ := stepped
                  rw [PMF.mem_support_pure_iff] at member
                  subst member
                  exact held

/-- A response recorded at a guarded state has a fixed evidence request. -/
theorem requestFixed_of_respond (swap : HiddenSwap (graph setup))
    (current : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action)
    (guarded : SwapGuard setup swap allowed
      (current.respond (application setup leaks) who response)) :
    swap.RequestFixed response := by
  have member : ∃ recalled ∈ (current.respond (application setup leaks) who
      response).recall who, recalled.action = response := by
    rcases response with ⟨transmission⟩
    cases transmission <;>
    · simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  obtain ⟨recalled, recalledMember, actionEq⟩ := member
  rw [← actionEq]
  exact guarded.requests who recalled recalledMember

variable [Fintype Player]

/-- **The hidden swap is a guarded state symmetry of the one-packet game** when
the initial law and the bounded values are closed under it. -/
def onePacketSwapSymmetry (bounds : MessageBounds (graph setup))
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ initial.support, state.config.inputs ∈ allowed →
      state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values) :
    ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).StateSymmetry where
  map := swap.protocolState
  act _ := swap.joint
  Guard := SwapGuardState setup swap allowed
  map_init := rfl
  guard_source := by
    intro source target joint _ reached guarded
    cases source with
    | none => trivial
    | some before =>
        obtain ⟨after, rfl, _⟩ := (application setup leaks).transition_recall_prefix initial
          horizon scheduler before target joint reached
        exact swapGuard_of_transition swap initial horizon scheduler before after joint reached
          guarded
  legal := by
    intro source target joint isLegal reached guarded
    cases source with
    | none =>
        refine ⟨isLegal.1, fun who => ?_⟩
        have legalHere := isLegal.2 who
        cases chosen : joint who with
        | none =>
            simp only [HiddenSwap.joint, chosen, Option.map_none]
            rw [chosen] at legalHere
            exact legalHere
        | some response =>
            simp only [HiddenSwap.joint, chosen, Option.map_some]
            rw [chosen] at legalHere
            exact absurd legalHere.1 (by intro impossible; cases impossible)
    | some before =>
        obtain ⟨after, rfl, _⟩ := (application setup leaks).transition_recall_prefix initial
          horizon scheduler before target joint reached
        rcases before with ⟨remaining, actor, current⟩
        refine ⟨isLegal.1, fun who => ?_⟩
        have legalHere := isLegal.2 who
        cases chosen : joint who with
        | none =>
            simp only [HiddenSwap.joint, chosen, Option.map_none]
            rw [chosen] at legalHere
            exact legalHere
        | some response =>
            simp only [HiddenSwap.joint, chosen, Option.map_some]
            rw [chosen] at legalHere
            obtain ⟨active, available⟩ := legalHere
            refine ⟨active, ?_⟩
            have actorEq : actor = some who := active
            subst actorEq
            cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
            have fixed := requestFixed_of_respond swap current who _ guarded
            change swap.RequestFixed ((joint who).getD ⟨none⟩) at fixed
            rw [chosen] at fixed
            change swap.action response ∈ bounds.onePacketActions (runtime setup) leaks who
              ((current.recall who).map swap.entry)
              ((swap.execution current).observe (application setup leaks) who)
            rw [swap.observe_execution]
            exact bounds.swap_mem_onePacketActions swap who _ _ rfl response available fixed
              bounded
  realized := by
    intro source target joint isLegal reached guarded
    exact transition_swap swap initial initialClosed horizon scheduler source target joint
      reached guarded

/-- **The one-packet swap symmetry is involutive.** -/
theorem onePacketSwapSymmetry_involutive (bounds : MessageBounds (graph setup))
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ initial.support, state.config.inputs ∈ allowed →
      state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (allowedClosed : ∀ inputs ∈ allowed,
      (fun input => swap.values.value (.inl input) (inputs input)) ∈ allowed) :
    (onePacketSwapSymmetry bounds initial horizon scheduler swap initialClosed
      bounded).Involutive where
  map_map state _ := swap.protocolState_involutive state
  guard_map state guarded := by
    cases state with
    | none => trivial
    | some current =>
        obtain ⟨inputs, compatible, reveals, requests⟩ := guarded
        refine ⟨allowedClosed _ inputs, compatible, reveals, fun who recalled member => ?_⟩
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact (swap.requestFixed_action original.action).mpr
          (requests who original originalMember)
  act_act _ _ _ := swap.joint_involutive _
end Vegas
