/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapInfo
import Vegas.Game.OnePacketCounterpartSteps
import Vegas.Game.OnePacketProjectedDecision

/-! # Hidden swaps scale the source weight

Fix an observer `who` and a hidden swap that fixes every other player
(`Vegas.EventGraphRuntime.HiddenSwap.Fixes`).

**Chance mass.** The chance mass of a completed event is unchanged by the swap:
only samples carry chance mass, and a sample reads public fields only
(`Vegas.completionMass_swap`).

**Content factors.** At a response of another player the swap fixes the
responder's view and its one-packet response, and the source action the
transmission decodes to reads the candidate at the responder's own handle,
which the swap fixes (`Vegas.contentFactor_swap`).

**The source weight.** So the image of a history under the swap symmetry has
the source weight of the history, up to the ratio of the initial masses of the
two draws: when that ratio is a constant `c` on the allowed inputs, the source
weight of every history ending at a protocol state scales by `c`
(`Vegas.othersSourceWeight_mapTrace_scaled`).

**Regular histories.** The image of a history is regular exactly when the
history is, provided forcedness for `who` is invariant under the swap along
guarded histories (`Vegas.regularTrace_mapTrace_iff`). It is: every other player
sees the decoded points of a state and of its image alike, so neither is
excluded or owes a failure at one but not the other, and whether a reveal of
`who` failed is public, so any other player witnesses it
(`Vegas.forcedState_swap_iff`, `Vegas.regularTrace_mapTrace_iff_of_fixes`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {allowed : Set (graph setup).Inputs}

/-- A swap fixing the value at a handle keeps the binding result there. -/
private theorem bindingResult_swap_of_raw (swap : HiddenSwap (graph setup))
    (state : EventGraphRuntime.State (graph setup)) (handle : Handle (graph setup))
    (fixed : swap.raw handle = id) (payload : L.Ty) :
    (state.swap swap).bindingResult handle payload = state.bindingResult handle payload := by
  rw [State.swap_bindingResult, fixed, swapCandidate_id, id_eq, State.bindingResult_eq]

/-- **The decoded source action ignores the swap** when the swap fixes the
value at every handle the transmission commits. -/
theorem sentSourceAction_swap (swap : HiddenSwap (graph setup))
    (after : (application setup leaks).Execution) (action : (application setup leaks).Action)
    (fixed : ∀ material event handle, action.transmission = some material →
      material.call.packet = .commitment event handle → swap.raw handle = id) :
    sentSourceAction setup leaks (swap.execution after) action =
      sentSourceAction setup leaks after action := by
  rcases action with ⟨_ | material⟩
  · rfl
  · unfold sentSourceAction
    simp only
    cases packetEq : material.call.packet with
    | commitment event handle =>
        simp only
        split
        · rw [HiddenSwap.execution_application,
            bindingResult_swap_of_raw swap _ handle (fixed material event handle rfl packetEq)]
        · rfl
    | opening | malformed => rfl

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- A one-packet commitment names a handle of its sender. -/
theorem commitment_owner_of_onePacket {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {observed : (application setup leaks).PlayerView}
    {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past observed)
    {material : WitnessedSubmission (graph setup)} (sent : response.transmission = some material)
    {event : (graph setup).EventId} {handle : Handle (graph setup)}
    (packet : material.call.packet = .commitment event handle) :
    handle.1 = who := by
  obtain ⟨_, onePacket⟩ := (bounds.mem_onePacketActions _ _ _ _ _ _).mp member
  rcases onePacket with silent | ⟨submission, transmitted, permitted⟩
  · rw [sent] at silent
    cases silent
  · rw [sent] at transmitted
    cases transmitted
    rw [countPermits_eq_true_iff] at permitted
    obtain ⟨_, correct, _⟩ := permitted
    rcases materialEq : material with ⟨⟨packetValue, opening⟩, evidence⟩
    rw [materialEq] at correct packet
    cases packet
    exact correct.2.2.1

/-- **The swap keeps the content factor** of a one-packet response of a player
it fixes. -/
theorem contentFactor_swap (swap : HiddenSwap (graph setup))
    (assessment : setup.intendedModel.BehavioralAssessment) {actor : Player}
    (fixes : swap.Fixes actor) (before after : (application setup leaks).Execution)
    {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks actor
      (before.recall actor) (before.observe (application setup leaks) actor)) :
    contentFactor setup leaks assessment actor (swap.execution before) (swap.execution after)
        (swap.action response) =
      contentFactor setup leaks assessment actor before after response := by
  rw [swap.action_eq_of_onePacket fixes member]
  unfold contentFactor
  rw [swap.observe_execution, swap.view_observe_of_fixes fixes,
    sentSourceAction_swap swap after response fun material event handle sent packet => by
      have owned := commitment_owner_of_onePacket member sent packet
      have handleEq : handle = (actor, handle.2) := by rw [← owned]
      rw [handleEq]
      exact fixes.2.2 handle.2]

/-- The response of the actor of a legal joint action at a protocol state. -/
private theorem response_of_legal {control : (application setup leaks).Control}
    {joint : Player → Option (application setup leaks).Action}
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal (some control) joint)
    {actor : Player} (acting : control.actor = some actor) :
    ∃ response, joint actor = some response ∧
      response ∈ bounds.onePacketActions (runtime setup) leaks actor
        (control.execution.recall actor) (control.execution.observe (application setup leaks)
          actor) := by
  have localLegal := legal.2 actor
  have active : (application setup leaks).actor (some control) = some actor := acting
  cases picked : joint actor with
  | none =>
      rw [picked] at localLegal
      exact (localLegal active).elim
  | some response =>
      rw [picked] at localLegal
      exact ⟨response, rfl, localLegal.2⟩

/-- The content factor of a legal joint action at a protocol state, at a player
the swap fixes, is unchanged by the swap. -/
private theorem contentFactor_joint_swap (swap : HiddenSwap (graph setup))
    (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control} (after : (application setup leaks).Execution)
    {joint : Player → Option (application setup leaks).Action}
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal (some control) joint)
    {actor : Player} (acting : control.actor = some actor) (fixes : swap.Fixes actor) :
    contentFactor setup leaks assessment actor (swap.execution control.execution)
        (swap.execution after) ((swap.joint joint actor).getD ⟨none⟩) =
      contentFactor setup leaks assessment actor control.execution after
        ((joint actor).getD ⟨none⟩) := by
  obtain ⟨response, picked, member⟩ := response_of_legal legal acting
  rw [swap.getD_joint, picked, Option.getD_some]
  exact contentFactor_swap swap assessment fixes control.execution after member

/-- A realized transition from a protocol state reaches a protocol state. -/
private theorem target_some_of_realized {control : (application setup leaks).Control}
    {joint : Player → Option (application setup leaks).Action}
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal (some control) joint)
    {target : (application setup leaks).ProtocolState}
    (reached : target ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step
      (some control) ⟨joint, legal⟩).support) :
    ∃ next, target = some next := by
  obtain ⟨next, nextEq, _⟩ := (application setup leaks).transition_recall_prefix
    (initialLaw setup) horizon scheduler control target joint reached
  exact ⟨next, nextEq⟩

/-- **The swap keeps the source factor** of a transition between protocol states
when it fixes every player other than the observer. -/
theorem transitionSourceFactor_swap (swap : HiddenSwap (graph setup))
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (fixesOthers : ∀ other, other ≠ who → swap.Fixes other)
    {control next : (application setup leaks).Control}
    {joint : Player → Option (application setup leaks).Action}
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal (some control)
      joint) :
    transitionSourceFactor setup leaks assessment who (some (swap.control control))
        (swap.joint joint) (some (swap.control next)) =
      transitionSourceFactor setup leaks assessment who (some control) joint (some next) := by
  simp only [transitionSourceFactor, HiddenSwap.control]
  cases acting : control.actor with
  | none =>
      simp only [HiddenSwap.execution_application]
      exact completionMass_swap swap _ _
  | some actor =>
      by_cases owner : actor = who
      · simp only [owner, ↓reduceIte]
      · simp only [owner, ↓reduceIte]
        exact contentFactor_joint_swap swap assessment next.execution legal acting
          (fixesOthers actor owner)

/-- The source weight of the image of a history: the initial draw scales by the
ratio `c`, and every later source factor is unchanged. -/
private theorem othersSourceWeight_mapTrace_aux (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (fixesOthers : ∀ other, other ≠ who → swap.Fixes other) (c : ℝ)
    (priorScaled : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      (initialLaw setup (state.swap swap)).toReal = c * (initialLaw setup state).toReal) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (guarded : SwapGuardState setup swap allowed state),
    othersSourceWeight setup leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
          bounded).mapTrace trace guarded) =
      state.elim 1 (fun _ => c) *
        othersSourceWeight setup leaks bounds horizon scheduler assessment who trace
  | _, .start, _ => by
      change (1 : ℝ) = 1 * 1
      ring
  | _, .extend (source := source) (target := target) prior joint legal reached, guarded => by
      rw [StateSymmetry.mapTrace_extend]
      simp only [othersSourceWeight]
      rw [othersSourceWeight_mapTrace_aux swap initialClosed bounded assessment who fixesOthers c
        priorScaled prior]
      cases source with
      | none =>
          change target ∈ ((initialLaw setup).map _).support at reached
          rw [PMF.support_map] at reached
          obtain ⟨initial, member, rfl⟩ := reached
          have inputs : initial.config.inputs ∈ allowed := guarded.inputs
          change 1 * _ * (initialLaw setup (initial.swap swap)).toReal =
            c * (_ * (initialLaw setup initial).toReal)
          rw [priorScaled initial member inputs]
          ring
      | some control =>
          obtain ⟨next, rfl⟩ := target_some_of_realized legal reached
          change c * _ * transitionSourceFactor setup leaks assessment who
              (some (swap.control control)) (swap.joint joint) (some (swap.control next)) =
            c * (_ * _)
          rw [transitionSourceFactor_swap swap assessment who fixesOthers legal]
          ring

/-- **The swap scales the source weight.** When the swap fixes every player
other than the observer and scales the initial mass of every allowed draw by
`c`, the image of every history ending at a protocol state has `c` times its
source weight. -/
theorem othersSourceWeight_mapTrace_scaled (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (fixesOthers : ∀ other, other ≠ who → swap.Fixes other) (c : ℝ)
    (priorScaled : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      (initialLaw setup (state.swap swap)).toReal = c * (initialLaw setup state).toReal)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (guarded : SwapGuardState setup swap allowed (some control)) :
    othersSourceWeight setup leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
          bounded).mapTrace trace guarded) =
      c * othersSourceWeight setup leaks bounds horizon scheduler assessment who trace :=
  othersSourceWeight_mapTrace_aux swap initialClosed bounded assessment who fixesOthers c
    priorScaled trace guarded

/-- A player the swap fixes has the same information at the swapped state of a
history. -/
theorem observe_swap_of_fixes (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    {player : Player} (fixes : swap.Fixes player) {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (guarded : SwapGuardState setup swap allowed state) :
    (application setup leaks).observe player (swap.protocolState state) =
      (application setup leaks).observe player state := by
  have mapped := infoOf_mapTrace swap initialClosed bounded player trace guarded
  rw [onePacket_infoOf, onePacket_infoOf] at mapped
  change (application setup leaks).observe player (swap.protocolState state) = _ at mapped
  rw [mapped]
  cases observed : (application setup leaks).observe player state with
  | none => rfl
  | some current =>
      obtain ⟨past, view⟩ := current
      have decision : (onePacketInformation setup leaks bounds horizon scheduler).infoOf player
          trace = some (past, view) := by
        rw [onePacket_infoOf, observed]
      have fixedInfo := infoOf_mapTrace_of_fixes swap initialClosed bounded fixes ⟨state, trace⟩
        guarded decision
      have direct := infoOf_mapTrace swap initialClosed bounded player trace guarded
      rw [fixedInfo, onePacket_infoOf, observed] at direct
      exact direct.symm

/-- **The swap keeps regular steps** into guarded states, when forcedness for the
observer is invariant under the swap at guarded states. -/
theorem regularStep_swap_iff (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (fixesOthers : ∀ other, other ≠ who → swap.Fixes other)
    (forcedEq : ∀ state, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state →
      SwapGuardState setup swap allowed state →
      (ForcedState setup leaks who (swap.protocolState state) ↔ ForcedState setup leaks who state))
    {source target : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace source)
    {joint : Player → Option (application setup leaks).Action}
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal source joint)
    (reached : target ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step source
      ⟨joint, legal⟩).support)
    (sourceGuarded : SwapGuardState setup swap allowed source) :
    RegularStep setup leaks bounds horizon scheduler assessment who (swap.protocolState source)
        (swap.joint joint) (swap.protocolState target) ↔
      RegularStep setup leaks bounds horizon scheduler assessment who source joint target := by
  cases source with
  | none => exact Iff.rfl
  | some control =>
      obtain ⟨next, rfl⟩ := target_some_of_realized legal reached
      change (∀ actor, control.actor = some actor → actor ≠ who →
          (forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
              scheduler actor ((application setup leaks).observe actor
                (swap.protocolState (some control))) ∧
            ForcedState setup leaks who (swap.protocolState (some control))) ∧
          0 < contentFactor setup leaks assessment actor (swap.execution control.execution)
            (swap.execution next.execution) ((swap.joint joint actor).getD ⟨none⟩)) ↔ _
      apply forall_congr'
      intro actor
      apply forall_congr'
      intro acting
      apply forall_congr'
      intro owner
      rw [observe_swap_of_fixes swap initialClosed bounded (fixesOthers actor owner) prior
          sourceGuarded, forcedEq _ prior sourceGuarded,
        contentFactor_joint_swap swap assessment next.execution legal acting
          (fixesOthers actor owner)]

/-- **The image of a history is regular exactly when the history is**, when the
swap fixes every player other than the observer and forcedness for the observer
is invariant under the swap at guarded states. -/
theorem regularTrace_mapTrace_iff (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (fixesOthers : ∀ other, other ≠ who → swap.Fixes other)
    (forcedEq : ∀ state, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state →
      SwapGuardState setup swap allowed state →
      (ForcedState setup leaks who (swap.protocolState state) ↔
        ForcedState setup leaks who state)) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (guarded : SwapGuardState setup swap allowed state),
    RegularTrace setup leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
          bounded).mapTrace trace guarded) ↔
      RegularTrace setup leaks bounds horizon scheduler assessment who trace
  | _, .start, _ => Iff.rfl
  | _, .extend (source := source) (target := target) prior joint legal reached, guarded => by
      rw [StateSymmetry.mapTrace_extend]
      simp only [RegularTrace]
      exact and_congr
        (regularTrace_mapTrace_iff swap initialClosed bounded assessment who fixesOthers forcedEq
          prior _)
        (regularStep_swap_iff swap initialClosed bounded assessment who fixesOthers forcedEq prior
          legal reached
          ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
            bounded).guard_source prior legal reached guarded))

omit [Fintype Player] in
/-- A player the swap fixes sees the decoded points of a configuration and of
its swap alike. -/
theorem observe_decodedPoint_swap_of_fixes (swap : HiddenSwap (graph setup)) {player : Player}
    (fixes : swap.Fixes player) (execution : (application setup leaks).Execution)
    {point swapped : ProtocolState setup.program}
    (decoded : decodedPoint setup execution.application.config = some point)
    (swappedDecoded : decodedPoint setup (swap.execution execution).application.config =
      some swapped) :
    ProtocolState.observe player setup.program swapped =
      ProtocolState.observe player setup.program point := by
  obtain ⟨rank, ordered, read⟩ := decodedPoint_isPrefix decoded
  obtain ⟨swappedRank, swappedOrdered, swappedRead⟩ := decodedPoint_isPrefix swappedDecoded
  have original := projectView_observe setup leaks player execution rank ordered point read []
  have image := projectView_observe setup leaks player (swap.execution execution) swappedRank
    swappedOrdered swapped swappedRead []
  rw [swap.observe_execution, swap.view_observe_of_fixes fixes, original] at image
  exact (Option.some.inj image).symm

/-- **The swap keeps forcedness for the observer** at every state of a history
ending at a guarded state, when it fixes every other player and some other
player exists to witness the observer's public reveals. -/
theorem forcedState_swap_iff (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (who : Player) (fixesOthers : ∀ other, other ≠ who → swap.Fixes other)
    (observer : Player) (distinct : observer ≠ who)
    {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (guarded : SwapGuardState setup swap allowed state) :
    ForcedState setup leaks who (swap.protocolState state) ↔ ForcedState setup leaks who state := by
  cases state with
  | none => exact Iff.rfl
  | some control =>
      obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
        (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
      obtain ⟨swappedRank, ⟨swappedResidual⟩⟩ := protocol_sourceResidual
        (failureProfile setup.program) (bounds.onePacketMenu (runtime setup) leaks) horizon
        scheduler ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
          initialClosed bounded).mapTrace trace guarded) (swap.control control) rfl
      have decoded := decodedPoint_eq residual
      have swappedDecoded := decodedPoint_eq swappedResidual
      change ForcedState setup leaks who (some (swap.control control)) ↔ _
      rw [forcedState_iff_decodedPoint, forcedState_iff_decodedPoint, swappedDecoded, decoded]
      simp only [Option.some.injEq, exists_eq_left']
      generalize residual.lift (ProtocolState.entry residual.program residual.source) =
        point at decoded
      generalize swappedResidual.lift (ProtocolState.entry swappedResidual.program
        swappedResidual.source) = swapped at swappedDecoded
      have sameView : ∀ other, other ≠ who →
          ProtocolState.observe other setup.program swapped =
            ProtocolState.observe other setup.program point := fun other different =>
        observe_decodedPoint_swap_of_fixes swap (fixesOthers other different) control.execution
          decoded swappedDecoded
      unfold ForcedPoint
      refine and_congr (not_congr (ProtocolState.revealFailed_iff_of_observe_eq who observer
        setup.program swapped point (sameView observer distinct))) (forall_congr' fun other =>
          forall_congr' fun different => and_congr (not_congr
            (ProtocolState.excluded_iff_of_observe_eq other setup.program swapped point
              (sameView other different))) (not_congr ?_))
      have projected : projectView setup leaks other
          (some ([], (swap.execution control.execution).observe (application setup leaks)
            other)) =
          projectView setup leaks other
            (some ([], control.execution.observe (application setup leaks) other)) := by
        rw [swap.observe_execution, swap.view_observe_of_fixes (fixesOthers other different)]
      exact owesFailure_iff_of_projectView_eq other swappedDecoded decoded projected

/-- **The image of a history is regular exactly when the history is**, when the
swap fixes every player other than the observer and some other player exists. -/
theorem regularTrace_mapTrace_iff_of_fixes (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (fixesOthers : ∀ other, other ≠ who → swap.Fixes other)
    (observer : Player) (distinct : observer ≠ who)
    {state : (application setup leaks).ProtocolState}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (guarded : SwapGuardState setup swap allowed state) :
    RegularTrace setup leaks bounds horizon scheduler assessment who
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
          bounded).mapTrace trace guarded) ↔
      RegularTrace setup leaks bounds horizon scheduler assessment who trace :=
  regularTrace_mapTrace_iff swap initialClosed bounded assessment who fixesOthers
    (fun _ trace guarded => forcedState_swap_iff swap initialClosed bounded who fixesOthers
      observer distinct trace guarded) trace guarded

end Vegas
