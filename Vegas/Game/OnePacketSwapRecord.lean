/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapSymmetry

/-! # Hidden swaps keep operational records and the observer's information

**Operational records.** At a guarded state the swap changes no operational
datum: not the scheduler's view or recall, not the network, and not any
player's late key, since an opening at a reveal turn reads a binding the guard
fixes (`Vegas.operationalState_swap`). So the image of a history under the swap
symmetry has the same operational record (`Vegas.operationalRecord_mapTrace`).

**The observer.** A swap that fixes every field visible to a player, its
actions and its handles fixes that player's view, and every one-packet response
of that player (`Vegas.EventGraphRuntime.HiddenSwap.action_eq_of_onePacket`),
since a permitted commitment names a handle of its sender. So along every
history the player's recall is fixed (`Vegas.recall_swap_of_fixes`), and the
image of a history leaves the player in the same information state
(`Vegas.infoOf_mapTrace_of_fixes`).
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

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem swapCandidate_id : swapCandidate (id : Raw L → Raw L) = id := by
  funext candidate
  cases candidate <;> rfl

namespace EventGraphRuntime.HiddenSwap

variable (swap : HiddenSwap (graph setup))

/-- The swap leaves a player's late-delivery key unchanged when every binding
read at a reveal turn of that player is fixed. -/
theorem lateKey_swap (who : Player) (past : List (application setup leaks).PlayerEntry)
    (observed : (application setup leaks).PlayerView)
    (fixed : ∀ event, observed.application.publicView.ownTurn? who = some event →
      EventGraph.ResolutionFixed swap.values event) :
    lateKey setup leaks who (some (past.map swap.entry, swap.view observed)) =
      lateKey setup leaks who (some (past, observed)) := by
  simp only [lateKey, List.map_map]
  congr 2
  · unfold deliveredValue
    change (match observed.application.publicView.ownTurn? who with
      | none => none
      | some event => _) = _
    cases turn : observed.application.publicView.ownTurn? who with
    | none => rfl
    | some event =>
        have fixedHere := fixed event turn
        unfold EventGraph.ResolutionFixed at fixedHere
        simp only
        cases view : nodeView (graph setup) event with
        | bind | sample => rfl
        | resolve owner payload binding checks outputEq codeEq =>
            rw [view] at fixedHere
            simp only
            congr 2
            apply binding.get?_congr
            change (observed.application.observation.store binding.field).map
              (swap.values.value binding.field) = _
            rw [fixedHere, Option.map_id, id_eq]

end EventGraphRuntime.HiddenSwap

/-- **The swap keeps the operational state** of a guarded protocol state. -/
theorem operationalState_swap (swap : HiddenSwap (graph setup))
    (state : (application setup leaks).ProtocolState)
    (guarded : SwapGuardState setup swap allowed state) :
    operationalState setup leaks (swap.protocolState state) =
      operationalState setup leaks state := by
  cases state with
  | none => rfl
  | some current =>
      change some _ = some _
      congr 1
      simp only [HiddenSwap.control,
        HiddenSwap.observeEnvironment_execution, HiddenSwap.execution_environmentRecall,
        HiddenSwap.execution_network, HiddenSwap.execution_recall, HiddenSwap.observe_execution]
      congr 1
      funext who
      apply swap.lateKey_swap who
      intro event turn
      have ready := (PublicView.ownTurn?_spec _ who event turn).1
      change current.execution.application.publicView.EventReady event at ready
      rw [State.publicView_eventReady] at ready
      have reveal := guarded.reveals event (Or.inl ready)
      unfold RevealFixed at reveal
      unfold EventGraph.ResolutionFixed
      cases view : nodeView (graph setup) event with
      | bind | sample => trivial
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at reveal
          exact reveal.1

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (application setup leaks).State} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **The image of a history has the same operational record.** -/
theorem operationalRecord_mapTrace (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (guarded : SwapGuardState setup swap allowed state),
    operationalRecord setup leaks bounds horizon scheduler
        ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap initialClosed
          bounded).mapTrace trace guarded) =
      operationalRecord setup leaks bounds horizon scheduler trace
  | _, .start, _ => rfl
  | _, .extend (target := target) prior joint isLegal reached, guarded => by
      rw [StateSymmetry.mapTrace_extend]
      simp only [operationalRecord]
      rw [operationalRecord_mapTrace swap initialClosed bounded prior]
      congr 1
      exact operationalState_swap swap target guarded


namespace EventGraphRuntime.HiddenSwap

variable (swap : HiddenSwap (graph setup))

/-- The swap **fixes a player** when it fixes every field visible to the player,
every action at the player's events and the value at every handle of the
player. -/
def Fixes (who : Player) : Prop :=
  (∀ field, (graph setup).fieldVisibleTo who field → swap.values.value field = id) ∧
    (∀ event, (graph setup).actor? event = some who → swap.values.action event = id) ∧
    ∀ slot, swap.raw (who, slot) = id

omit [Fintype Player] in
/-- A swap fixing a player fixes that player's view. -/
theorem view_observe_of_fixes {who : Player} (fixes : swap.Fixes who)
    (current : (application setup leaks).Execution) :
    swap.view (current.observe (application setup leaks) who) =
      current.observe (application setup leaks) who := by
  obtain ⟨fixedValues, fixedActions, fixedRaw⟩ := fixes
  change (⟨current.network.observe who,
    PlayerView.swap swap (current.application.playerView who), current.receipts⟩ :
      (application setup leaks).PlayerView) = ⟨current.network.observe who,
    current.application.playerView who, current.receipts⟩
  congr 1
  unfold PlayerView.swap State.playerView
  simp only [EventGraph.PlayerObservation.swap_eq_self swap.values fixedValues fixedActions]
  congr 1
  funext slot
  rw [fixedRaw slot, swapCandidate_id]
  rfl

/-- **A swap fixing a player fixes its one-packet responses**: a permitted
commitment names a handle of its sender. -/
theorem action_eq_of_onePacket {bounds : MessageBounds (graph setup)} {who : Player}
    (fixes : swap.Fixes who) {past : List (application setup leaks).PlayerEntry}
    {observed : (application setup leaks).PlayerView}
    {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past observed) :
    swap.action response = response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      obtain ⟨_, onePacket⟩ := (bounds.mem_onePacketActions _ _ _ _ _ _).mp member
      rcases onePacket with silent | ⟨material, sent, permitted⟩
      · cases silent
      · cases sent
        rw [countPermits_eq_true_iff] at permitted
        obtain ⟨_, correct, _⟩ := permitted
        unfold HiddenSwap.action
        simp only [Option.map_some]
        congr 2
        rcases submissionCall : submission with ⟨⟨packet, opening⟩, evidence⟩
        rw [submissionCall] at correct
        cases packet with
        | commitment event candidate =>
            have owned : candidate.1 = who := correct.2.2.1
            have handleEq : candidate = (who, candidate.2) := by rw [← owned]
            change WitnessedSubmission.mk ⟨_, opening.map (swap.raw candidate)⟩ evidence = _
            rw [handleEq, fixes.2.2 candidate.2, Option.map_id]
            rfl
        | opening | malformed => rfl

end EventGraphRuntime.HiddenSwap

/-- **A swap fixing the player fixes its recall** at each of its information
states. -/
theorem recall_swap_of_fixes (swap : HiddenSwap (graph setup)) {who : Player}
    (fixes : swap.Fixes who)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History)
    {past : List (application setup leaks).PlayerEntry}
    {observed : (application setup leaks).PlayerView}
    (decision : ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who history.trace = some (past, observed)) :
    past.map swap.entry = past := by
  conv_rhs => rw [← List.map_id past]
  apply List.map_congr_left
  intro recalled member
  obtain ⟨index, inside, rfl⟩ := List.getElem_of_mem member
  have legal := (bounds.onePacketMenu (runtime setup) leaks).recall_entry_legal initial horizon
    scheduler who history past observed decision index inside
  have info : ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who history.trace = (application setup leaks).observe who history.state :=
    (bounds.onePacketMenu (runtime setup) leaks).info initial horizon scheduler who history.trace
  rw [decision] at info
  rcases stateEq : history.state with _ | control
  · rw [stateEq] at info
    cases info
  · rw [stateEq] at info
    change some (past, observed) = (if control.actor = some who then
      some (control.execution.recall who, control.execution.observe _ who) else none) at info
    split at info
    · cases info
      have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace initial horizon
        scheduler (stateEq ▸ history.trace)
      obtain ⟨before, _, _, viewed⟩ := (application setup leaks).recorded_response_prefix initial
        horizon scheduler control rawTrace who _ member
      change (⟨swap.view _, swap.action _, _⟩ : (application setup leaks).PlayerEntry) = _
      rw [swap.action_eq_of_onePacket fixes legal, viewed, swap.view_observe_of_fixes fixes]
      rcases recalledEq : (control.execution.recall who)[index] with ⟨beforeView, action, emitted⟩
      rw [recalledEq] at viewed
      simp only at viewed ⊢
      rw [viewed]
      rfl
    · cases info

/-- **The image of a history leaves a fixed player in the same information
state** at each of its decisions. -/
theorem infoOf_mapTrace_of_fixes (swap : HiddenSwap (graph setup))
    (initialClosed : ∀ state ∈ initial.support, state.config.inputs ∈ allowed →
      state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    {who : Player} (fixes : swap.Fixes who)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History) (guarded : SwapGuardState setup swap allowed history.state)
    {past : List (application setup leaks).PlayerEntry}
    {observed : (application setup leaks).PlayerView}
    (decision : ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who history.trace = some (past, observed)) :
    ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who
      ((onePacketSwapSymmetry bounds initial horizon scheduler swap initialClosed
        bounded).mapTrace history.trace guarded) = some (past, observed) := by
  have fixedRecall := recall_swap_of_fixes swap fixes history decision
  have info : ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who history.trace = (application setup leaks).observe who history.state :=
    (bounds.onePacketMenu (runtime setup) leaks).info initial horizon scheduler who history.trace
  have mappedInfo : ((bounds.onePacketMenu (runtime setup) leaks).information initial horizon
      scheduler).infoOf who ((onePacketSwapSymmetry bounds initial horizon scheduler swap
        initialClosed bounded).mapTrace history.trace guarded) =
      (application setup leaks).observe who (swap.protocolState history.state) :=
    (bounds.onePacketMenu (runtime setup) leaks).info initial horizon scheduler who _
  rw [mappedInfo, ← decision, info]
  rcases history with ⟨state, trace⟩
  cases state with
  | none => rfl
  | some control =>
      change (if control.actor = some who then
          some ((control.execution.recall who).map swap.entry,
            (swap.execution control.execution).observe _ who) else none) =
        (if control.actor = some who then
          some (control.execution.recall who, control.execution.observe _ who) else none)
      split
      · rename_i active
        rw [info] at decision
        change (if control.actor = some who then
          some (control.execution.recall who, control.execution.observe _ who) else none) = _
          at decision
        simp only [active, ↓reduceIte] at decision
        cases decision
        rw [fixedRecall, swap.observe_execution, swap.view_observe_of_fixes fixes]
      · rfl
end Vegas
