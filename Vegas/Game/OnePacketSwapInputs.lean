/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapReplay

/-! # Inputs closed under a hidden swap

**The allowed inputs of a swap.** The inputs of an initial state that the swap
sends into the support of the initial law (`Vegas.swapAllowed`). Every initial
state is the initial state of its inputs, so the initial law is closed under the
swap at these inputs (`Vegas.initialClosed_swapAllowed`), and the swap, being
involutive, maps them to allowed inputs again (`Vegas.swapAllowed_closed`).

**Initial handles.** The swap of the initial state of some inputs is the initial
state of the swapped inputs when the swap acts on the candidate of every initial
binding handle as it acts on the input
(`Vegas.EventGraphRuntime.HiddenSwap.InitialHandlesCompatible`,
`Vegas.EventGraphRuntime.State.swap_initial`). The swap of pairs has this
property when each initial binding handle carries the raw pair of its input's
pair, and no pair when the input has none
(`Vegas.EventGraphRuntime.HiddenSwap.initialHandlesCompatible_ofPairs`).

**Inputs along a replay.** Along a native history with an intended replay, the
inputs are those of a setup draw whose cells the replay still finds, with their
values, at its end. So for two intended histories ending at p and q, the swap
between p and q maps the inputs of the draw of the first to the inputs of the
draw of the second, and the inputs of every native history replaying the first
are allowed (`Vegas.inputs_mem_swapAllowed`).
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- The swap of inputs: of each input value. -/
def HiddenSwap.inputs (swap : HiddenSwap graph) (inputs : graph.Inputs) : graph.Inputs :=
  fun input => swap.values.value (.inl input) (inputs input)

/-- **Compatible initial handles.** The swap acts on the candidate every initial
handle has for an input value as on that value. -/
def HiddenSwap.InitialHandlesCompatible (swap : HiddenSwap graph) : Prop :=
  ∀ (input : graph.InputId) (owner : Player) (value : (graph.inputLayout input).Value),
    swapCandidate (swap.raw (owner, .initial input))
        (State.candidateOfValue owner (graph.inputLayout input) value) =
      State.candidateOfValue owner (graph.inputLayout input)
        (swap.values.value (.inl input) value)

omit [DecidableEq Player] in
private theorem candidates_ext
    {first second : CommitmentCandidates Player (CandidateSlot graph) (Raw L)}
    (same : ∀ handle, first.lookup handle = second.lookup handle) : first = second := by
  rcases first with ⟨first⟩
  rcases second with ⟨second⟩
  congr 1
  funext owner slot
  exact same (owner, slot)

/-- **The swap of an initial state** is the initial state of the swapped inputs
when the initial handles are compatible. -/
theorem State.swap_initial (swap : HiddenSwap graph)
    (compatible : swap.InitialHandlesCompatible) (inputs : graph.Inputs) :
    (State.initial inputs).swap swap = State.initial (swap.inputs inputs) := by
  have candidates : swap.candidates (State.initial inputs).candidates =
      (State.initial (swap.inputs inputs)).candidates := by
    apply candidates_ext
    rintro ⟨owner, slot⟩
    rw [HiddenSwap.lookup_candidates, State.initial_candidate, State.initial_candidate]
    cases slot with
    | initial input => exact compatible input owner (inputs input)
    | prepared serial => rfl
  change State.mk _ _ (swap.candidates (State.initial inputs).candidates) _ _ = _
  rw [candidates]
  rfl

omit [IExpr.ResultTypes L] in
private theorem swapCandidate_candidateOfValue (owner : Player) :
    ∀ (kind : EventField Player L) (pair : Option (kind.Value × kind.Value))
      (rawPair : Option (Raw L × Raw L)),
      (∀ payload (kindEq : kind = .binding owner payload),
        (pair = none ∧ rawPair = none) ∨
          ∃ left right : L.Val payload,
            pair = some (cast (congrArg EventField.Value kindEq.symm) (.success left),
              cast (congrArg EventField.Value kindEq.symm) (.success right)) ∧
            rawPair = some (⟨payload, left⟩, ⟨payload, right⟩)) →
      ∀ value : kind.Value,
        swapCandidate (pairSwap rawPair) (State.candidateOfValue owner kind value) =
          State.candidateOfValue owner kind (pairSwap pair value)
  | .publicData _, _, _, _, _ => rfl
  | .publication _, _, _, _, _ => rfl
  | .privateInput _ _, _, _, _, _ => rfl
  | .binding inputOwner payload, pair, rawPair, paired, value => by
      classical
      by_cases same : inputOwner = owner
      · subst same
        rcases paired payload rfl with ⟨pairNone, rawNone⟩ | ⟨left, right, pairEq, rawEq⟩
        · subst pairNone rawNone
          cases value <;> simp [State.candidateOfValue, pairSwap]
        · subst pairEq rawEq
          change PublicationResult (L.Val payload) at value
          cases value with
          | failure =>
              have fixed : pairSwap (some ((PublicationResult.success left :
                  PublicationResult (L.Val payload)), PublicationResult.success right))
                  PublicationResult.failure = PublicationResult.failure :=
                pairSwap_of_ne _ _ _ (by simp) (by simp)
              simp only [cast_eq]
              rw [fixed]
              simp [State.candidateOfValue]
          | success value =>
              simp only [cast_eq]
              rw [pairSwap_map (fun value : L.Val payload =>
                  (PublicationResult.success value : PublicationResult (L.Val payload)))
                (fun _ _ same => PublicationResult.success.inj same)]
              simp only [State.candidateOfValue, ↓reduceIte, swapCandidate_openable]
              rw [pairSwap_map (fun value : L.Val payload => (⟨payload, value⟩ : Raw L))
                (fun _ _ same => by cases same; rfl)]
      · simp [State.candidateOfValue, same]

/-- **Initial handles carrying the raw pairs of their inputs are compatible**
with the swap of pairs: every initial binding handle carries no pair when its
input has none, and the raw pair of the input's pair of two successes
otherwise. -/
theorem HiddenSwap.initialHandlesCompatible_ofPairs (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L))
    (initialPairs : ∀ (input : graph.InputId) (owner : Player) (payload : L.Ty)
      (layoutEq : graph.inputLayout input = .binding owner payload),
      (pairs.pair (.inl input) = none ∧ handlePairs (owner, .initial input) = none) ∨
        ∃ left right : L.Val payload,
          pairs.pair (.inl input) =
            some (cast (congrArg EventField.Value layoutEq.symm) (.success left),
              cast (congrArg EventField.Value layoutEq.symm) (.success right)) ∧
          handlePairs (owner, .initial input) = some (⟨payload, left⟩, ⟨payload, right⟩)) :
    (HiddenSwap.ofPairs pairs handlePairs).InitialHandlesCompatible := by
  intro input owner value
  exact swapCandidate_candidateOfValue owner (graph.inputLayout input) (pairs.pair (.inl input))
    (handlePairs (owner, .initial input)) (initialPairs input owner) value

end Vegas.EventGraphRuntime

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **The allowed inputs of a swap**: the inputs of an initial state the swap
sends into the support of the initial law. -/
def swapAllowed (swap : HiddenSwap (graph setup)) : Set (graph setup).Inputs :=
  {inputs | ∃ state ∈ (initialLaw setup).support, state.config.inputs = inputs ∧
    state.swap swap ∈ (initialLaw setup).support}

/-- An initial state is the initial state of its inputs. -/
private theorem eq_initial_of_mem_initialLaw {state : EventGraphRuntime.State (graph setup)}
    (member : state ∈ (initialLaw setup).support) :
    state = EventGraphRuntime.State.initial state.config.inputs := by
  rw [initialLaw, serviceInitialLaw, PMF.support_map] at member
  obtain ⟨_, _, rfl⟩ := member
  rfl

/-- **The initial law is closed under the swap at the allowed inputs.** -/
theorem initialClosed_swapAllowed (swap : HiddenSwap (graph setup)) :
    ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ swapAllowed swap →
      state.swap swap ∈ (initialLaw setup).support := by
  rintro state member ⟨other, otherMember, sameInputs, swapped⟩
  rw [eq_initial_of_mem_initialLaw member, ← sameInputs, ← eq_initial_of_mem_initialLaw otherMember]
  exact swapped

/-- **The allowed inputs are closed under the swap.** -/
theorem swapAllowed_closed (swap : HiddenSwap (graph setup)) :
    ∀ inputs ∈ swapAllowed swap,
      (fun input => swap.values.value (.inl input) (inputs input)) ∈ swapAllowed swap := by
  rintro inputs ⟨state, member, rfl, swapped⟩
  exact ⟨state.swap swap, swapped, rfl, by rw [State.swap_involutive]; exact member⟩

section Replay

variable [DecidableEq (CellTy Player L)]

/-- A program point finds every cell of a setup draw with its value. -/
def InitialCellsAt (initial : State L setup.context) (point : ProtocolState setup.program) :
    Prop :=
  ∀ {name : VarId} {kind : CellTy Player L} (source : HasVar setup.context name kind),
    ProtocolState.cell? setup.program point name kind = some (initial.get source)

/-- The entry point of a setup draw finds its cells. -/
theorem initialCellsAt_entry (initial : State L setup.context) :
    InitialCellsAt initial (ProtocolState.entry setup.program (setup.initialConfig initial)) := by
  intro name kind source
  rw [ProtocolState.cell?_entry]
  exact State.cell?_eq_of_hasVar source setup.namesNodup initial

/-- The cells of a setup draw persist along a source step. -/
theorem initialCellsAt_step {initial : State L setup.context}
    {before after : ProtocolState setup.program} {joint : Player → Option (OwnAction Player L)}
    (reached : after ∈ (ProtocolState.step setup.program before joint).support)
    (found : InitialCellsAt initial before) : InitialCellsAt initial after :=
  fun source => ProtocolState.cell?_step setup.program reached (found source)

/-- **Every intended history ends where a setup draw's cells are found.** -/
theorem exists_initialCellsAt {state : setup.intendedProtocol.State}
    (trace : setup.intendedProtocol.Trace state) : ∀ {point : ProtocolState setup.program},
    state = some point →
      ∃ initial ∈ setup.initialLaw.support, InitialCellsAt initial point := by
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint legal realized ih =>
      intro point initialized
      subst initialized
      cases before with
      | none =>
          change some point ∈ (setup.initialLaw.map fun initial =>
            some (ProtocolState.entry setup.program (setup.initialConfig initial))).support
            at realized
          rw [PMF.support_map] at realized
          obtain ⟨initial, member, entered⟩ := realized
          cases Option.some.inj entered
          exact ⟨initial, member, initialCellsAt_entry initial⟩
      | some previous =>
          obtain ⟨initial, member, found⟩ := ih rfl
          change some point ∈ ((ProtocolState.step setup.program previous joint).map
            some).support at realized
          rw [PMF.support_map] at realized
          obtain ⟨next, reached, entered⟩ := realized
          cases Option.some.inj entered
          exact ⟨initial, member, initialCellsAt_step reached found⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq (CellTy Player L)] in
/-- Every position of a context is the position of a variable of it. -/
private theorem exists_inputId : ∀ (Γ : SourceCtx Player L) (input : Fin Γ.length),
    ∃ (name : VarId) (kind : CellTy Player L) (source : HasVar Γ name kind),
      inputId source = input
  | [], input => Fin.elim0 input
  | (name, kind) :: Γ, input => by
      cases input using Fin.cases with
      | zero => exact ⟨name, kind, .here, rfl⟩
      | succ input =>
          obtain ⟨other, otherKind, source, rfl⟩ := exists_inputId Γ input
          exact ⟨other, otherKind, .there source, rfl⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq (CellTy Player L)] in
private theorem swapFoundField_some_left {kind : CellTy Player L} (left right : CellVal L kind) :
    swapFoundField (some left) (some right) (cellValue left) = cellValue right := by
  classical
  cases kind <;> exact Equiv.swap_apply_left _ _

/-- **The swap between the ends of two intended histories moves the draw of the
first to the draw of the second.** -/
theorem inputs_betweenPairs {p q : ProtocolState setup.program}
    {publicAgree : PublicCellsAgree setup p q} {succeed : CommitmentCellsSucceed setup p q}
    {first second : State L setup.context} (firstCells : InitialCellsAt first p)
    (secondCells : InitialCellsAt second q) (input : (graph setup).InputId) :
    (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).value (.inl input)
        (setup.eventInputs first input) = setup.eventInputs second input := by
  obtain ⟨name, kind, source, rfl⟩ := exists_inputId setup.context input
  have layoutEq : (graph setup).layout (.inl (inputId source)) = cellField kind :=
    inputLayout_inputId source
  apply (cast_inj (congrArg EventGraph.EventField.Value layoutEq)).mp
  change cast _ (EventGraph.pairSwap (betweenPair setup p q (.inl (inputId source)))
    (setup.eventInputs first (inputId source))) = _
  rw [pairSwap_betweenPair (field := .inl (inputId source))
    (show fieldCell setup (.inl (inputId source)) = (name, kind) from inputId_get source)
    layoutEq, field_between, firstCells source, secondCells source]
  have firstValue := encodeInputs_get first source
  have secondValue := encodeInputs_get second source
  change cast _ (setup.eventInputs first (inputId source)) = _ at firstValue
  change cast _ (setup.eventInputs second (inputId source)) = _ at secondValue
  rw [firstValue, secondValue]
  exact swapFoundField_some_left _ _

omit [DecidableEq (CellTy Player L)] in
/-- The state of an existing extension is reached by the source step from the
extended state. -/
private theorem extendIntended?_reached {history result : setup.intendedProtocol.History}
    {choice : Option (OwnAction Player L)} {target : setup.ProtocolState}
    (extended : extendIntended? setup history choice target = some result) :
    result.state ∈ (setup.protocolStep history.state
      (actingJoint setup history.state choice)).support := by
  unfold extendIntended? at extended
  split at extended
  · split at extended
    · rename_i reached
      cases extended
      exact reached
    · cases extended
  · cases extended

variable [Fintype Player] {leaks : MessageNetwork.ObservationRule Player
    (WitnessedPacket (graph setup))} {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **The inputs along a replay.** Along a native history with an intended
replay, the inputs are those of a setup draw whose cells the replay finds at
its end. -/
theorem replay_initialCellsAt {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    ∀ {history : setup.intendedProtocol.History},
    intendedHistory? setup leaks bounds horizon scheduler trace = some history →
    ∀ control : (application setup leaks).Control, state = some control →
      ∃ initial ∈ setup.initialLaw.support,
        control.execution.application.config.inputs = setup.eventInputs initial ∧
        ∃ point, history.state = some point ∧ InitialCellsAt initial point := by
  induction trace with
  | start => intro _ _ _ initialized; cases initialized
  | @extend before after prior joint legal realized ih =>
      intro history replayed control initialized
      subst initialized
      obtain ⟨previous, previousReplay, advanced⟩ := Option.bind_eq_some_iff.mp replayed
      cases before with
      | none =>
          change extendIntended? setup previous none
            (decodedPoint setup control.execution.application.config) = some history
            at advanced
          have stateEq := extendIntended?_state advanced
          change some control ∈ ((application setup leaks).transition (initialLaw setup)
            horizon scheduler none joint).support at realized
          rw [ReactiveApplication.transition, PMF.support_map] at realized
          obtain ⟨drawn, drawnMember, drawnEq⟩ := realized
          cases Option.some.inj drawnEq
          have drawnSupport : drawn ∈ (initialLaw setup).support := drawnMember
          rw [initialLaw, serviceInitialLaw, PMF.support_map] at drawnSupport
          obtain ⟨initial, member, rfl⟩ := drawnSupport
          refine ⟨initial, member, rfl, _, ?_, initialCellsAt_entry initial⟩
          rw [stateEq]
          exact decodedPoint_initial initial
      | some current =>
          obtain ⟨initial, member, inputsEq, point, pointEq, found⟩ :=
            ih previousReplay current rfl
          have step := transition_configStep (initialLaw setup) horizon scheduler current
            control joint realized
          have sameInputs : control.execution.application.config.inputs =
              current.execution.application.config.inputs := by
            rcases step with same | ⟨other, ready, action, completed⟩
            · rw [same]
            · rw [EventGraph.Config.step, PMF.support_map] at completed
              obtain ⟨_, _, completedEq⟩ := completed
              exact (congrArg EventGraph.Config.inputs completedEq).symm
          refine ⟨initial, member, sameInputs.trans inputsEq, ?_⟩
          change (match control.execution.application.config.history.drop
              current.execution.application.config.history.length with
            | [] => some previous
            | [⟨event, action⟩] => extendIntended? setup previous
                (decodeEventAction setup.program event action)
                (decodedPoint setup control.execution.application.config)
            | _ => none) = some history at advanced
          split at advanced
          · cases advanced
            exact ⟨point, pointEq, found⟩
          · have reached := extendIntended?_reached advanced
            rw [pointEq, protocolStep_actingJoint, PMF.support_map] at reached
            obtain ⟨next, nextReached, nextEq⟩ := reached
            exact ⟨next, nextEq.symm, initialCellsAt_step nextReached found⟩
          · cases advanced

/-- **The inputs of a native history replaying an intended history are allowed**
by the swap between the end of that history and the end of any other intended
history, when the initial handles are compatible with the swap. -/
theorem inputs_mem_swapAllowed {first second : setup.intendedProtocol.History}
    {p q : ProtocolState setup.program} (firstState : first.state = some p)
    (secondState : second.state = some q)
    {publicAgree : PublicCellsAgree setup p q} {succeed : CommitmentCellsSucceed setup p q}
    (handlePairs : Handle (graph setup) → Option (Raw L × Raw L))
    (compatible : (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      handlePairs).InitialHandlesCompatible)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (replayed : intendedHistory? setup leaks bounds horizon scheduler trace = some first) :
    control.execution.application.config.inputs ∈
      swapAllowed (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs) := by
  obtain ⟨initial, member, inputsEq, point, pointEq, found⟩ :=
    replay_initialCellsAt trace replayed control rfl
  rw [firstState] at pointEq
  cases pointEq
  obtain ⟨other, otherMember, otherFound⟩ := exists_initialCellsAt second.trace secondState
  have drawnMember : ∀ draw ∈ setup.initialLaw.support,
      EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs draw) ∈
        (initialLaw setup).support := fun draw drawMember => by
    rw [initialLaw, serviceInitialLaw, PMF.support_map]
    exact ⟨draw, drawMember, rfl⟩
  refine ⟨_, drawnMember initial member, inputsEq.symm, ?_⟩
  rw [State.swap_initial _ compatible]
  have swapped : (HiddenSwap.ofPairs (betweenPairs publicAgree succeed) handlePairs).inputs
      (setup.eventInputs initial) = setup.eventInputs other :=
    funext (inputs_betweenPairs found otherFound)
  rw [swapped]
  exact drawnMember other otherMember

end Replay

end Vegas
