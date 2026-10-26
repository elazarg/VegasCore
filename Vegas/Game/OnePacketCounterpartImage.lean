/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCounterpartGuard
import Vegas.Game.OnePacketDebtFreeRegular
import Vegas.Game.OnePacketSwapFiberSum

/-! # Regular counterparts by a swap toward a forced witness

Fix a decision input of `who` at `who`'s own turn, a history `h` of it, and a
history `W` of it whose decoded point leaves nobody owing a failure. Both
decoded points `p` and `w` look alike to `who`. When the commitment cells where
`p` and `w` differ hold values at both, and the message bounds cover every
binding field, the swap between `p` and `w`, at the handles accepted at the end
of `h`, maps `h` to a history of the same input
(`Vegas.infoOf_mapTrace_of_fixes`) with the same operational record
(`Vegas.operationalRecord_mapTrace`). Its decoded point is the swap of `p`,
which holds the cells of `w`, so nobody owes a failure there either, and the
image is regular under a fully mixed assessment
(`Vegas.counterpart_of_witness`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [DecidableEq (CellTy Player L)]

omit [DecidableEq (CellTy Player L)] in
private theorem observe_of_infoOf {who : Player}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (native : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    (seen : (onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf who
      native.trace =
      some (past, view)) {control : (application setup runtime leaks).Control}
    (current : native.state = some control) :
    control.execution.observe (application setup runtime leaks) who = view := by
  obtain ⟨state, trace⟩ := native
  change state = some control at current
  subst current
  rw [onePacket_infoOf] at seen
  by_cases active : control.actor = some who
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    exact (Prod.mk.inj (Option.some.inj seen)).2
  · simp [ReactiveApplication.observe, active] at seen

/-- **A regular counterpart toward a forced witness.** For a well-formed setup,
under a fully mixed assessment, at a decision input of `who` at its own turn,
take a history `h` and a history `W` of the input whose decoded point `w` leaves
nobody owing a failure. If the commitment cells where `h`'s decoded point `p`
and `w` differ hold values at both, and the message bounds cover every binding
field, then some regular history of the input has the operational record of
`h`. -/
theorem counterpart_of_witness (wellFormed : setup.WellFormed)
    {assessment : setup.intendedModel.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    {who : Player} {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (history witness : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who (some (past, view)))
    {current witnessControl : (application setup runtime leaks).Control}
    (historyState : history.1.state = some current)
    (witnessState : witness.1.state = some witnessControl)
    {p w : ProtocolState setup.program}
    (decodedP : decodedPoint setup current.execution.application.config = some p)
    (decodedW : decodedPoint setup witnessControl.execution.application.config = some w)
    (freeW : ∀ player, ¬ ProtocolState.OwesFailure player setup.program w)
    (succeed : CommitmentCellsSucceed setup p w) (covered : BindingFieldsCovered bounds) :
    ∃ counterpart : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who (some (past, view)),
      RegularTrace setup runtime leaks bounds horizon scheduler assessment who counterpart.1.trace ∧
      operationalRecord setup runtime leaks bounds horizon scheduler counterpart.1.trace =
        operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace := by
  have currentView := observe_of_infoOf (runtime := runtime) history.1 history.2 historyState
  have witnessView := observe_of_infoOf (runtime := runtime) witness.1 witness.2 witnessState
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change state = some current at historyState
  subst historyState
  obtain ⟨⟨witnessStateRaw, witnessTrace⟩, witnessSeen⟩ := witness
  change witnessStateRaw = some witnessControl at witnessState
  subst witnessState
  -- The two decoded points look alike to `who`.
  have sameSource := (sourceViewOf_eq_decodedPoint (runtime := runtime) who trace).symm.trans
    ((congrArg (sourceViewOf setup runtime leaks who) (currentView.trans witnessView.symm)).trans
      (sourceViewOf_eq_decodedPoint (runtime := runtime) who witnessTrace))
  rw [decodedP, decodedW] at sameSource
  have sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program w := Option.some.inj sameSource
  have publicAgree := publicCellsAgree_of_observe sameView
  -- The witness replays an intended history ending at `w`.
  have freeWitness : ∀ point, decodedPoint setup witnessControl.execution.application.config =
      some point → ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
    intro point decoded player
    rw [decodedW, Option.some.injEq] at decoded
    subst decoded
    exact freeW player
  obtain ⟨second, secondReplay⟩ := intendedHistory?_isSome_of_debtFree (runtime := runtime)
    wellFormed witnessTrace
    witnessControl rfl freeWitness
  have secondState : second.state = some w :=
    (intendedHistory?_state (runtime := runtime) witnessTrace secondReplay).trans decodedW
  have staticW := decodedPoint_staticAt decodedW
  -- The swap guard at the end of `h`.
  have currentTurn : current.execution.application.publicView.ownTurn? who = some event := by
    rw [← currentView] at turn
    exact turn
  have readyOwn := readyOwn_of_ownTurn current.execution.application currentTurn
  let swap := HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
    (betweenHandlePairs setup p w current.execution.application.accepted)
  have guarded : SwapGuardState setup runtime swap (swapAllowed swap) (some current) :=
    swapGuardState_of_decoded (runtime := runtime) wellFormed secondState who sameView trace
      decodedP staticW
      readyOwn rfl
  have bounded := bounded_betweenHandlePairs (p := p) (q := w) (betweenPairs publicAgree succeed)
    current.execution.application.accepted covered
  have fixes : swap.Fixes who :=
    fixes_between sameView (fun _ _ accepted => accepted_owner_of_trace (runtime := runtime) trace
      accepted)
  let symmetry := onePacketSwapSymmetry (runtime := runtime) bounds (initialLaw setup) horizon
    scheduler swap
    (initialClosed_swapAllowed swap) bounded
  have imageInfo := infoOf_mapTrace_of_fixes (runtime := runtime) swap (initialClosed_swapAllowed
    swap) bounded
    fixes ⟨some current, trace⟩ guarded seen
  refine ⟨⟨⟨_, symmetry.mapTrace trace guarded⟩, imageInfo⟩, ?_,
    operationalRecord_mapTrace (runtime := runtime) swap (initialClosed_swapAllowed swap) bounded
      trace guarded⟩
  -- Nobody owes at the image's decoded point.
  have freeImage : ∀ point, decodedPoint setup (swap.control
    current).execution.application.config =
      some point → ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
    intro point decoded player owes
    change decodedPoint setup (current.execution.application.config.swap
      (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed))) = some point at decoded
    rw [decodedPoint_betweenPairs, decodedP, Option.map_some, Option.some.injEq] at decoded
    subst decoded
    have staticP := decodedPoint_staticAt decodedP
    have same := ProtocolState.sameCells_between setup.program setup.namesNodup p w
      (ProtocolState.sameShape_of_observe_eq who setup.program p w sameView)
    exact freeW player ((ProtocolState.owesFailure_iff_of_sameCells player setup.program _ _ _ w
      (ProtocolState.staticAt_swap _ setup.program _ _ p staticP) staticW same).mp owes)
  have imageTurn : ((swap.control current).execution.observe (application
    setup runtime leaks)
      who).application.publicView.ownTurn? who = some event := by
    change ((swap.execution current.execution).observe (application setup runtime leaks)
      who).application.publicView.ownTurn? who = some event
    rw [HiddenSwap.observe_execution, swap.view_observe_of_fixes fixes,
      currentView]
    exact turn
  exact regularTrace_of_debtFree (runtime := runtime) wellFormed mixed who (symmetry.mapTrace
    trace guarded)
    freeImage imageTurn

end Vegas
