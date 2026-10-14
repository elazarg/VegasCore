/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCounterpartImage
import Vegas.Game.OnePacketCounterpartSteps

/-! # Regular counterparts with dominated weight

The swap toward a forced witness (`Vegas.counterpart_of_witness`) also
dominates weights: when the response masses along a history are at most `K₁`
times those of their images under such swaps
(`Vegas.SwapResponseBound`), and at most `ε` times at the first irregular
response (`Vegas.SwapFirstBound`), an irregular history's upper source weight is
at most `ε (1 + error)` times `K` to the length bound times the source weight
of its counterpart (`Vegas.counterpart_bound_of_witness`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}

variable (setup leaks bounds horizon scheduler sequence profiles) in
/-- **Response masses compared under hidden swaps.** At stage `n`, every
response of a player other than `who` along a history ending at a state
guarded for a hidden swap, whose image under the swap is regular, has response
mass at most `K₁` times that of its image. -/
def SwapResponseBound (n : ℕ) (who : Player) (K₁ : ℝ) : Prop :=
  ∀ (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs) {before after}
    (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (_ : SwapGuardState setup swap allowed after)
    (control next : (application setup leaks).Control) (actor : Player),
    before = some control → after = some next → control.actor = some actor → actor ≠ who →
    RegularStep setup leaks bounds horizon scheduler (sequence n) who
      (swap.protocolState before) (swap.joint joint) (swap.protocolState after) →
    responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
      K₁ * responseMass setup leaks bounds horizon scheduler (profiles n) (swap.control control)
        (swap.joint joint)

variable (setup leaks bounds horizon scheduler sequence profiles) in
/-- **The first irregular response compared under hidden swaps.** At stage `n`,
an irregular response of a player other than `who` after a regular history,
whose image under a hidden swap is regular, has response mass at most `ε` times
that of its image. -/
def SwapFirstBound (n : ℕ) (who : Player) (ε : ℝ) : Prop :=
  ∀ (swap : HiddenSwap (graph setup)) (allowed : Set (graph setup).Inputs) {before after}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (_ : SwapGuardState setup swap allowed after)
    (control next : (application setup leaks).Control) (actor : Player),
    before = some control → after = some next → control.actor = some actor → actor ≠ who →
    RegularStep setup leaks bounds horizon scheduler (sequence n) who
      (swap.protocolState before) (swap.joint joint) (swap.protocolState after) →
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who prior →
    ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
    responseMass setup leaks bounds horizon scheduler (profiles n) control joint ≤
      ε * responseMass setup leaks bounds horizon scheduler (profiles n) (swap.control control)
        (swap.joint joint)

variable [DecidableEq (CellTy Player L)]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]

omit [DecidableEq (CellTy Player L)]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History] in
private theorem observe_of_infoOf'' {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (native : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (seen : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who native.trace =
      some (past, view)) {control : (application setup leaks).Control}
    (current : native.state = some control) :
    control.execution.observe (application setup leaks) who = view := by
  obtain ⟨state, trace⟩ := native
  change state = some control at current
  subst current
  rw [onePacket_infoOf] at seen
  by_cases active : control.actor = some who
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    exact (Prod.mk.inj (Option.some.inj seen)).2
  · simp [ReactiveApplication.observe, active] at seen

/-- **A regular counterpart with dominated weight.** For a well-formed setup,
under a fully mixed source assessment at stage `n`, at a decision input of
`who` at its own turn, take an irregular history `h` and a history `W` of the
input whose decoded point `w` leaves nobody owing a failure. When the
commitment cells where `h`'s decoded point `p` and `w` differ hold values at
both and the message bounds cover every binding field, some regular history of
the input has the operational record of `h` and source weight at least the
upper source weight of `h` divided by `ε (1 + error)` times `K` to the power
`2 * horizon + 1`. -/
theorem counterpart_bound_of_witness (wellFormed : setup.WellFormed)
    {who : Player} {steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who}
    (positive : ∀ n {before after : (application setup leaks).ProtocolState}
      (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint legal
      (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup leaks).Control),
      before = some control → after = some next →
      ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
      0 < responseMass setup leaks bounds horizon scheduler (profiles n) control joint →
      0 < steps.mass n (operationalState setup leaks before) (operationalState setup leaks after))
    (n : ℕ) (mixed : (sequence n).IsFullyMixed)
    {ι K₁ ε : ℝ} (ιPos : 0 < ι)
    (initialFloored : ∀ state ∈ (initialLaw setup).support, ι ≤ (initialLaw setup state).toReal)
    (K₁Nonneg : 0 ≤ K₁) (εNonneg : 0 ≤ ε)
    (responseBound : SwapResponseBound setup leaks bounds horizon scheduler sequence profiles n
      who K₁)
    (firstBound : SwapFirstBound setup leaks bounds horizon scheduler sequence profiles n who ε)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (history witness : (onePacketInformation setup leaks bounds horizon
      scheduler).InformationHistory who (some (past, view)))
    {current witnessControl : (application setup leaks).Control}
    (historyState : history.1.state = some current)
    (witnessState : witness.1.state = some witnessControl)
    {p w : ProtocolState setup.program}
    (decodedP : decodedPoint setup current.execution.application.config = some p)
    (decodedW : decodedPoint setup witnessControl.execution.application.config = some w)
    (freeW : ∀ player, ¬ ProtocolState.OwesFailure player setup.program w)
    (succeed : CommitmentCellsSucceed setup p w) (covered : BindingFieldsCovered bounds)
    (irregularHistory : ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace) :
    ∃ counterpart : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who (some (past, view)),
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who counterpart.1.trace ∧
      operationalRecord setup leaks bounds horizon scheduler counterpart.1.trace =
        operationalRecord setup leaks bounds horizon scheduler history.1.trace ∧
      upperSourceWeight (IrregularStepBound.ofResponseMass steps positive) n history.1.trace ≤
        ε * (1 + steps.error n) *
          max 1 (max (max (1 / ι) (1 / contentFloor setup leaks bounds horizon scheduler
            (sequence n))) (K₁ * (1 + steps.error n))) ^ (2 * horizon + 1) *
          othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who
            counterpart.1.trace := by
  have currentView := observe_of_infoOf'' history.1 history.2 historyState
  have witnessView := observe_of_infoOf'' witness.1 witness.2 witnessState
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change state = some current at historyState
  subst historyState
  obtain ⟨⟨witnessStateRaw, witnessTrace⟩, witnessSeen⟩ := witness
  change witnessStateRaw = some witnessControl at witnessState
  subst witnessState
  -- The two decoded points look alike to `who`.
  have sameSource := (sourceViewOf_eq_decodedPoint who trace).symm.trans
    ((congrArg (sourceViewOf setup leaks who) (currentView.trans witnessView.symm)).trans
      (sourceViewOf_eq_decodedPoint who witnessTrace))
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
  obtain ⟨second, secondReplay⟩ := intendedHistory?_isSome_of_debtFree wellFormed witnessTrace
    witnessControl rfl freeWitness
  have secondState : second.state = some w :=
    (intendedHistory?_state witnessTrace secondReplay).trans decodedW
  have staticW := decodedPoint_staticAt decodedW
  -- The swap guard at the end of `h`.
  have currentTurn : current.execution.application.publicView.ownTurn? who = some event := by
    rw [← currentView] at turn
    exact turn
  have readyOwn := readyOwn_of_ownTurn current.execution.application currentTurn
  let swap := HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
    (betweenHandlePairs setup p w current.execution.application.accepted)
  have guarded : SwapGuardState setup swap (swapAllowed swap) (some current) :=
    swapGuardState_of_decoded wellFormed secondState who sameView trace decodedP staticW
      readyOwn rfl
  have bounded := bounded_betweenHandlePairs (p := p) (q := w) (betweenPairs publicAgree succeed)
    current.execution.application.accepted covered
  have fixes : swap.Fixes who :=
    fixes_between sameView (fun _ _ accepted => accepted_owner_of_trace trace accepted)
  let symmetry := onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
    (initialClosed_swapAllowed swap) bounded
  have imageInfo := infoOf_mapTrace_of_fixes swap (initialClosed_swapAllowed swap) bounded
    fixes ⟨some current, trace⟩ guarded seen
  -- Nobody owes at the image's decoded point.
  have freeImage : ∀ point, decodedPoint setup (swap.control current).execution.application.config =
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
  have imageTurn : ((swap.control current).execution.observe (application setup leaks)
      who).application.publicView.ownTurn? who = some event := by
    change ((swap.execution current.execution).observe (application setup leaks)
      who).application.publicView.ownTurn? who = some event
    rw [HiddenSwap.observe_execution, swap.view_observe_of_fixes fixes, currentView]
    exact turn
  have imageRegular := regularTrace_of_debtFree wellFormed mixed who
    (symmetry.mapTrace trace guarded) freeImage imageTurn
  refine ⟨⟨⟨_, symmetry.mapTrace trace guarded⟩, imageInfo⟩, imageRegular,
    operationalRecord_mapTrace swap (initialClosed_swapAllowed swap) bounded trace guarded, ?_⟩
  have weight := upperSourceWeight_le_swap positive swap (initialClosed_swapAllowed swap)
    bounded n ιPos initialFloored K₁Nonneg εNonneg (responseBound swap (swapAllowed swap))
    (firstBound swap (swapAllowed swap)) trace guarded imageRegular irregularHistory
  refine weight.trans ?_
  set K := max 1 (max (max (1 / ι) (1 / contentFloor setup leaks bounds horizon scheduler
    (sequence n))) (K₁ * (1 + steps.error n)))
  have one_le : 1 ≤ K := le_max_left _ _
  have length : trace.length ≤ 2 * horizon + 1 :=
    le_trans (Nat.le_add_left _ _) (trace_length_le trace)
  have powerLe : K ^ trace.length ≤ K ^ (2 * horizon + 1) := pow_le_pow_right₀ one_le length
  have imageNonneg := othersSourceWeight_nonneg (sequence n) who
    (symmetry.mapTrace trace guarded)
  have errorNonneg := steps.error_nonneg n
  have front : 0 ≤ ε * (1 + steps.error n) := mul_nonneg εNonneg (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left powerLe front) imageNonneg

end Vegas
