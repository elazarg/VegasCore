/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSplicePoint
import Vegas.Game.OnePacketSwapFiberSum
import Vegas.Game.OnePacketSwapBaseWeight
import Vegas.Game.OnePacketCellObservation

/-! # Responders along a history at a forced site are forced

Fix a history `h` ending at an own turn of `who`, with decoded point `p`, and an
intended point `w` that `who` observes like `p` and at which nobody owes a
failure. A responder `r ≠ who` at a state along `h` may owe at `p` (its own
cells may be the ones that went wrong), and the swap between `p` and `w` may
move what `r` sees. Splicing `p` and `w` for `r`
(`Vegas.SourceProgram.ProtocolState.splicePoint`) keeps `r`'s hidden cells and
takes everybody else's from `w`. With hidden initial cells independent given a public
signal, the swap between `p` and the splice is guarded at the end of `h`, so it maps `h` and each
of its prefixes to histories (`Vegas.forcedAgent_of_splice`):

* it fixes `r`, so the image of each prefix carries `r`'s information there;
* at the image of the end of `h`, every player other than `r` observes its cells
  as at `w`, so nobody but `r` owes a failure or is excluded; and `r`'s failed
  reveals are publications, which `who` observes as at `w`, where none failed
  (`Vegas.not_revealFailed_splice`). So the image is in a forced state of `r`
  (`Vegas.forcedPoint_splice`), and so is the image of every prefix, since
  forced states reach back along transitions.

Hence every responder along `h` acts at an information state forced for it.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]

variable {Public : Type*} {signal : State L setup.context → Public}

section Points

variable {p q w : ProtocolState setup.program} {r : Player}

/-- **The swap between two points at the same position finds the second point's
cells at the first.** -/
theorem cell?_between_self (shape : ProtocolState.SameShape setup.program p q) (name : VarId)
    (kind : CellTy Player L) :
    ProtocolState.cell? setup.program
        ((CellSwap.between setup.program p q).protocolState setup.program p) name kind =
      ProtocolState.cell? setup.program q name kind := by
  have found := ProtocolState.isSome_cell?_eq_of_sameShape name kind setup.program p q shape
  rw [ProtocolState.cell?_swap]
  cases pFound : ProtocolState.cell? setup.program p name kind with
  | none =>
      rw [pFound] at found
      cases qFound : ProtocolState.cell? setup.program q name kind with
      | none => rfl
      | some _ => rw [qFound] at found; cases found
  | some left =>
      rw [pFound] at found
      cases qFound : ProtocolState.cell? setup.program q name kind with
      | none => rw [qFound] at found; cases found
      | some right =>
          simp [CellSwap.between, pFound, qFound, swapFound]

/-- At the swap of `p` toward its splice with `w` for `r`, every player other
than `r` observes its cells as at `w`. -/
theorem observedAlike_between_splice (shape : ProtocolState.SameShape setup.program p w)
    {other : Player} (different : other ≠ r) :
    ProtocolState.ObservedAlike other setup.program
      ((CellSwap.between setup.program p
        (ProtocolState.splicePoint setup.program r p w)).protocolState setup.program p) w := by
  have spliceShape : ProtocolState.SameShape setup.program p
      (ProtocolState.splicePoint setup.program r p w) :=
    ProtocolState.sameShape_swap _ setup.program p
  refine ProtocolState.observedAlike_of_cell? other setup.program setup.namesNodup _ _
    (ProtocolState.sameShape_swap_left _ setup.program p w shape) fun name kind visible => ?_
  rw [cell?_between_self spliceShape]
  refine ProtocolState.cell?_splicePoint_of_not_hidden ?_ shape
  cases kind with
  | publicData => simp [CellTy.hiddenOwner?]
  | publication => simp [CellTy.hiddenOwner?]
  | commitment owner payload =>
      cases (visible : owner = other)
      simpa [CellTy.hiddenOwner?] using different
  | privateInput owner payload =>
      cases (visible : owner = other)
      simpa [CellTy.hiddenOwner?] using different

/-- **No failed reveal of `r` at the splice image.** The swap of `p` toward its
splice with an intended point `w` for `r` holds no failed reveal of `r`: failed
reveals are publications, which any other player `who` observes there as at
`w`, and an intended point has none. This holds even when `r` itself owes at
`p`. -/
theorem not_revealFailed_splice (shape : ProtocolState.SameShape setup.program p w)
    (intendedW : ProtocolState.Intended setup.program w) {who : Player} (different : who ≠ r) :
    ¬ ProtocolState.RevealFailed r setup.program
      ((CellSwap.between setup.program p
        (ProtocolState.splicePoint setup.program r p w)).protocolState setup.program p) :=
  fun failed => (forcedPoint_of_intended r intendedW).1
    ((ProtocolState.revealFailed_iff_of_observedAlike r who setup.program _ _
      (observedAlike_between_splice shape different)).mp failed)

/-- **The splice image is forced for `r`.** At the swap of a point `p`, carrying
the registry and publication status of its program point, toward its splice with
an intended point `w` for `r`, both carrying the registry and publication status
of their program point, `r` has no failed reveal and nobody else is excluded or
owes a failure, provided some player other than `r` exists. -/
theorem forcedPoint_splice (shape : ProtocolState.SameShape setup.program p w)
    (staticP : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) p)
    (staticW : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) w)
    (intendedW : ProtocolState.Intended setup.program w) {who : Player} (different : who ≠ r) :
    ForcedPoint setup r
      ((CellSwap.between setup.program p
        (ProtocolState.splicePoint setup.program r p w)).protocolState setup.program p) := by
  refine ⟨not_revealFailed_splice shape intendedW different, fun other otherDifferent =>
    ⟨fun excluded => ((forcedPoint_of_intended r intendedW).2 other otherDifferent).1
      ((ProtocolState.excluded_iff_of_observedAlike other setup.program _ _
        (observedAlike_between_splice shape otherDifferent)).mp excluded),
    fun owes => ((forcedPoint_of_intended r intendedW).2 other otherDifferent).2
      ((ProtocolState.owesFailure_iff_of_observedAlike other setup.program _ _ _ _
        (ProtocolState.staticAt_swap _ setup.program _ _ p staticP) staticW
        (observedAlike_between_splice shape otherDifferent)).mp owes)⟩⟩

end Points

section Native

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [DecidableEq (CellTy Player L)] in
/-- An initialized history is no prefix of the empty history. -/
theorem not_tracePrefix_start {control : (application setup leaks).Control}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control)}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace none) :
    ¬ TracePrefix prior trace := by
  intro isPrefix
  have length := isPrefix.length_le
  rw [trace_eq_start_of_none trace] at length
  have positive : ∀ {state}
      (prefixTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
      state = some control → 0 < prefixTrace.length := by
    intro state prefixTrace initialized
    cases prefixTrace with
    | start => cases initialized
    | extend => simp [Trace.length]
  have := positive prior rfl
  simp [Trace.length] at length
  omega

omit [DecidableEq (CellTy Player L)] in
/-- **Forced images reach back along a history.** If the image under a hidden
swap of a history guarded at its end is forced for a player, so is the image of
each of its initialized prefixes. -/
theorem forcedState_image_of_tracePrefix (swap : HiddenSwap (graph setup))
    {allowed : Set (graph setup).Inputs}
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (r : Player) {control : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {state} {trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state}
    (isPrefix : TracePrefix prior trace) (guarded : SwapGuardState setup swap allowed state)
    (forced : ForcedState setup leaks r (swap.protocolState state)) :
    ForcedState setup leaks r (some (swap.control control)) := by
  let symmetry := onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
    initialClosed bounded
  induction isPrefix with
  | refl => exact forced
  | @extend source target before earlier joint legal realized ih =>
      cases source with
      | none => exact (not_tracePrefix_start before earlier).elim
      | some previous =>
          have guardSource := symmetry.guard_source before legal realized guarded
          exact ih guardSource (forcedState_of_transition
            (symmetry.mapTrace before guardSource) (symmetry.act (some previous) joint)
            (symmetry.realized before legal realized guarded) forced)

omit [DecidableEq (CellTy Player L)] in
/-- The swap guard reaches back along a history. -/
theorem swapGuardState_of_tracePrefix (swap : HiddenSwap (graph setup))
    {allowed : Set (graph setup).Inputs}
    (initialClosed : ∀ state ∈ (initialLaw setup).support, state.config.inputs ∈ allowed →
      state.swap swap ∈ (initialLaw setup).support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    {first : (application setup leaks).ProtocolState}
    {prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace first}
    {state} {trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state}
    (isPrefix : TracePrefix prior trace) (guarded : SwapGuardState setup swap allowed state) :
    SwapGuardState setup swap allowed first := by
  let symmetry := onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
    initialClosed bounded
  induction isPrefix with
  | refl => exact guarded
  | @extend _ _ before earlier joint legal realized ih =>
      exact ih (symmetry.guard_source before legal realized guarded)

/-- **Responders along a history at a forced site are forced.** Take a history
ending at a state `current` with decoded point `p`, at which every ready reveal
belongs to `who`, and the end `w` of an intended history that `who` observes like
`p`, at which nobody owes a failure. Assume the commitments changed by the splice
that retains the responder's hidden cells are successful. With hidden initial cells
independent given a publicly determined signal and bounds covering every binding field, every player
`r ≠ who` acting at a state along the history acts at an information state
forced for it. -/
theorem forcedAgent_of_splice (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) (covered : BindingFieldsCovered bounds)
    {who : Player} {current : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current))
    {p w : ProtocolState setup.program}
    (decodedP : decodedPoint setup current.execution.application.config = some p)
    {second : setup.intendedProtocol.History} (secondState : second.state = some w)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program w)
    (staticW : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) w)
    (readyOwn : ∀ event, current.execution.application.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who)
    {r : Player}
    (succeed : CommitmentCellsSucceed setup p (ProtocolState.splicePoint setup.program r p w))
    {control : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (isPrefix : TracePrefix prior trace) (different : r ≠ who) :
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
      r ((application setup leaks).observe r (some control)) := by
  have publicAgree := publicCellsAgree_of_observe sameView
  have shape := ProtocolState.sameShape_of_observe_eq who setup.program p w sameView
  let q := ProtocolState.splicePoint setup.program r p w
  have publicAgreeQ : PublicCellsAgree setup p q := publicCellsAgree_splicePoint publicAgree
  have succeedQ : CommitmentCellsSucceed setup p q := succeed
  let swap := HiddenSwap.ofPairs (betweenPairs publicAgreeQ succeedQ)
    (betweenHandlePairs setup p q current.execution.application.accepted)
  -- The swap toward the splice is guarded at the end of the history.
  have drawnP : ∃ initial ∈ setup.initialLaw.support, InitialCellsAt initial p := by
    obtain ⟨initial, member, _, point, pointEq, found⟩ := decoded_initialCellsAt trace current rfl
    rw [decodedP, Option.some.injEq] at pointEq
    subst pointEq
    exact ⟨initial, member, found⟩
  have drawn := drawn_splicePoint (r := r) independent observable publicAgree drawnP
    (exists_initialCellsAt second.trace secondState)
  have staticP := decodedPoint_staticAt decodedP
  have guarded : SwapGuardState setup swap (swapAllowed swap) (some current) :=
    swapGuardState_of_agree drawn trace decodedP
      (fun event active owner payload binding checks outputEq codeEq view =>
        cell?_splicePoint_eq_of_agree (bindingCellsAgree_of_decoded (event := event)
          (owner := owner) (payload := payload) (binding := binding) (checks := checks)
          (outputEq := outputEq) (codeEq := codeEq) wellFormed secondState who sameView trace
          decodedP staticW readyOwn active view)) rfl
  have bounded := bounded_betweenHandlePairs (p := p) (q := q)
    (betweenPairs publicAgreeQ succeedQ) current.execution.application.accepted covered
  have fixes : swap.Fixes r :=
    fixes_between_of_visible (fun name _ visible => cell?_splicePoint_of_visible publicAgree name
      visible) (fun _ _ accepted => accepted_owner_of_trace trace accepted)
  -- The image of the end of the history is forced for `r`.
  have forcedEnd : ForcedState setup leaks r (some (swap.control current)) := by
    refine (forcedState_iff_decodedPoint _).mpr ⟨_, ?_,
      forcedPoint_splice shape staticP staticW
        (intended_of_history wellFormed second.trace w secondState) (Ne.symm different)⟩
    change decodedPoint setup (current.execution.application.config.swap
      (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgreeQ succeedQ))) = _
    rw [decodedPoint_betweenPairs, decodedP, Option.map_some]
  -- So is the image of the prefix, which carries `r`'s information there.
  have guardedPrior := swapGuardState_of_tracePrefix swap (initialClosed_swapAllowed swap) bounded
    isPrefix guarded
  have forcedPrior := forcedState_image_of_tracePrefix swap (initialClosed_swapAllowed swap)
    bounded r prior isPrefix guarded forcedEnd
  let symmetry := onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
    (initialClosed_swapAllowed swap) bounded
  refine ⟨⟨_, symmetry.mapTrace prior guardedPrior⟩, ?_, forcedPrior⟩
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf r
    (symmetry.mapTrace prior guardedPrior) = _
  rw [onePacket_infoOf]
  exact observe_swap_of_fixes swap (initialClosed_swapAllowed swap) bounded fixes prior
    guardedPrior

end Native

end Vegas
