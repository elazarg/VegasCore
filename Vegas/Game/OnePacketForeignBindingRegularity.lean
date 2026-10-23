/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCounterpartImage
import Vegas.Game.OnePacketOwnerPriorSite
import Vegas.Game.OnePacketSplicePoint
import Vegas.Game.AsyncDeviationForeign

/-! # Regular counterparts from successful foreign binding fields

Typed decoding preserves the absence of failures at foreign binding fields.
At source points with the same focal view, own commitment cells agree; if the
other point is intended, successful foreign cells suffice for the value swap.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  [DecidableEq (CellTy Player L)]

/-- A source commitment read from a store with successful foreign binding
fields is successful whenever its owner differs from the focal player. -/
theorem decodeSourcePrefix?_commitment_not_failure (who : Player)
    {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L}
    (store : EventGraph.Store layout)
    (successful : ∀ owner payload (ref : EventGraph.FieldRef layout (.binding owner payload))
      value, owner ≠ who → ref.get? store = some value → value ≠ .failure) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (history : History Player L) (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
        some point →
      ∀ name owner payload value,
        ProtocolState.cell? program point name (.commitment owner payload) = some value →
        owner ≠ who → value ≠ .failure
  | 0, _, _, program, refs, registry, revelations, outputs, history, point, decoded,
      name, owner, payload, value, found, foreign => by
      rw [decodeSourcePrefix?] at decoded
      obtain ⟨cells, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      rw [ProtocolState.cell?_entry] at found
      obtain ⟨source, same⟩ := State.exists_hasVar_of_cell?_eq_some found
      have agrees := decodeState?_agrees refs store cells read source
      exact successful owner payload (refs.get source) value foreign
        (by simpa only [same, cellValue] using agrees)
  | count + 1, _, _, program, refs, registry, revelations, outputs, history, point, decoded,
      name, owner, payload, value, found, foreign => by
      cases program with
      | ret _ => cases decoded
      | sample _ _ _ next =>
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_commitment_not_failure who store successful count next
            _ _ _ _ history rest read name owner payload value found foreign
      | commit _ _ _ _ next =>
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_commitment_not_failure who store successful count next
            _ _ _ _ history rest read name owner payload value found foreign
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_commitment_not_failure who store successful count next
            _ _ _ _ history rest read name owner payload value found foreign

variable {setup : Setup (Player := Player) (L := L)}

/-- Successful foreign binding reads in a native configuration give successful
foreign commitment cells at its decoded source point. -/
theorem decodedPoint_commitment_not_failure (who : Player)
    {config : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point)
    (successful : ∀ owner payload
      (ref : EventGraph.FieldRef (graph setup).layout (.binding owner payload)) value,
      owner ≠ who → ref.get? config.store = some value → value ≠ .failure)
    {name owner payload value}
    (found : ProtocolState.cell? setup.program point name (.commitment owner payload) =
      some value) (foreign : owner ≠ who) : value ≠ .failure := by
  unfold decodedPoint at decoded
  split at decoded
  · rename_i ordered
    exact decodeSourcePrefix?_commitment_not_failure who config.store successful ordered.choose
      setup.program _ _ _ _ _ point decoded name owner payload value found foreign
  · cases decoded

/-- Equal focal views and successful foreign binding fields make the differing
commitment cells compatible with an intended witness. -/
theorem commitmentCellsSucceed_of_foreign_bindings {who : Player}
    {config : (graph setup).Config} {point witness : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point)
    (sameView : ProtocolState.observe who setup.program point =
      ProtocolState.observe who setup.program witness)
    (intended : ProtocolState.Intended setup.program witness)
    (successful : ∀ owner payload
      (ref : EventGraph.FieldRef (graph setup).layout (.binding owner payload)) value,
      owner ≠ who → ref.get? config.store = some value → value ≠ .failure) :
    CommitmentCellsSucceed setup point witness := by
  intro name owner payload left right first second different
  obtain ⟨value, rfl⟩ := ProtocolState.cell?_commitment_success intended second
  refine ⟨?_, by simp⟩
  by_cases mine : owner = who
  · subst owner
    have equal := visibleCellsAgree_of_observe sameView name
      (show (cellField (.commitment who payload)).VisibleTo who from rfl)
    rw [first, second] at equal
    exact (different (Option.some.inj equal)).elim
  · exact decodedPoint_commitment_not_failure who decoded successful first mine



/-- Successful foreign binding fields suffice for the value swap toward a
splice retaining the responder's own cells, even when those own cells fail. -/
theorem commitmentCellsSucceed_splicePoint_of_foreign_bindings {responder : Player}
    {config : (graph setup).Config} {point witness : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point)
    (intended : ProtocolState.Intended setup.program witness)
    (successful : ∀ owner payload
      (ref : EventGraph.FieldRef (graph setup).layout (.binding owner payload)) value,
      owner ≠ responder → ref.get? config.store = some value → value ≠ .failure) :
    CommitmentCellsSucceed setup point
      (ProtocolState.splicePoint setup.program responder point witness) := by
  intro name owner payload left right first second different
  by_cases mine : owner = responder
  · subst owner
    rw [ProtocolState.cell?_splicePoint_of_hidden rfl, first] at second
    exact (different (Option.some.inj second)).elim
  · cases witnessFound : ProtocolState.cell? setup.program witness name
        (.commitment owner payload) with
    | none =>
        rw [ProtocolState.cell?_splicePoint_of_none witnessFound, first] at second
        exact (different (Option.some.inj second)).elim
    | some other =>
        have hidden : (CellTy.commitment owner payload : CellTy Player L).hiddenOwner? ≠
            some responder := by
          intro equal
          exact mine (Option.some.inj equal)
        rw [ProtocolState.cell?_splicePoint_of_found hidden first witnessFound] at second
        refine ⟨decodedPoint_commitment_not_failure responder decoded successful first mine, ?_⟩
        obtain ⟨value, success⟩ := ProtocolState.cell?_commitment_success intended witnessFound
        rw [← Option.some.inj second, success]
        simp

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [DecidableEq (CellTy Player L)] in
/-- Once every completed foreign binding succeeds, all present foreign binding
reads succeed. Initial binding inputs succeed by well-formedness. -/
theorem foreignBinding_reads_not_failure (wellFormed : setup.WellFormed)
    {who : Player} {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (successful : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ≠ who →
      event ∈ control.execution.application.config.cut.completed →
      ¬ StoreEventFailed control.execution.application.config.store event) :
    ∀ owner payload (ref : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
      value, owner ≠ who →
      ref.get? control.execution.application.config.store = some value → value ≠ .failure := by
  intro owner payload ref value foreign stored failed
  subst value
  rcases ref with ⟨field, layoutEq⟩
  cases field with
  | inl input =>
      obtain ⟨initial, member, inputsEq, -⟩ := initialSlots_of_trace trace control rfl
      have positions : ∀ (Γ : SourceCtx Player L) (position : Fin Γ.length),
          ∃ (name : VarId) (kind : CellTy Player L) (source : HasVar Γ name kind),
            inputId source = position := by
        intro Γ
        induction Γ with
        | nil => exact fun position => Fin.elim0 position
        | cons head Γ ih =>
            intro position
            cases position using Fin.cases with
            | zero => exact ⟨head.1, head.2, .here, rfl⟩
            | succ position =>
                obtain ⟨name, kind, source, rfl⟩ := ih position
                exact ⟨name, kind, .there source, rfl⟩
      obtain ⟨name, kind, source, rfl⟩ := positions setup.context input
      have kindEq : cellField kind = .binding owner payload :=
        (inputLayout_inputId source).symm.trans layoutEq
      have hidden : kind.hiddenOwner? = some owner := by
        cases kind <;> cases kindEq
        rfl
      have notFailed := eventInputs_not_failure wellFormed member source hidden
      have failedField : ((graph setup).layout (.inl (inputId source))).IsFailure
          (setup.eventInputs initial (inputId source)) := by
        have transport : ∀ (kind : EventGraph.EventField Player L)
            (same : kind = .binding owner payload) (entry : kind.Value),
            cast (congrArg (fun kind => Option kind.Value) same) (some entry) =
              some PublicationResult.failure → kind.IsFailure entry := by
          rintro _ rfl entry equal
          exact Option.some.inj equal
        apply transport _ layoutEq
        change cast _ (some (control.execution.application.config.inputs (inputId source))) =
          some PublicationResult.failure at stored
        simpa only [inputsEq] using stored
      exact notFailed failedField
  | inr event =>
      have failure : StoreEventFailed control.execution.application.config.store event :=
        storeEventFailed_of_ref _ event ⟨.inr event, layoutEq⟩ rfl stored rfl
      obtain ⟨storedValue, storedValueEq, isFailed⟩ := failure
      have available : (control.execution.application.config.outputs event).isSome = true := by
        change (control.execution.application.config.store (.inr event)).isSome = true
        rw [storedValueEq]
        rfl
      exact successful event owner payload layoutEq foreign
        ((control.execution.application.config.output_available event).mp available)
        ⟨storedValue, storedValueEq, isFailed⟩


omit [DecidableEq (CellTy Player L)] in
/-- Repairing all completed foreign bindings suffices for a regular counterpart
with the repaired trace's operational record and full focal information. -/
theorem counterpart_of_successful_foreign_bindings (wellFormed : setup.WellFormed)
    {assessment : setup.intendedModel.BehavioralAssessment} (mixed : assessment.IsFullyMixed)
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (history witness : (onePacketInformation setup leaks bounds horizon
      scheduler).InformationHistory who (some (past, view)))
    {current witnessControl : (application setup leaks).Control}
    (historyState : history.1.state = some current)
    (witnessState : witness.1.state = some witnessControl)
    {point target : ProtocolState setup.program}
    (decoded : decodedPoint setup current.execution.application.config = some point)
    (witnessDecoded : decodedPoint setup witnessControl.execution.application.config = some target)
    (free : ∀ player, ¬ ProtocolState.OwesFailure player setup.program target)
    (successful : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ≠ who →
      event ∈ current.execution.application.config.cut.completed →
      ¬ StoreEventFailed current.execution.application.config.store event)
    (covered : BindingFieldsCovered bounds) :
    ∃ counterpart : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who (some (past, view)),
      RegularTrace setup leaks bounds horizon scheduler assessment who counterpart.1.trace ∧
      operationalRecord setup leaks bounds horizon scheduler counterpart.1.trace =
        operationalRecord setup leaks bounds horizon scheduler history.1.trace := by
  classical
  have succeed : CommitmentCellsSucceed setup point target := by
    have observed (native : (onePacketProtocol setup leaks bounds horizon scheduler).History)
        (seen : (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
          native.trace = some (past, view))
        (control : (application setup leaks).Control) (current : native.state = some control) :
        control.execution.observe (application setup leaks) who = view := by
      obtain ⟨state, nativeTrace⟩ := native
      change state = some control at current
      subst current
      rw [onePacket_infoOf] at seen
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        exact (Prod.mk.inj (Option.some.inj seen)).2
      · simp [ReactiveApplication.observe, active] at seen
    have currentView := observed history.1 history.2 current historyState
    have witnessView := observed witness.1 witness.2 witnessControl witnessState
    obtain ⟨⟨state, trace⟩, info⟩ := history
    change state = some current at historyState
    subst historyState
    obtain ⟨⟨state, witnessTrace⟩, witnessInfo⟩ := witness
    change state = some witnessControl at witnessState
    subst witnessState
    have sameSource := (sourceViewOf_eq_decodedPoint who trace).symm.trans
      ((congrArg (sourceViewOf setup leaks who) (currentView.trans witnessView.symm)).trans
        (sourceViewOf_eq_decodedPoint who witnessTrace))
    rw [decoded, witnessDecoded] at sameSource
    have sameView := Option.some.inj sameSource
    have freeWitness : ∀ point, decodedPoint setup witnessControl.execution.application.config =
        some point → ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
      intro point read player
      rw [witnessDecoded, Option.some.injEq] at read
      subst read
      exact free player
    obtain ⟨second, secondReplay⟩ := intendedHistory?_isSome_of_debtFree wellFormed witnessTrace
      witnessControl rfl freeWitness
    have secondState : second.state = some target :=
      (intendedHistory?_state witnessTrace secondReplay).trans witnessDecoded
    exact commitmentCellsSucceed_of_foreign_bindings decoded sameView
      (intended_of_history wellFormed second.trace target secondState)
      (foreignBinding_reads_not_failure wellFormed trace successful)
  exact counterpart_of_witness wellFormed mixed turn history witness historyState witnessState
    decoded witnessDecoded free succeed covered

end Vegas
