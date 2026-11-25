module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.ConditionedInitialFiber
public import Vegas.Source.Exclusion
public import Vegas.Game.RevealService
public import Vegas.Pending.ReactiveStateInvariant

@[expose] public section

/-! # A common signal determined by the original private observations -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {Signal : Type*} {signal : State L setup.context → Signal}

/-- Every player knows the same signal from its own original observation on supported draws. -/
def SharesInitialSignal (setup : Setup (Player := Player) (L := L))
    (signal : State L setup.context → Signal) : Prop :=
  ∀ who (first second : State L setup.context),
    first ∈ setup.initialDistribution.support → second ∈ setup.initialDistribution.support →
    sourceObserve who first = sourceObserve who second → signal first = signal second

private theorem intendedInfo_eq {state : setup.ProtocolState}
    (trace : setup.intendedProtocol.Trace state) (who : Player) :
    setup.intendedModel.infoOf who trace = setup.protocolObserve who state := by
  simp only [intendedModel, InformationModel.restrictMenu_infoOf]
  exact setup.protocol_info (CommitmentInterface.values setup.program) who
    (ExecutionProtocol.restrictAvailable.trace trace)

/-- Each actual decision fiber lies entirely in its observed component even off path. -/
theorem SharesInitialSignal.sourceFiber (common : setup.SharesInitialSignal signal)
    (value : Signal) (supported : value ∈ (setup.initialDistribution.map signal).support)
    (who : Player) (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (history : setup.intendedModel.InformationHistory who site.1) :
    setup.initialComponent signal value history.1.state := by
  obtain ⟨anchor, _⟩ := site.2
  cases atAnchor : anchor.1.state with
  | none =>
    have active := InformationModel.InformationSite.active
      (M := (setup.conditionInitial signal value).intendedModel) site anchor
    rw [atAnchor] at active
    exact active.elim
  | some first =>
    cases atHistory : history.1.state with
    | none => trivial
    | some second =>
      let original := setup.conditionInitial_informationHistory signal value supported who site.1
        anchor
      have same := (intendedInfo_eq original.1.trace who).symm.trans
        (original.2.trans history.2.symm) |>.trans (intendedInfo_eq history.1.trace who)
      change setup.protocolObserve who anchor.1.state = _ at same
      rw [atAnchor, atHistory] at same
      have equality := ProtocolState.sourceObserve_base_eq_of_observe_eq who setup.program first
        second (Option.some.inj same)
      have present := (setup.conditionInitial signal value).intended_trace_initialSupport
        anchor.1.trace first atAnchor
      obtain ⟨keyEq, initial⟩ := GameTheory.Math.Probability.mem_support_fiberPosterior
        supported present
      exact (common who _ _ initial (setup.intended_trace_initialSupport history.1.trace second
        atHistory) equality).symm.trans keyEq

variable {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}

local notation "app" => application setup timeouts leaks

/-- The view's masked store agrees with the visible input cells of a possible source draw. -/
def VisibleInitialInputs (who : Player) (view : (app).PlayerView) (draw : State L setup.context) :
    Prop :=
  ∀ input, setup.informationGraph.fieldVisibleTo who (.inl input) →
    view.application.observation.store (.inl input) = some (setup.eventInputs draw input)

private theorem observe_eq_of_visibleInitialInputs (who : Player) (view : (app).PlayerView)
    {first second : State L setup.context}
    (left : VisibleInitialInputs who view first) (right : VisibleInitialInputs who view second) :
    sourceObserve who first = sourceObserve who second := by
  have cell {name : VarId} {kind : CellTy Player L} (ref : HasVar setup.context name kind)
      (visible : (cellField kind).VisibleTo who) : first.get ref = second.get ref := by
    have field : setup.informationGraph.fieldVisibleTo who (.inl (inputId ref)) := by
      change (inputLayout setup.context (inputId ref)).VisibleTo who
      rwa [inputLayout_inputId ref]
    have both := Option.some.inj ((left _ field).symm.trans (right _ field))
    have get := (encodeInputs_get first ref).symm.trans ((congrArg
      (cast (congrArg EventGraph.EventField.Value (inputLayout_inputId ref))) both).trans
        (encodeInputs_get second ref))
    cases kind <;> exact get
  exact sourceObserve_congr who first second (fun ref => cell ref trivial)
    (fun ref => cell ref trivial) (fun ref => cell ref rfl) (fun ref => cell ref rfl)

private theorem reachable_inputs {inputs : setup.informationGraph.Inputs}
    {config : setup.informationGraph.Config} (reached : config.Reachable inputs) :
    config.inputs = inputs := by
  induction reached with
  | initial => rfl
  | step _ event ready action next supported ih =>
    exact (EventGraph.Config.Step.inputs_eq ⟨event, ready, action, supported⟩).trans ih

/-- Read a shared signal from an ordinary local ledger view. Unsupported views can use
any value of the signal; their choice does not affect a legal execution. -/
def nativeInitialSignal (signal : State L setup.context → Signal) (who : Player)
    (view : (app).PlayerView) : Signal := by
  classical
  exact if h : ∃ draw ∈ setup.initialDistribution.support, VisibleInitialInputs who view draw then
    signal h.choose else signal setup.initialDistribution.support_nonempty.choose

/-- Every valid raw execution reveals the correct common signal to its owner at any turn.
The construction requires no ledger publication or extension of the observation rule. -/
theorem SharesInitialSignal.native (common : setup.SharesInitialSignal signal)
    (draw : State L setup.context) (present : draw ∈ setup.initialDistribution.support)
    (execution : (app).Execution)
    (valid : EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
      (setup.eventInputs draw) execution.application) (who : Player) :
    nativeInitialSignal signal who (execution.observe app who) = signal draw := by
  classical
  have readsDraw : VisibleInitialInputs who (execution.observe app who) draw := by
    intro input visible
    change setup.informationGraph.playerStore who execution.application.config.store
      (.inl input) = _
    rw [EventGraph.playerStore_of_visible _ _ _ _ visible, EventGraph.Config.store_input,
      reachable_inputs valid.reachable]
  have existsDraw : ∃ other ∈ setup.initialDistribution.support,
      VisibleInitialInputs who (execution.observe app who) other := ⟨draw, present, readsDraw⟩
  unfold nativeInitialSignal
  rw [dite_eq_left existsDraw]
  exact common who _ _ existsDraw.choose_spec.1 present
    (observe_eq_of_visibleInitialInputs who _ existsDraw.choose_spec.2 readsDraw)

end Vegas.SourceProgram.Setup
