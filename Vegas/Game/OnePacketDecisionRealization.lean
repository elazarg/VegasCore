module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketAssessmentFidelity
public import Vegas.Game.OnePacketBoundaryWaiting
public import Vegas.Game.OnePacketDecodedActor

@[expose] public section

/-! # Genuine first source decisions at clean native boundaries -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler

/-- A reached source boundary at an intended decision admits a genuine first
native activation at that same source point, with no fallback replay premise. -/
theorem exists_sourceDecisionRealization_of_boundary
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (rank : Nat) (start : (E).History)
    (anchor : (application setup timeouts leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {who : Player} (source : setup.intendedModel.InformationSite who)
    (sourceHistory : setup.intendedModel.InformationHistory who source.1)
    (sourceState : sourceHistory.1.state = some point) :
    ∃ site : (N).InformationSite who,
      SourceDecisionRealization setup timeouts leaks bounds horizon scheduler source site ∧
      ∃ history : (N).InformationHistory who site.1,
        nativeDecodedState setup timeouts leaks history.1.state = some point := by
  classical
  obtain ⟨_, _, action, offered⟩ := source.2
  have localOffered : some action ∈ setup.intendedModel.menu who
      (setup.intendedModel.infoOf who sourceHistory.1.trace) := by
    rw [sourceHistory.2]
    exact offered
  have sourceActive :=
    ((setup.intendedModel.menu_adequate who sourceHistory.1.trace _).mp localOffered).1
  rw [sourceState] at sourceActive
  change ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
    some who at sourceActive
  have notTerminal := ProtocolState.not_terminal_of_actor who who setup.program point sourceActive
  have inside : rank < (graph setup).order.eventCount := by
    by_contra outside
    have atEnd : rank = (graph setup).order.eventCount :=
      Nat.le_antisymm boundary.ordered.1 (Nat.le_of_not_gt outside)
    subst rank
    obtain ⟨found, read, terminal⟩ := serviceSourcePrefix?_terminal setup .sequential
      anchor.application.config boundary.ordered.terminal
    have samePoint : found = point := Option.some.inj (read.symm.trans decoded)
    exact notTerminal (samePoint ▸ terminal)
  let event : (graph setup).EventId := ⟨rank, inside⟩
  have ready := (ready_iff_rank setup _ rank boundary.ordered event).mpr rfl
  have actual : decodedPoint setup anchor.application.config = some point :=
    (decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
    scheduler (state ▸ start.trace)
  have owned : (graph setup).actor? event = some who :=
    (decodedPoint_actor_of_history who rawTrace ready actual).symm.trans sourceActive
  have clear := defaulted_eq_empty_of_decodedIntended actual intended
  let waiting := (N).runBehavioralUntil certificate players
    (fun history => (application setup timeouts leaks).actor history.state = some who) start
  obtain ⟨callback, supported⟩ := waiting.support_nonempty
  obtain ⟨remaining, execution, current, same, _callbackClear, _recalled, pending, never⟩ :=
    counted_boundary_firstActivation (timeouts := timeouts) opportunity timely completes certificate
      players start state boundary clear decoded intended who event rfl owned callback supported
  let info : (N).InfoState who := some (execution.logs who,
    execution.observe (application setup timeouts leaks) who)
  have observed : (N).infoOf who callback.trace = info := by
    have nativeInfo : (N).infoOf who callback.trace =
        (application setup timeouts leaks).observe who callback.state :=
      (bounds.onePacketMenu timeouts leaks).info (initialLaw setup) horizon scheduler who
        callback.trace
    rw [nativeInfo, current]
    simp only [ReactiveApplication.observe, ↓reduceIte, info]
  have callbackRunning : ¬ (E).terminal callback.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  let site : (N).InformationSite who := ⟨info, ⟨⟨callback, observed⟩, callbackRunning,
    ⟨none⟩, ⟨⟨none⟩, bounds.silence_onePacket timeouts leaks who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who), rfl⟩⟩⟩
  have nextOrdered : execution.application.config.cut.IsPrefix rank := same ▸ boundary.ordered
  have nextDecoded : sourceServicePrefix? setup rank execution.application.config = some point :=
    same ▸ decoded
  have nextActual : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix nextOrdered).trans nextDecoded
  have nativeDecoded : nativeDecodedState setup timeouts leaks callback.state = some point := by
    rw [current]
    exact nextActual
  refine ⟨site, ⟨?_, ?_, ?_⟩, ⟨callback, observed⟩, nativeDecoded⟩
  · have sourceInfo : source.1 = setup.protocolObserve who (some point) := by
      rw [← sourceHistory.2, setup.intended_info, sourceState]
    exact sourceInfo.trans
      (projectView_observe setup timeouts leaks who execution rank nextOrdered point nextDecoded
        (execution.logs who)).symm
  · refine ⟨callback, observed, ?_⟩
    rw [current]
    exact ⟨rank, point, nextOrdered, nextDecoded, forcedPoint_of_intended who intended⟩
  · exact ⟨execution.logs who, execution.observe (application setup timeouts leaks) who,
      event, rfl, pending, never⟩

end Vegas
