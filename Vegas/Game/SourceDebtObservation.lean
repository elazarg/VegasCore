/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketIntendedProjection
import Vegas.Source.DebtObservation

/-! # Own source debt over native information fibers

The prefix decoder retains static guard and publication data and the full
public default history. The native projected view therefore determines the
owner's source debt wherever the current source point decodes. Response menus
and their initial laws do not change that observation argument.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **The prefix decoder carries the program's static data.** A source point
decoded from a registry and a publication status carries, at its program point,
the registry and publication status the program carries there. -/
theorem decodeSourcePrefix?_staticAt {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
          some point →
        ProtocolState.StaticAt program registry revelations point
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨state, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ProtocolState.staticAt_entry program _ rfl rfl
  | _ + 1, _, _, .ret _, _, _, _, _, _, _, _, _, decoded => by
      simp only [decodeSourcePrefix?, reduceCtorEq] at decoded
  | count + 1, _, _, .sample _ _ _ next, refs, registry, revelations, outputs, store, history,
      defaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact decodeSourcePrefix?_staticAt count next _ _ _ _ store history defaults rest read
  | count + 1, _, _, .commit _ _ _ _ next, refs, registry, revelations, outputs, store, history,
      defaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact decodeSourcePrefix?_staticAt count next _ _ _ _ store history defaults rest read
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, refs, registry, revelations, outputs, store,
      history, defaults, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact decodeSourcePrefix?_staticAt count next _ _ _ _ store history defaults rest read

variable {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}

/-- A decoded point is the source prefix decoding at the configuration's
completed prefix. -/
theorem decodedPoint_isPrefix {config : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) :
    ∃ rank, config.cut.IsPrefix rank ∧ sourceServicePrefix? setup rank config = some point := by
  unfold decodedPoint at decoded
  split at decoded
  · rename_i ordered
    exact ⟨_, ordered.choose_spec, decoded⟩
  · cases decoded

/-- A decoded point carries the program's registry and publication status. -/
theorem decodedPoint_staticAt {config : (graph setup).Config}
    {point : ProtocolState setup.program} (decoded : decodedPoint setup config = some point) :
    ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) point := by
  obtain ⟨rank, _, read⟩ := decodedPoint_isPrefix decoded
  exact decodeSourcePrefix?_staticAt rank setup.program _ _ _ _ _ _ _ point read

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **Owing a failure is a function of the projected view.** Two native
executions whose decoded points `who` sees through the same projected view agree
on whether `who` owes a failure there. -/
theorem owesFailure_iff_of_projectView_eq (who : Player)
    {first second : (application setup runtime leaks).Execution}
    {firstPast secondPast : List (application setup runtime leaks).PlayerEntry}
    {firstPoint secondPoint : ProtocolState setup.program}
    (firstDecoded : decodedPoint setup first.application.config = some firstPoint)
    (secondDecoded : decodedPoint setup second.application.config = some secondPoint)
    (same : projectView setup runtime leaks who
        (some (firstPast, first.observe (application setup runtime leaks) who)) =
      projectView setup runtime leaks who
        (some (secondPast, second.observe (application setup runtime leaks) who))) :
    ProtocolState.OwesFailure who setup.program firstPoint ↔
      ProtocolState.OwesFailure who setup.program secondPoint := by
  obtain ⟨firstRank, firstOrdered, firstRead⟩ := decodedPoint_isPrefix firstDecoded
  obtain ⟨secondRank, secondOrdered, secondRead⟩ := decodedPoint_isPrefix secondDecoded
  rw [projectView_observe setup runtime leaks who first firstRank firstOrdered firstPoint firstRead
      firstPast,
    projectView_observe setup runtime leaks who second secondRank secondOrdered secondPoint
      secondRead secondPast]
    at same
  exact ProtocolState.owesFailure_iff_of_observe_eq who setup.program []
    (Revelations.initial setup.context) firstPoint secondPoint (decodedPoint_staticAt firstDecoded)
    (decodedPoint_staticAt secondDecoded) (Option.some.inj same)

variable {menu : (application setup runtime leaks).ResponseMenu}
  {initial : PMF (application setup runtime leaks).State} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- A concrete native decision input identifies its current control and displayed view. -/
theorem control_of_infoOf {who : Player}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (native : (menu.protocol initial horizon scheduler).History)
    (seen : (menu.information initial horizon scheduler).infoOf who
      native.trace =
      some (past, view)) :
    ∃ control : (application setup runtime leaks).Control, native.state = some control ∧
      control.execution.observe (application setup runtime leaks) who = view := by
  obtain ⟨state, trace⟩ := native
  have observed : (menu.information initial horizon scheduler).infoOf who trace =
      (application setup runtime leaks).observe who state :=
    menu.info initial horizon scheduler who trace
  rw [observed] at seen
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        exact ⟨control, rfl, (Prod.mk.inj (Option.some.inj seen)).2⟩
      · simp [ReactiveApplication.observe, active] at seen

/-- **All histories of a decision input agree on owing.** Any two histories of
an arbitrary native response menu at the same decision input of `who` agree on whether `who`
owes a failure at their decoded points. -/
theorem owesFailure_iff_of_infoOf {who : Player}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView}
    (first second : (menu.information initial horizon scheduler).InformationHistory
      who (some (past, view)))
    {firstPoint secondPoint : ProtocolState setup.program}
    (firstDecoded : nativeDecodedState setup runtime leaks first.1.state = some firstPoint)
    (secondDecoded : nativeDecodedState setup runtime leaks second.1.state = some secondPoint) :
    ProtocolState.OwesFailure who setup.program firstPoint ↔
      ProtocolState.OwesFailure who setup.program secondPoint := by
  obtain ⟨firstControl, firstState, firstView⟩ := control_of_infoOf (runtime := runtime) first.1
    first.2
  obtain ⟨secondControl, secondState, secondView⟩ := control_of_infoOf (runtime := runtime)
    second.1 second.2
  rw [firstState] at firstDecoded
  rw [secondState] at secondDecoded
  refine owesFailure_iff_of_projectView_eq (runtime := runtime) (firstPast := past) (secondPast :=
    past) who
    firstDecoded secondDecoded ?_
  rw [firstView, secondView]

end Vegas
