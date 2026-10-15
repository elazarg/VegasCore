/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceView
import Vegas.Game.PhaseSourceObservation

/-! # Whole source views decoded from actual partial concurrent cuts

Only the source-visible cells at the selected event are decoded. Hidden
foreign pending values and physical scheduling recall are not substituted by
source history data.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)

/-- At every owned ready nonpublication event, the whole syntactic source view
is available even when the concurrent cut has holes at hidden foreign events. -/
theorem exists_decodeEventView_of_ready :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
      (_before : ContextRefsBefore refs embedding) (event : Fin (eventCount program))
      (config : (serviceGraph setup mode).Config) (who : Player),
      config.cut.Ready (embedding.event event) →
      (serviceGraph setup mode).actor? (embedding.event event) = some who →
      ¬ ((serviceGraph setup mode).outputLayout (embedding.event event)).IsPublication →
      ∀ past : List (OwnAction Player L),
        ∃ view, decodeEventView? program refs embedding.ref who event
          ((serviceGraph setup mode).playerStore who config.store) past = some view := by
  intro Γ O program
  induction program with
  | ret => intro refs embedding before event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs embedding before event config who ready acting notPublication past
      refine Fin.cases ?_ ?_ event ready acting notPublication
      · intro ready acting notPublication
        obtain ⟨observation, decoded⟩ := exists_decodeObservation_of_ready setup mode
          (.sample name fresh law next) refs embedding before ⟨0, by simp [eventCount]⟩ config who
            ready acting notPublication
        exact ⟨.inl (observation, past), by
          simp only [decodeEventView?, Fin.cases_zero, decoded, Option.map_some]⟩
      · intro tail ready acting notPublication
        let head : Fin (eventCount (.sample name fresh law next)) := ⟨0, by simp [eventCount]⟩
        let nextEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
        let nextRefs := refs.cons (name := name) (cell := .publicData _) (embedding.ref head)
        have nextBefore : ContextRefsBefore nextRefs nextEmbedding := by
          intro readName readCell selected later
          cases selected with
          | here =>
              change (embedding.event head).val < (embedding.event (Fin.succ later)).val
              exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
          | there selected => exact before selected (Fin.succ later)
        obtain ⟨view, decoded⟩ := ih nextRefs nextEmbedding nextBefore tail config who
          ready acting notPublication past
        have nextOutputs : nextEmbedding.ref = fun later => embedding.ref (Fin.succ later) := by
          funext later
          rfl
        rw [nextOutputs] at decoded
        exact ⟨.inr view, by
          simpa only [decodeEventView?, Fin.cases_succ, Option.map_some, nextRefs, head] using
            congrArg (Option.map Sum.inr) decoded⟩
  | commit name owner fresh guard next ih =>
      intro refs embedding before event config who ready acting notPublication past
      refine Fin.cases ?_ ?_ event ready acting notPublication
      · intro ready acting notPublication
        obtain ⟨observation, decoded⟩ := exists_decodeObservation_of_ready setup mode
          (.commit name owner fresh guard next) refs embedding before
            ⟨0, by simp [eventCount]⟩ config who
            ready acting notPublication
        exact ⟨.inl (observation, past), by
          simp only [decodeEventView?, Fin.cases_zero, decoded, Option.map_some]⟩
      · intro tail ready acting notPublication
        let head : Fin (eventCount (.commit name owner fresh guard next)) :=
          ⟨0, by simp [eventCount]⟩
        let nextEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
        let nextRefs := refs.cons (name := name) (cell := .commitment owner _)
          (embedding.ref head)
        have nextBefore : ContextRefsBefore nextRefs nextEmbedding := by
          intro readName readCell selected later
          cases selected with
          | here =>
              change (embedding.event head).val < (embedding.event (Fin.succ later)).val
              exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
          | there selected => exact before selected (Fin.succ later)
        obtain ⟨view, decoded⟩ := ih nextRefs nextEmbedding nextBefore tail config who
          ready acting notPublication past
        have nextOutputs : nextEmbedding.ref = fun later => embedding.ref (Fin.succ later) := by
          funext later
          rfl
        rw [nextOutputs] at decoded
        exact ⟨.inr view, by
          simpa only [decodeEventView?, Fin.cases_succ, Option.map_some, nextRefs, head] using
            congrArg (Option.map Sum.inr) decoded⟩
  | reveal published owner name fresh source unresolved next ih =>
      intro refs embedding before event config who ready acting notPublication past
      refine Fin.cases ?_ ?_ event ready acting notPublication
      · intro ready acting notPublication
        obtain ⟨observation, decoded⟩ := exists_decodeObservation_of_ready setup mode
          (.reveal published owner name fresh source unresolved next) refs embedding before
            ⟨0, by simp [eventCount]⟩ config who
            ready acting notPublication
        exact ⟨.inl (observation, past), by
          simp only [decodeEventView?, Fin.cases_zero, decoded, Option.map_some]⟩
      · intro tail ready acting notPublication
        let head : Fin (eventCount
            (.reveal published owner name fresh source unresolved next)) :=
          ⟨0, by simp [eventCount]⟩
        let nextEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
        let nextRefs := refs.cons (name := published) (cell := .publication _)
          (embedding.ref head)
        have nextBefore : ContextRefsBefore nextRefs nextEmbedding := by
          intro readName readCell selected later
          cases selected with
          | here =>
              change (embedding.event head).val < (embedding.event (Fin.succ later)).val
              exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
          | there selected => exact before selected (Fin.succ later)
        obtain ⟨view, decoded⟩ := ih nextRefs nextEmbedding nextBefore tail config who
          ready acting notPublication past
        have nextOutputs : nextEmbedding.ref = fun later => embedding.ref (Fin.succ later) := by
          funext later
          rfl
        rw [nextOutputs] at decoded
        exact ⟨.inr view, by
          simpa only [decodeEventView?, Fin.cases_succ, Option.map_some, nextRefs, head] using
            congrArg (Option.map Sum.inr) decoded⟩

variable (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- Actual physical private input determines the original source protocol view
at its selected compiled event. This is not a source-history projection. -/
def phaseSourceView? (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (phaseApplication runtime leaks).PlayerView) : setup.ProtocolView who :=
  if same : view.application.1.who = who then
    let observed : (serviceGraph setup mode).PlayerObservation who := same ▸
      view.application.1.observation
    decodeEventView? setup.program (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputRef setup.program) who event observed.store
      (decodeCompletions setup.program
        (observed.ownActions.map (setup.eventGraph.fromModeCompletion mode)))
  else none

/-- Every actual ready owned nonpublication callback has a decoded whole source
view; no completed total prefix or intended source witness is required. -/
theorem phaseSourceView?_succeeds (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (ready : execution.application.current.native.config.cut.Ready event)
    (acting : (serviceGraph setup mode).actor? event = some who)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication) :
    ∃ view, phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view := by
  unfold phaseSourceView?
  rw [dite_eq_left (show
    (execution.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl)]
  exact exists_decodeEventView_of_ready setup mode setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) event execution.application.current.native.config who
      ready acting notPublication _

/-- A successfully decoded actual source view names the same owner as its
actual compiled event. -/
theorem phaseSourceView?_actor (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view) :
    SourceProgram.ProtocolView.actor who setup.program view =
      (serviceGraph setup mode).actor? event := by
  unfold phaseSourceView? at decoded
  rw [dite_eq_left (show
    (execution.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl)]
    at decoded
  exact (decodeEventView?_actor setup.program _ _ who event _ _ view decoded).trans
    (eventOwner?_eq_actor setup.program event)

/-- Every legal source action at the actual decoded input has a correctly
addressed action at this compiled event. -/
theorem phaseSourceView?_available (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view)
    (action : OwnAction Player L)
    (available : action ∈ SourceProgram.ProtocolView.available who setup.program
      (CommitmentInterface.forfeiture setup.program) view) :
    ∃ choice, decodeEventAction setup.program event choice = some action := by
  unfold phaseSourceView? at decoded
  rw [dite_eq_left (show
    (execution.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl)]
    at decoded
  exact decodeEventView?_available setup.program _ _ who event _ _ view decoded action available

/-- Actual binding callbacks decode to a source commitment control point. -/
theorem phaseSourceView?_atCommit (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload) :
    SourceProgram.ProtocolView.atCommit who setup.program view = true := by
  unfold phaseSourceView? at decoded
  rw [dite_eq_left (show
    (execution.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl)]
    at decoded
  exact decodeEventView?_atCommit setup.program _ _ who event _ _ view decoded owner payload binding

end Vegas
