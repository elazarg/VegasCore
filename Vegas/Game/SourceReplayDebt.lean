module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceDecodedDebt
public import Vegas.Game.SourceDebtObservation

@[expose] public section

/-! # Owed failures along source replay continuations

An existing source residual transports debt through arbitrary supported graph
continuations. At completion this produces an owned failed reveal. A matching
initialized source trace also supplies public-default provenance, yielding the
fixed-exit branch. Debt can be transferred from another source point through
its own observation without identifying hidden foreign values.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem point_eq_of_terminal_readout :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    (final : Config Player L program.terminalCtx) →
    ProtocolState.readout program left = some final →
    ProtocolState.readout program right = some final → left = right
  | _, _, .ret _, _, _, _, leftRead, rightRead =>
      Option.some.inj (leftRead.trans rightRead.symm)
  | _, _, .sample _ _ _ next, left, right, final, leftRead, rightRead
  | _, _, .commit _ _ _ _ next, left, right, final, leftRead, rightRead
  | _, _, .reveal _ _ _ _ _ _ next, left, right, final, leftRead, rightRead => by
      cases left with
      | inl _ => cases leftRead
      | inr left =>
          cases right with
          | inl _ => cases rightRead
          | inr right =>
              exact congrArg Sum.inr (point_eq_of_terminal_readout next left right final
                leftRead rightRead)

private theorem SourceResidual.terminal_owed_of_replay_prefix
    {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {before final : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank before)
    (path : Relation.ReflTransGen EventGraph.Config.Step before final)
    (terminal : final.cut.Terminal) (who : Player) (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (owed : ProtocolState.OwesFailure who setup.program point) :
    ∃ finalPoint : ProtocolState setup.program,
      ProtocolState.OwesFailure who setup.program finalPoint ∧
      ProtocolState.readout setup.program finalPoint =
        some (terminalConfig setup.program ⟨final, terminal⟩) := by
  have holds : DecodedHolds (ProtocolState.OwesFailure who setup.program) rank before := by
    intro state read
    rw [decoded, Option.some.injEq] at read
    exact read ▸ owed
  obtain ⟨lastRank, ⟨lastResidual⟩, remains⟩ :=
    residual.decodedHolds_path (owesFailure_stepClosed who) holds path
  have full : final.cut.IsPrefix (eventCount setup.program) := by
    refine ⟨le_rfl, fun event => ?_⟩
    rw [terminal]
    exact iff_of_true (Finset.mem_univ _) event.isLt
  have atEnd := lastResidual.checkpoint.ordered.unique full
  subst lastRank
  let finalPoint := lastResidual.lift (ProtocolState.entry lastResidual.program lastResidual.source)
  have finalOwed : ProtocolState.OwesFailure who setup.program finalPoint :=
    remains _ lastResidual.decode
  have read := sourceServicePrefix?_terminal_readout setup final
  rw [lastResidual.decode, decodeConfig?_terminal setup.program ⟨final, terminal⟩] at read
  exact ⟨finalPoint, finalOwed, read⟩

/-- Debt is the same at a replay prefix and any source point with matching own view
and static metadata. The replay prefix's static metadata comes from its decoder. -/
theorem owesFailure_of_sourcePrefix_observe_eq
    {setup : Setup (Player := Player) (L := L)}
    {rank : Nat}
    {before : setup.informationGraph.Config}
    (who : Player) (point other : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (otherStatic : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context)
      other)
    (same : ProtocolState.observe who setup.program other =
      ProtocolState.observe who setup.program point)
    (owed : ProtocolState.OwesFailure who setup.program other) :
    ProtocolState.OwesFailure who setup.program point := by
  have pointStatic := decodeSourcePrefix?_staticAt rank setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) before.store
    (decodeHistory setup.program before.history) before.defaults point decoded
  exact (ProtocolState.owesFailure_iff_of_observe_eq who setup.program []
    (Revelations.initial setup.context) other point otherStatic pointStatic same).mp owed

/-- Debt at a genuine source replay prefix forces a failed reveal at completion. -/
theorem SourceResidual.failedReveals_of_owesFailure_path
    {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {before final : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank before)
    (path : Relation.ReflTransGen EventGraph.Config.Step before final)
    (terminal : final.cut.Terminal) (who : Player) (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (owed : ProtocolState.OwesFailure who setup.program point) :
    1 ≤ failedReveals setup.program who
      (publicOutcome setup.program (terminalConfig setup.program ⟨final, terminal⟩)) := by
  obtain ⟨finalPoint, finalOwed, read⟩ :=
    residual.terminal_owed_of_replay_prefix path terminal who point decoded owed
  exact ProtocolState.failedReveals_pos_of_owesFailure who setup.program finalPoint finalOwed read

/-- A matching terminal source trace turns source debt into an actual public default. -/
theorem SourceResidual.defaulted_of_owesFailure_path
    {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {before final : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank before)
    (path : Relation.ReflTransGen EventGraph.Config.Step before final)
    (terminal : final.cut.Terminal) (who : Player) (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank before = some point)
    (owed : ProtocolState.OwesFailure who setup.program point)
    (initial : State L setup.context)
    (history : (executionProtocol setup.program (CommitmentInterface.forfeiture setup.program)
      (Config.initial initial)).History)
    (historyRead : ProtocolState.readout setup.program history.state =
      some (terminalConfig setup.program ⟨final, terminal⟩)) :
    who ∈ final.defaulted := by
  obtain ⟨finalPoint, finalOwed, read⟩ :=
    residual.terminal_owed_of_replay_prefix path terminal who point decoded owed
  have same := point_eq_of_terminal_readout setup.program finalPoint history.state
    (terminalConfig setup.program ⟨final, terminal⟩) read historyRead
  rw [same] at finalOwed
  exact ProtocolState.defaulted_of_owesFailure_trace setup.program
    (CommitmentInterface.forfeiture setup.program) (Config.initial initial) history.trace who
    finalOwed historyRead

end Vegas
