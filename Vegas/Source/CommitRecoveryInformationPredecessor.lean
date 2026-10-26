/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryInformation

/-! # Recovering the preceding source information from full attempt recall

The signal word records every source transition. Its preceding signal decides
whether that transition also added an own-play entry. Popping precisely these
records recovers the preceding full information, including at retries, public
chance and transitions that permanently exclude an owner.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

open Classical in
/-- The preceding full source information, when the signal word has a preceding
entry. That preceding signal decides whether to remove one own move. -/
def commitRecoveryInformationPredecessor (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.InfoState who :=
  match information.1.2 with
  | [] => information
  | previous :: earlier =>
    ((previous, earlier), if setup.commitRecoveryActive who previous then information.2.tail
      else information.2)

/-- Every actual legal source step retains its full predecessor information.
No assumption on the player moving or the kind of source transition is needed. -/
theorem commitRecoveryInformationPredecessor_infoOf (who : Player)
    {before after : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (reached : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    setup.commitRecoveryInformationPredecessor who
      (setup.commitRecoveryModel.infoOf who (trace.extend joint legal reached)) =
        setup.commitRecoveryModel.infoOf who trace := by
  classical
  have active : setup.commitRecoveryActive who
      (((setup.commitRecoverySignals).infoOf who trace).1) ↔
      setup.commitRecoveryProtocol.active before who := by
    rw [setup.commitRecoverySignals_current who trace]
    cases before with
    | none => rfl
    | some current =>
      simp only [commitRecoveryActive, commitRecoveryPrivate, commitRecoveryPublic,
        Option.map_some, Option.elim_some, ProtocolState.actor_observe_eq,
        commitRecoveryProtocol, CommitRecoveryState.Active]
  have permitted : LegalOption setup.commitRecoveryProtocol before who (joint who) :=
    setup.commitRecoveryProtocol.legalOption_of_legal legal who
  change setup.commitRecoveryInformationPredecessor who
      ((setup.commitRecoverySignals).withOwnPlayRecall.infoOf who
        (trace.extend joint legal reached)) =
    (setup.commitRecoverySignals).withOwnPlayRecall.infoOf who trace
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf,
    InfoSignals.infoOf_extend, InfoSignals.ownPlay_extend]
  cases selected : joint who with
  | none =>
    rw [selected] at permitted
    have inactive : ¬ setup.commitRecoveryActive who
        (((setup.commitRecoverySignals).infoOf who trace).1) := by
      intro acting
      exact permitted (active.mp acting)
    change ((((setup.commitRecoverySignals).infoOf who trace).1,
      ((setup.commitRecoverySignals).infoOf who trace).2),
      if setup.commitRecoveryActive who (((setup.commitRecoverySignals).infoOf who trace).1) then
        ((setup.commitRecoverySignals).ownPlay who trace).tail
      else (setup.commitRecoverySignals).ownPlay who trace) = _
    simp only [ite_eq_right inactive]
    exact Prod.ext (Prod.eta _) rfl
  | some move =>
    rw [selected] at permitted
    have acting : setup.commitRecoveryActive who
        (((setup.commitRecoverySignals).infoOf who trace).1) := active.mpr permitted.1
    change ((((setup.commitRecoverySignals).infoOf who trace).1,
      ((setup.commitRecoverySignals).infoOf who trace).2),
      if setup.commitRecoveryActive who (((setup.commitRecoverySignals).infoOf who trace).1) then
        (((setup.commitRecoverySignals).infoOf who trace, move) ::
          (setup.commitRecoverySignals).ownPlay who trace).tail
      else ((setup.commitRecoverySignals).infoOf who trace, move) ::
        (setup.commitRecoverySignals).ownPlay who trace) = _
    simp only [ite_eq_left acting, List.tail_cons]
    exact Prod.ext (Prod.eta _) rfl

end Vegas.SourceProgram.Setup
