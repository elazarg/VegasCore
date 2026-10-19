/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBindingReplay
import Vegas.Source.CommitRecoveryCommitStep

/-! # Genuine recovery histories with virtual domain replacements -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

/-- Raw pre-close witnesses retained from the existing virtual instruction
coupling. Publication comparisons can read the actual guard result before
automatic commitment closure without assuming any rollback property. -/
def VirtualRepairResult {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (preserved : Finset VarId) (who : Player)
    (original repaired : CommitRecoveryState program)
    (joint translated : Player → Option (CommitRecoveryMove Player L)) : Prop :=
  ∃ left right : ProtocolState program × Finset Player,
    left ∈ (ProtocolState.recoveryStep program original.point original.excluded joint).support ∧
    right ∈
      (ProtocolState.recoveryStep program repaired.point repaired.excluded translated).support ∧
    right.2 = left.2 ∧
    ProtocolState.VirtualRepair preserved who program left.1 right.1 ∧ who ∉ left.2

/-- One genuine instruction and its actual dispatcher have a legal repaired
partner. Public omissions, occurrence identity and original foreign choices
are retained, even when the final slot retries or exhausts its block. -/
theorem VirtualRepair.step {Γ : SourceCtx Player L} {O : Finset VarId}
    {preserved : Finset VarId} {program : SourceProgram Player L Γ O} {who : Player}
    {original repaired : CommitRecoveryState program}
    (related : VirtualRepair preserved who original repaired)
    (known : preserved ⊆ (Γ.map Prod.fst).toFinset)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : IsLegalJoint original.Active original.available joint)
    (after : CommitRecoveryState program) (reached : after ∈ (original.step joint).support)
    (survives : who ∉ after.excluded) :
    ∃ translated : Player → Option (CommitRecoveryMove Player L),
      (∀ observer, observer ≠ who → translated observer = joint observer) ∧
      IsLegalJoint repaired.Active repaired.available translated ∧
      ∃ paired ∈ (repaired.step translated).support,
        VirtualRepair preserved who after paired ∧
          VirtualRepairResult preserved who original repaired joint translated := by
  obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  subst after
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program original.point original.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program original.point original.excluded joint)
      (fun value supported => ProtocolState.recoveryStep_excluded_monotone program original.point
        original.excluded joint value supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have active : who ∉ result.1.2 := by simpa only [close_excluded, install] using survives
  obtain ⟨translated, same, permitted, paired, supported, exclusions, point⟩ :=
    ProtocolState.VirtualRepair.recoveryStep preserved who program original.point repaired.point
      related.point known original.excluded joint legal result.1 raw active
  have actual : paired ∈
      (ProtocolState.recoveryStep program repaired.point repaired.excluded translated).support := by
    simpa only [related.excluded] using supported
  let monotone := ProtocolState.recoveryStep_excluded_monotone program repaired.point
    repaired.excluded translated paired actual
  have pairedRelation : VirtualRepair preserved who (original.install result.1 result.2)
      (repaired.install paired monotone) :=
    ⟨point, related.saved, exclusions, related.entryExcluded, related.generation⟩
  refine ⟨translated, same, ?_, (repaired.install paired monotone).close,
    repaired.step_contains_close translated paired monotone actual, pairedRelation.close active,
      result.1, paired, raw, actual, exclusions, point, active⟩
  simpa only [IsLegalJoint, Active, available, atPoint, related.excluded] using permitted

end CommitRecoveryState

namespace Setup

/-- The paired real recovery states emit identical actual public signals.
The current private typed virtual fields are intentionally retained separately. -/
theorem commitRecovery_publicSignal_of_focalRepair
    (setup : Setup (Player := Player) (L := L)) {who : Player}
    {original repaired : CommitRecoveryState setup.program}
    (related : CommitRecoveryState.FocalRepair who original repaired) (observer : Player) :
    setup.attemptPublicSignal observer (some repaired) =
      setup.attemptPublicSignal observer (some original) := by
  have fields := ProtocolState.FocalRepair.publicOnly who setup.program _ _ related.point observer
  have saved := ProtocolState.FocalRepair.control who setup.program _ _ related.saved
  simp only [attemptPublicSignal, commitRecoveryPrivate, commitRecoveryPublic, Option.map_some,
    fields, related.excluded, related.generation, saved.1]

/-- Literal actual events of the existing recovery trace, newest first. This
proof readout retains the pre-state and joint discarded by public recall. -/
def commitRecoveryEventRecall (setup : Setup (Player := Player) (L := L)) :
    ∀ {state : setup.commitRecoveryProtocol.State},
      setup.commitRecoveryProtocol.Trace state → List setup.commitRecoveryProtocol.StepEvent
  | _, .start => []
  | _, .extend prior joint legal supported =>
      ⟨_, joint, legal, _, supported⟩ :: commitRecoveryEventRecall setup prior

/-- Evidence retained by the existing paired recovery construction. Literal
initial events agree; subsequent pairs keep actual states, foreign choices,
and the surviving actor's typed-store repair at BOTH ends of the step. -/
def CommitRecoveryVirtualEvent (setup : Setup (Player := Player) (L := L)) (who : Player)
    (left right : setup.commitRecoveryProtocol.StepEvent) : Prop :=
  left = right ∨ ∃ original repaired after paired : CommitRecoveryState setup.program,
    left.source = some original ∧ right.source = some repaired ∧
    left.target = some after ∧ right.target = some paired ∧
    CommitRecoveryState.VirtualRepair (setup.context.map Prod.fst).toFinset who
      original repaired ∧
    CommitRecoveryState.VirtualRepair (setup.context.map Prod.fst).toFinset who after paired ∧
    (∀ observer, observer ≠ who → right.joint observer = left.joint observer) ∧
    who ∉ after.excluded ∧
    CommitRecoveryState.VirtualRepairResult (setup.context.map Prod.fst).toFinset who
      original repaired left.joint right.joint

/-- Every genuine initialized recovery history of a surviving owner admits
an actual legal history of the same length with its latent failed bindings
replaced by domain values. The complete public source signal word, every
foreign choice and the actual retry/exhaustion dispatch are preserved. -/
theorem commitRecovery_virtual_history
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (current : CommitRecoveryState setup.program) (present : state = some current)
    (survives : who ∉ current.excluded) :
    ∃ repaired : CommitRecoveryState setup.program,
      ∃ replay : setup.commitRecoveryProtocol.Trace (some repaired),
        replay.length = trace.length ∧
        CommitRecoveryState.VirtualRepair (setup.context.map Prod.fst).toFinset who
          current repaired ∧
        (∀ observer, setup.attemptPublicRecall observer replay =
          setup.attemptPublicRecall observer trace) ∧
        List.Forall₂ (setup.CommitRecoveryVirtualEvent who)
          (setup.commitRecoveryEventRecall trace) (setup.commitRecoveryEventRecall replay) := by
  have build : ∀ {source : setup.commitRecoveryProtocol.State}
      (path : setup.commitRecoveryProtocol.Trace source),
      ∀ original, source = some original → who ∉ original.excluded →
      ∃ repaired : CommitRecoveryState setup.program,
        ∃ replay : setup.commitRecoveryProtocol.Trace (some repaired),
          replay.length = path.length ∧
          CommitRecoveryState.VirtualRepair (setup.context.map Prod.fst).toFinset who
            original repaired ∧
          (∀ observer, setup.attemptPublicRecall observer replay =
            setup.attemptPublicRecall observer path) ∧
          List.Forall₂ (setup.CommitRecoveryVirtualEvent who)
            (setup.commitRecoveryEventRecall path) (setup.commitRecoveryEventRecall replay) := by
    intro source path
    induction path with
    | start => intro original impossible; cases impossible
    | @extend before after prior joint legal supported ih =>
        intro original present active
        cases before with
        | none =>
            obtain ⟨input, drawn, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
            cases equal
            cases Option.some.inj present
            let paired := ProtocolState.virtualRepair_entry
              (setup.context.map Prod.fst).toFinset who setup.program
              (Config.VirtualRepair.initial who (setup.initialConfig input))
            exact ⟨_, .extend prior joint legal supported, rfl,
              ⟨paired, paired, rfl, rfl, rfl⟩, (fun _ => rfl),
              List.forall₂_same.mpr (fun _ _ => Or.inl rfl)⟩
        | some before =>
            have actual := supported
            rw [present] at actual
            obtain ⟨target, targetSupport, targetEq⟩ :=
              (PMF.mem_support_map_iff _ _ _).mp actual
            have targetSame := Option.some.inj targetEq
            subst target
            have priorActive : who ∉ before.excluded := fun excluded =>
              active (before.step_excluded_monotone joint original targetSupport excluded)
            obtain ⟨paired, pairedTrace, length, relation, recall, annotated⟩ :=
              ih before rfl priorActive
            obtain ⟨translated, foreign, permitted, next, nextSupport,
                nextRelation, rawRelation⟩ :=
              relation.step (Finset.Subset.refl _) joint legal.2 original targetSupport active
            have running : ¬ ProtocolState.terminal setup.program paired.point :=
              fun stopped => legal.1
                ((ProtocolState.FocalRepair.terminal_iff who setup.program _ _
                  relation.focalRepair.point).mp
                  stopped)
            have translatedLegal : setup.commitRecoveryProtocol.Legal (some paired) translated :=
              ⟨running, permitted⟩
            have realized : some next ∈
                (setup.commitRecoveryProtocol.step (some paired)
                  ⟨translated, translatedLegal⟩).support :=
              (PMF.mem_support_map_iff _ _ _).mpr ⟨next, nextSupport, rfl⟩
            let replay := pairedTrace.extend translated translatedLegal realized
            refine ⟨next, replay, ?_, nextRelation, ?_, ?_⟩
            · simpa only [replay, Trace.length] using congrArg (· + 1) length
            · intro observer
              have newSignal := setup.commitRecovery_publicSignal_of_focalRepair
                nextRelation.focalRepair
                observer
              dsimp only [replay, attemptPublicRecall]
              rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
              change setup.attemptPublicSignal observer (some next) ::
                  setup.attemptPublicRecall observer pairedTrace =
                setup.attemptPublicSignal observer after :: setup.attemptPublicRecall observer prior
              rw [newSignal, recall observer, present]
            · exact List.Forall₂.cons
                (Or.inr ⟨before, paired, original, next, rfl, rfl, present, rfl,
                  relation, nextRelation, foreign, active, rawRelation⟩) annotated
  exact build trace current present survives

end Setup

end Vegas.SourceProgram
