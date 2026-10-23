/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedGame

/-! # Source histories are determined by their state

A source step records everything it consumes. A chance step keeps the
predecessor's cells under the drawn one, and a commit or a reveal appends the
owner's action to the owner's own action list, which determines the owner's
choice; only the acting player moves. The registry and the publication status
are not recorded in this way (a reveal overwrites the status of its source), but
they depend only on the program point, so they agree for any two states
reached in the same number of steps. Hence, at reachable states, the predecessor
and the joint action of a realized legal step are determined by its target, and
every history of the source protocol is determined by the state it reaches
(`Vegas.SourceProgram.Setup.executionProtocol_isTreeShaped`), in particular in
the intended game
(`Vegas.SourceProgram.Setup.intendedProtocol_history_eq_of_state`).
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Two configurations with the same retained obligations and publication status. -/
private def ConfigAligned {Γ : SourceCtx Player L} (first second : Config Player L Γ) : Prop :=
  first.registry = second.registry ∧
    @Config.revelations Player L Γ first = @Config.revelations Player L Γ second

/-- Two states at the same program point whose configurations there are aligned. -/
private def Aligned : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program →
      Prop
  | _, _, .ret _, first, second => ConfigAligned first second
  | _, _, .sample _ _ _ next, first, second =>
      Sum.elim (fun first => Sum.elim (fun second => ConfigAligned first second)
          (fun _ => False) second)
        (fun first => Sum.elim (fun _ => False) (fun second => Aligned next first second) second)
        first
  | _, _, .commit _ _ _ _ next, first, second =>
      Sum.elim (fun first => Sum.elim (fun second => ConfigAligned first second)
          (fun _ => False) second)
        (fun first => Sum.elim (fun _ => False) (fun second => Aligned next first second) second)
        first
  | _, _, .reveal _ _ _ _ _ _ next, first, second =>
      Sum.elim (fun first => Sum.elim (fun second => ConfigAligned first second)
          (fun _ => False) second)
        (fun first => Sum.elim (fun _ => False) (fun second => Aligned next first second) second)
        first

private theorem aligned_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) {first second : Config Player L Γ}
    (aligned : ConfigAligned first second) :
    Aligned program (entry program first) (entry program second) := by
  cases program <;> exact aligned

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem env_tail_eq {Γ : SourceCtx Player L} {name : VarId} {cell : CellTy Player L}
    {firstHead secondHead : CellVal L cell} {first second : State L Γ}
    (same : (Env.cons (x := name) firstHead first : State L ((name, cell) :: Γ)) =
      Env.cons secondHead second) : first = second :=
  funext fun y => funext fun τ => funext fun h =>
    congrFun (congrFun (congrFun same y) τ) (.there h)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem config_eq {Γ : SourceCtx Player L} {first second : Config Player L Γ}
    (state : first.state = second.state) (aligned : ConfigAligned first second)
    (history : first.history = second.history) : first = second := by
  obtain ⟨firstState, firstRegistry, firstRevelations, firstHistory⟩ := first
  obtain ⟨secondState, secondRegistry, secondRevelations, secondHistory⟩ := second
  obtain ⟨registry, revelations⟩ := aligned
  cases state
  cases registry
  cases revelations
  cases history
  rfl

omit [IExpr.ResultTypes L] in
/-- Appending one own action to one player's list determines the previous lists
and the appended action. -/
private theorem history_update_eq {owner : Player} {first second : History Player L}
    {firstAction secondAction : OwnAction Player L}
    (same : Function.update first owner (first owner ++ [firstAction]) =
      Function.update second owner (second owner ++ [secondAction])) :
    first = second ∧ firstAction = secondAction := by
  have atOwner := congrFun same owner
  simp only [Function.update_self] at atOwner
  obtain ⟨prefixEq, lastEq⟩ := List.append_inj' atOwner rfl
  refine ⟨funext fun who => ?_, List.singleton_inj.mp lastEq⟩
  by_cases mover : who = owner
  · subst who
    exact prefixEq
  · have atOther := congrFun same who
    simpa only [Function.update_of_ne mover] using atOther

private theorem eq_none_of_menu {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {admission : CommitmentInterface program}
    {view : ProtocolView who program} {choice : Option (OwnAction Player L)}
    (legal : ProtocolView.menu who program admission view choice)
    (other : ProtocolView.actor who program view ≠ some who) : choice = none := by
  cases choice with
  | none => rfl
  | some _ => exact (other legal.1).elim

/-- Alignment is preserved by any pair of realized steps. -/
private theorem aligned_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    {firstBefore secondBefore firstAfter secondAfter : ProtocolState program} →
    {firstJoint secondJoint : Player → Option (OwnAction Player L)} →
    Aligned program firstBefore secondBefore →
    firstAfter ∈ (step program firstBefore firstJoint).support →
    secondAfter ∈ (step program secondBefore secondJoint).support →
    Aligned program firstAfter secondAfter
  | _, _, .ret _, _, _, _, _, _, _, aligned, firstReached, secondReached => by
      rw [(PMF.mem_support_pure_iff _ _).mp firstReached,
        (PMF.mem_support_pure_iff _ _).mp secondReached]
      exact aligned
  | _, _, .sample _ _ _ next, firstBefore, secondBefore, _, _, _, _, aligned, firstReached,
      secondReached => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact aligned.elim
          | inl second =>
              simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, _, rfl⟩ := firstReached
              obtain ⟨_, _, rfl⟩ := secondReached
              obtain ⟨registry, revelations⟩ := aligned
              exact aligned_entry next ⟨by simp only [sampleSuccessor, registry],
                by simp only [sampleSuccessor, revelations]⟩
      | inr first =>
          cases secondBefore with
          | inl _ => exact aligned.elim
          | inr second =>
              simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, firstInner, rfl⟩ := firstReached
              obtain ⟨_, secondInner, rfl⟩ := secondReached
              exact aligned_step next (firstJoint := _) (secondJoint := _) aligned firstInner
                secondInner
  | _, _, .commit _ _ _ _ next, firstBefore, secondBefore, _, _, _, _, aligned,
      firstReached, secondReached => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact aligned.elim
          | inl second =>
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff]
                at firstReached secondReached
              subst firstReached secondReached
              obtain ⟨registry, revelations⟩ := aligned
              exact aligned_entry next ⟨by simp only [commitSuccessor, registry],
                by simp only [commitSuccessor, revelations]⟩
      | inr first =>
          cases secondBefore with
          | inl _ => exact aligned.elim
          | inr second =>
              simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, firstInner, rfl⟩ := firstReached
              obtain ⟨_, secondInner, rfl⟩ := secondReached
              exact aligned_step next (firstJoint := _) (secondJoint := _) aligned firstInner
                secondInner
  | _, _, .reveal _ _ _ _ _ _ next, firstBefore, secondBefore, _, _, _, _,
      aligned, firstReached, secondReached => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact aligned.elim
          | inl second =>
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff]
                at firstReached secondReached
              subst firstReached secondReached
              obtain ⟨registry, revelations⟩ := aligned
              exact aligned_entry next ⟨by simp only [revealSuccessor, registry],
                by simp only [revealSuccessor, revelations]⟩
      | inr first =>
          cases secondBefore with
          | inl _ => exact aligned.elim
          | inr second =>
              simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, firstInner, rfl⟩ := firstReached
              obtain ⟨_, secondInner, rfl⟩ := secondReached
              exact aligned_step next (firstJoint := _) (secondJoint := _) aligned firstInner
                secondInner

/-- At aligned states, the predecessor and the joint action of a realized legal
step are determined by its target. -/
private theorem predecessor_unique : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    {firstBefore secondBefore after : ProtocolState program} →
    {firstJoint secondJoint : Player → Option (OwnAction Player L)} →
    Aligned program firstBefore secondBefore → ¬ terminal program firstBefore →
    (∀ who, ProtocolView.menu who program admission (observe who program firstBefore)
      (firstJoint who)) →
    (∀ who, ProtocolView.menu who program admission (observe who program secondBefore)
      (secondJoint who)) →
    after ∈ (step program firstBefore firstJoint).support →
    after ∈ (step program secondBefore secondJoint).support →
    firstBefore = secondBefore ∧ firstJoint = secondJoint
  | _, _, .ret _, _, _, _, _, _, _, _, running, _, _, _, _ => (running trivial).elim
  | _, _, .sample name _ _ next, admission, firstBefore, secondBefore, _, firstJoint,
      secondJoint, aligned, running, firstLegal, secondLegal, firstReached,
      secondReached => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact aligned.elim
          | inl second =>
              simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, _, rfl⟩ := firstReached
              obtain ⟨_, _, same⟩ := secondReached
              have successor := entry_injective next (Sum.inr.inj same)
              have stateEq := env_tail_eq (congrArg Config.state successor)
              have historyEq := congrArg Config.history successor
              refine ⟨congrArg Sum.inl (config_eq stateEq.symm ⟨aligned.1, aligned.2⟩
                historyEq.symm), funext fun who => ?_⟩
              rw [eq_none_of_menu (firstLegal who) (by simp [observe, ProtocolView.actor]),
                eq_none_of_menu (secondLegal who) (by simp [observe, ProtocolView.actor])]
      | inr first =>
          cases secondBefore with
          | inl _ => exact aligned.elim
          | inr second =>
              simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, firstInner, rfl⟩ := firstReached
              obtain ⟨_, secondInner, same⟩ := secondReached
              cases Sum.inr.inj same
              obtain ⟨rfl, rfl⟩ := predecessor_unique next admission aligned running
                firstLegal secondLegal firstInner secondInner
              exact ⟨rfl, rfl⟩
  | _, _, .commit (payload := payload) name owner _ guard next, admission, firstBefore,
      secondBefore, _, firstJoint, secondJoint, aligned, running, firstLegal, secondLegal,
      firstReached, secondReached => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact aligned.elim
          | inl second =>
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff]
                at firstReached secondReached
              subst firstReached
              have firstOwner := firstLegal owner
              have secondOwner := secondLegal owner
              cases firstChosen : firstJoint owner with
              | none =>
                  rw [firstChosen] at firstOwner
                  exact (firstOwner (by simp [observe, ProtocolView.actor])).elim
              | some firstAction =>
              cases secondChosen : secondJoint owner with
              | none =>
                  rw [secondChosen] at secondOwner
                  exact (secondOwner (by simp [observe, ProtocolView.actor])).elim
              | some secondAction =>
              rw [firstChosen] at firstOwner
              rw [secondChosen] at secondOwner
              obtain ⟨_, firstChoice, _, rfl⟩ := firstOwner
              obtain ⟨_, secondChoice, _, rfl⟩ := secondOwner
              rw [firstChosen, secondChosen, OwnAction.binding_commit,
                OwnAction.binding_commit] at secondReached
              have successor := entry_injective next (Sum.inr.inj secondReached)
              have stateEq := env_tail_eq (congrArg Config.state successor)
              obtain ⟨historyEq, actionEq⟩ :=
                history_update_eq (congrArg Config.history successor)
              refine ⟨congrArg Sum.inl (config_eq stateEq ⟨aligned.1, aligned.2⟩
                historyEq), funext fun who => ?_⟩
              by_cases mover : who = owner
              · subst who
                rw [firstChosen, secondChosen, actionEq]
              · have notActor := Ne.symm mover
                rw [eq_none_of_menu (firstLegal who)
                    (by simpa [observe, ProtocolView.actor] using notActor),
                  eq_none_of_menu (secondLegal who)
                    (by simpa [observe, ProtocolView.actor] using notActor)]
      | inr first =>
          cases secondBefore with
          | inl _ => exact aligned.elim
          | inr second =>
              simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, firstInner, rfl⟩ := firstReached
              obtain ⟨_, secondInner, same⟩ := secondReached
              cases Sum.inr.inj same
              obtain ⟨rfl, rfl⟩ := predecessor_unique next (fun site => admission (some site))
                aligned running firstLegal secondLegal firstInner secondInner
              exact ⟨rfl, rfl⟩
  | _, _, .reveal published owner name _ source _ next, admission, firstBefore, secondBefore,
      _, firstJoint, secondJoint, aligned, running, firstLegal, secondLegal, firstReached,
      secondReached => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact aligned.elim
          | inl second =>
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff]
                at firstReached secondReached
              subst firstReached
              have firstOwner := firstLegal owner
              have secondOwner := secondLegal owner
              cases firstChosen : firstJoint owner with
              | none =>
                  rw [firstChosen] at firstOwner
                  exact (firstOwner (by simp [observe, ProtocolView.actor])).elim
              | some firstAction =>
              cases secondChosen : secondJoint owner with
              | none =>
                  rw [secondChosen] at secondOwner
                  exact (secondOwner (by simp [observe, ProtocolView.actor])).elim
              | some secondAction =>
              rw [firstChosen] at firstOwner
              rw [secondChosen] at secondOwner
              obtain ⟨_, firstDisclose, rfl⟩ := firstOwner
              obtain ⟨_, secondDisclose, rfl⟩ := secondOwner
              rw [firstChosen, secondChosen] at secondReached
              have successor := entry_injective next (Sum.inr.inj secondReached)
              have stateEq := env_tail_eq (congrArg Config.state successor)
              obtain ⟨historyEq, actionEq⟩ :=
                history_update_eq (congrArg Config.history successor)
              refine ⟨congrArg Sum.inl (config_eq stateEq ⟨aligned.1, aligned.2⟩
                historyEq), funext fun who => ?_⟩
              by_cases mover : who = owner
              · subst who
                rw [firstChosen, secondChosen]
                simp only [OwnAction.disclosure] at actionEq
                rw [actionEq]
              · have notActor := Ne.symm mover
                rw [eq_none_of_menu (firstLegal who)
                    (by simpa [observe, ProtocolView.actor] using notActor),
                  eq_none_of_menu (secondLegal who)
                    (by simpa [observe, ProtocolView.actor] using notActor)]
      | inr first =>
          cases secondBefore with
          | inl _ => exact aligned.elim
          | inr second =>
              simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
                at firstReached secondReached
              obtain ⟨_, firstInner, rfl⟩ := firstReached
              obtain ⟨_, secondInner, same⟩ := secondReached
              cases Sum.inr.inj same
              obtain ⟨rfl, rfl⟩ := predecessor_unique next admission aligned running
                firstLegal secondLegal firstInner secondInner
              exact ⟨rfl, rfl⟩

end ProtocolState

namespace Setup

/-- Aligned setup states: both before the draw, or aligned source states. -/
private def SetupAligned (setup : Setup (Player := Player) (L := L)) :
    setup.ProtocolState → setup.ProtocolState → Prop
  | none, none => True
  | some first, some second => ProtocolState.Aligned setup.program first second
  | _, _ => False

private theorem setupAligned_step (setup : Setup (Player := Player) (L := L))
    {firstBefore secondBefore firstAfter secondAfter : setup.ProtocolState}
    {firstJoint secondJoint : Player → Option (OwnAction Player L)}
    (aligned : setup.SetupAligned firstBefore secondBefore)
    (firstReached : firstAfter ∈ (setup.protocolStep firstBefore firstJoint).support)
    (secondReached : secondAfter ∈ (setup.protocolStep secondBefore secondJoint).support) :
    setup.SetupAligned firstAfter secondAfter := by
  cases firstBefore with
  | none =>
      cases secondBefore with
      | some _ => exact aligned.elim
      | none =>
          simp only [protocolStep, PMF.support_map, Set.mem_image] at firstReached secondReached
          obtain ⟨_, _, rfl⟩ := firstReached
          obtain ⟨_, _, rfl⟩ := secondReached
          exact ProtocolState.aligned_entry setup.program ⟨rfl, rfl⟩
  | some first =>
      cases secondBefore with
      | none => exact aligned.elim
      | some second =>
          simp only [protocolStep, PMF.support_map, Set.mem_image] at firstReached secondReached
          obtain ⟨_, firstInner, rfl⟩ := firstReached
          obtain ⟨_, secondInner, rfl⟩ := secondReached
          exact ProtocolState.aligned_step setup.program aligned firstInner secondInner

/-- Histories of equal length reach aligned states. -/
private theorem setupAligned_of_length (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    ∀ {first second : setup.ProtocolState}
      (firstTrace : (setup.executionProtocol admission).Trace first)
      (secondTrace : (setup.executionProtocol admission).Trace second),
      firstTrace.length = secondTrace.length → setup.SetupAligned first second
  | _, _, .start, .start, _ => trivial
  | _, _, .start, .extend _ _ _ _, same => by simp [Trace.length] at same
  | _, _, .extend _ _ _ _, .start, same => by simp [Trace.length] at same
  | _, _, .extend firstPrior _ _ firstReached, .extend secondPrior _ _ secondReached,
      same => by
      simp only [Trace.length, Nat.add_right_cancel_iff] at same
      exact setup.setupAligned_step (setup.setupAligned_of_length admission firstPrior
        secondPrior same) firstReached secondReached

private theorem menu_of_legal (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    {state : SourceProgram.ProtocolState setup.program}
    {joint : Player → Option (OwnAction Player L)}
    (legal : (setup.executionProtocol admission).Legal (some state) joint) (who : Player) :
    ProtocolView.menu who setup.program admission
      (ProtocolState.observe who setup.program state) (joint who) := by
  have member := legal.2 who
  revert member
  cases joint who <;> exact id

private theorem predecessor_unique (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    {firstBefore secondBefore after : setup.ProtocolState}
    {firstJoint secondJoint : Player → Option (OwnAction Player L)}
    (aligned : setup.SetupAligned firstBefore secondBefore)
    (firstLegal : (setup.executionProtocol admission).Legal firstBefore firstJoint)
    (secondLegal : (setup.executionProtocol admission).Legal secondBefore secondJoint)
    (firstReached : after ∈ (setup.protocolStep firstBefore firstJoint).support)
    (secondReached : after ∈ (setup.protocolStep secondBefore secondJoint).support) :
    firstBefore = secondBefore ∧ firstJoint = secondJoint := by
  cases firstBefore with
  | none =>
      cases secondBefore with
      | some _ => exact aligned.elim
      | none =>
          refine ⟨rfl, funext fun who => ?_⟩
          have first := firstLegal.2 who
          have second := secondLegal.2 who
          revert first second
          cases firstJoint who <;> cases secondJoint who <;>
            simp [executionProtocol, protocolObserve]
  | some first =>
      cases secondBefore with
      | none => exact aligned.elim
      | some second =>
          simp only [protocolStep, PMF.support_map, Set.mem_image] at firstReached secondReached
          obtain ⟨_, firstInner, rfl⟩ := firstReached
          obtain ⟨_, secondInner, same⟩ := secondReached
          cases Option.some.inj same
          obtain ⟨rfl, rfl⟩ := ProtocolState.predecessor_unique setup.program admission aligned
            firstLegal.1 (setup.menu_of_legal admission firstLegal)
            (setup.menu_of_legal admission secondLegal) firstInner secondInner
          exact ⟨rfl, rfl⟩

private theorem init_not_reached (setup : Setup (Player := Player) (L := L))
    (before : setup.ProtocolState) (joint : Player → Option (OwnAction Player L)) :
    none ∉ (setup.protocolStep before joint).support := by
  intro reached
  cases before <;>
    · simp only [protocolStep, PMF.support_map, Set.mem_image] at reached
      obtain ⟨_, _, impossible⟩ := reached
      cases impossible

/-- **Source histories are determined by their state.** Under every commitment
interface, each state of the source protocol has at most one history. -/
theorem executionProtocol_isTreeShaped (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.executionProtocol admission).IsTreeShaped := by
  intro state
  constructor
  intro first second
  induction first with
  | start =>
      cases second with
      | start => rfl
      | extend _ _ _ realized => exact (setup.init_not_reached _ _ realized).elim
  | @extend source target prior joint legal realized ih =>
      cases second with
      | start => exact (setup.init_not_reached _ _ realized).elim
      | @extend other _ otherPrior otherJoint otherLegal otherRealized =>
          have firstCount := setup.protocol_history_length admission
            (Trace.extend prior joint legal realized)
          have secondCount := setup.protocol_history_length admission
            (Trace.extend otherPrior otherJoint otherLegal otherRealized)
          simp only [Trace.length] at firstCount secondCount
          have aligned := setup.setupAligned_of_length admission prior otherPrior (by omega)
          obtain ⟨rfl, rfl⟩ := setup.predecessor_unique admission aligned legal otherLegal
            realized otherRealized
          cases ih otherPrior
          rfl

/-- Each state of the intended protocol has at most one history. -/
theorem intendedProtocol_isTreeShaped (setup : Setup (Player := Player) (L := L)) :
    setup.intendedProtocol.IsTreeShaped := by
  intro state
  constructor
  intro first second
  have unique := setup.executionProtocol_isTreeShaped
    (CommitmentInterface.values setup.program) state
  exact restrictAvailable.trace_injective (Subsingleton.elim _ _)

/-- **Intended histories are determined by their state.** Two histories of the
intended game reaching the same state are equal. -/
theorem intendedProtocol_history_eq_of_state (setup : Setup (Player := Player) (L := L))
    {first second : setup.intendedProtocol.History} (same : first.state = second.state) :
    first = second := by
  obtain ⟨firstState, firstTrace⟩ := first
  obtain ⟨secondState, secondTrace⟩ := second
  change firstState = secondState at same
  subst same
  have unique := setup.intendedProtocol_isTreeShaped firstState
  rw [Subsingleton.elim firstTrace secondTrace]

end Setup

end Vegas.SourceProgram
