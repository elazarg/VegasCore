/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.IntendedBetween
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Prefixes of intended histories and the swap between their ends

A cell swap commutes with looking a cell up
(`Vegas.SourceProgram.ProtocolState.cell?_swap`), and a source step keeps every
cell it finds (`Vegas.SourceProgram.ProtocolState.cell?_step`): chance, commits
and reveals only add cells under fresh names.

**Prefixes.** Let two intended histories have the same length and public default record,
and end at p and q. Every prefix of the first has a prefix of the second of the same
length, and the swap between p and q maps the state of the first prefix to
the state of the second (`Vegas.SourceProgram.Setup.intended_prefix_between`).
Every cell found at the earlier state is still found, with the same value, at
the later one, so on the values of the earlier state the swap between the ends
agrees with the swap between the prefix states.

**The acting choice.** A realized step of the intended game is determined, on
the acting player, by its target: if the step of a choice addressed to the
acting site, played by everybody, reaches the same target, then the acting
player's component of the joint action is that choice
(`Vegas.SourceProgram.Setup.intended_joint_eq_of_choice`). The choice must be
addressed to the site: at a reveal, every opening reveal reaches the same
target.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section CellLookup

variable [DecidableEq (CellTy Player L)]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A swapped state finds the swap of the value found before. -/
theorem State.cell?_swap (swap : CellSwap Player L) (name : VarId) (kind : CellTy Player L) :
    ∀ {Γ : SourceCtx Player L} (cells : State L Γ),
      State.cell? (swap.state cells) name kind =
        (State.cell? cells name kind).map (swap.cell name kind)
  | [], _ => rfl
  | (current, currentKind) :: _, cells => by
      rw [State.cell?.eq_2, State.cell?.eq_2]
      split_ifs with same
      · obtain ⟨rfl, rfl⟩ := same
        rfl
      · exact State.cell?_swap swap name kind
          (fun other otherKind source => cells other otherKind (.there source))

/-- **Swapping commutes with lookup.** A swapped program point finds the swap of
the value found before. -/
theorem ProtocolState.cell?_swap (swap : CellSwap Player L) (name : VarId)
    (kind : CellTy Player L) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
      ProtocolState.cell? program (swap.protocolState program state) name kind =
        (ProtocolState.cell? program state name kind).map (swap.cell name kind)
  | _, _, .ret _, config => State.cell?_swap swap name kind config.state
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl config => exact State.cell?_swap swap name kind config.state
      | inr rest => exact ProtocolState.cell?_swap swap name kind next rest
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl config => exact State.cell?_swap swap name kind config.state
      | inr rest => exact ProtocolState.cell?_swap swap name kind next rest
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl config => exact State.cell?_swap swap name kind config.state
      | inr rest => exact ProtocolState.cell?_swap swap name kind next rest

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A cell found in a state is found in the state with a fresh cell added. -/
private theorem State.cell?_cons_of_found {Γ : SourceCtx Player L} {x name : VarId}
    {head : CellTy Player L} (fresh : x ∉ Γ.map Prod.fst) (headValue : CellVal L head)
    {cells : State L Γ} {kind : CellTy Player L} {value : CellVal L kind}
    (found : State.cell? cells name kind = some value) :
    State.cell? (Env.cons (x := x) headValue cells : State L ((x, head) :: Γ)) name kind =
      some value := by
  rw [State.cell?_cons_of_ne _ _ fun same : x = name =>
    fresh (by rw [same]; exact State.mem_of_cell?_eq_some found)]
  exact found

/-- An entry point finds the cells of its configuration. -/
theorem ProtocolState.cell?_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) (name : VarId)
    (kind : CellTy Player L) :
    ProtocolState.cell? program (ProtocolState.entry program config) name kind =
      State.cell? config.state name kind := by
  cases program <;> rfl

/-- **Cells persist along a step.** A source step keeps every cell it finds,
with its value. -/
theorem ProtocolState.cell?_step {name : VarId} {kind : CellTy Player L}
    {value : CellVal L kind} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → {before after : ProtocolState program} →
    {joint : Player → Option (OwnAction Player L)} →
    after ∈ (ProtocolState.step program before joint).support →
    ProtocolState.cell? program before name kind = some value →
    ProtocolState.cell? program after name kind = some value
  | _, _, .ret _, _, _, _, reached, found => by
      rw [(PMF.mem_support_pure_iff _ _).mp reached]
      exact found
  | _, _, .sample _ fresh _ next, before, _, _, reached, found => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.support_map, Set.mem_image]
            at reached
          obtain ⟨_, _, rfl⟩ := reached
          change ProtocolState.cell? next (ProtocolState.entry next _) name kind = some value
          rw [ProtocolState.cell?_entry]
          exact State.cell?_cons_of_found fresh _ found
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image]
            at reached
          obtain ⟨_, inner, rfl⟩ := reached
          exact ProtocolState.cell?_step next inner found
  | _, _, .commit _ _ fresh _ next, before, _, _, reached, found => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          change ProtocolState.cell? next (ProtocolState.entry next _) name kind = some value
          rw [ProtocolState.cell?_entry]
          exact State.cell?_cons_of_found fresh _ found
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image]
            at reached
          obtain ⟨_, inner, rfl⟩ := reached
          exact ProtocolState.cell?_step next inner found
  | _, _, .reveal _ _ _ fresh _ _ next, before, _, _, reached, found => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          change ProtocolState.cell? next (ProtocolState.entry next _) name kind = some value
          rw [ProtocolState.cell?_entry]
          exact State.cell?_cons_of_found fresh _ found
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image]
            at reached
          obtain ⟨_, inner, rfl⟩ := reached
          exact ProtocolState.cell?_step next inner found

end CellLookup

section ActingChoice

/-- **The acting choice of a realized intended step.** At a program point, let
an intended joint action and the joint action giving everybody one choice
addressed to the acting site reach the same state. Then the acting player
plays that choice. -/
theorem ProtocolState.intended_actor_eq_choice : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (admission : CommitmentInterface program) → {point after : ProtocolState program} →
    {joint : Player → Option (OwnAction Player L)} → {choice : Option (OwnAction Player L)} →
    (∀ who, ProtocolView.intendedMenu who program (observe who program point) (joint who)) →
    (∀ who action, choice = some action →
      ProtocolView.actor who program (observe who program point) = some who →
        action ∈ ProtocolView.available who program admission (observe who program point)) →
    after ∈ (step program point joint).support →
    after ∈ (step program point fun _ => choice).support →
    ∀ who, ProtocolView.actor who program (observe who program point) = some who →
      joint who = choice
  | _, _, .ret _, _, _, _, _, _, _, _, _, _ => by
      intro _ acting
      simp [ProtocolView.actor] at acting
  | _, _, .sample _ _ _ next, admission, point, _, _, _, legal, addressed, reached,
      choiceReached => by
      cases point with
      | inl _ =>
          intro _ acting
          simp [observe, ProtocolView.actor] at acting
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
            at reached choiceReached
          obtain ⟨_, inner, rfl⟩ := reached
          obtain ⟨_, choiceInner, same⟩ := choiceReached
          cases Sum.inr.inj same
          exact intended_actor_eq_choice next admission legal addressed inner choiceInner
  | _, _, .commit (payload := payload) name owner _ _ next, admission, point, _, joint,
      choice, legal, addressed, reached, choiceReached => by
      cases point with
      | inl config =>
          intro who acting
          have activeOwner : owner ∉ config.defaulted ∧ owner = who := by
            simpa [observe, ProtocolView.actor] using acting
          have active := activeOwner.1
          have mover := activeOwner.2
          subst mover
          have ownerLegal := legal owner
          cases chosen : joint owner with
          | none =>
              rw [chosen] at ownerLegal
              exact (ownerLegal acting).elim
          | some action =>
              rw [chosen] at ownerLegal
              obtain ⟨_, value, _, rfl⟩ := ownerLegal
              cases choice with
              | none =>
                  simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff]
                    at reached choiceReached
                  subst reached
                  rw [chosen, OwnAction.binding_commit] at choiceReached
                  have successor := entry_injective next (Sum.inr.inj choiceReached)
                  have lists := congrArg (fun config => config.history owner) successor
                  simp only [commitSuccessor, active, ite_false, Function.update_self,
                    List.append_cancel_left_eq,
                    List.cons.injEq, OwnAction.commit.injEq, heq_eq_eq, true_and,
                    and_true] at lists
                  simp [OwnAction.binding] at lists
              | some other =>
                  obtain ⟨otherChoice, _, rfl⟩ := addressed owner other rfl acting
                  simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff]
                    at reached choiceReached
                  subst reached
                  rw [chosen, OwnAction.binding_commit, OwnAction.binding_commit]
                    at choiceReached
                  have successor := entry_injective next (Sum.inr.inj choiceReached)
                  have lists := congrArg (fun config => config.history owner) successor
                  simp only [commitSuccessor, active, ite_false, Function.update_self,
                    List.append_cancel_left_eq,
                    List.cons.injEq, OwnAction.commit.injEq, heq_eq_eq, true_and,
                    and_true] at lists
                  rw [lists]
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
            at reached choiceReached
          obtain ⟨_, inner, rfl⟩ := reached
          obtain ⟨_, choiceInner, same⟩ := choiceReached
          cases Sum.inr.inj same
          exact intended_actor_eq_choice next (fun site => admission (some site)) legal
            addressed inner choiceInner
  | _, _, .reveal _ owner name _ _ _ next, admission, point, _, joint, choice, legal,
      addressed, reached, choiceReached => by
      cases point with
      | inl config =>
          intro who acting
          have activeOwner : owner ∉ config.defaulted ∧ owner = who := by
            simpa [observe, ProtocolView.actor] using acting
          have active := activeOwner.1
          have mover := activeOwner.2
          subst mover
          have ownerLegal := legal owner
          cases chosen : joint owner with
          | none =>
              rw [chosen] at ownerLegal
              exact (ownerLegal acting).elim
          | some action =>
              rw [chosen] at ownerLegal
              obtain ⟨_, opening⟩ := ownerLegal
              have opens : action = .reveal owner name true := opening
              subst opens
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached choiceReached
              subst reached
              rw [chosen] at choiceReached
              have successor := entry_injective next (Sum.inr.inj choiceReached)
              have lists := congrArg (fun config => config.history owner) successor
              simp only [revealSuccessor, active, ite_false, Function.update_self,
                List.append_cancel_left_eq,
                List.cons.injEq, OwnAction.reveal.injEq, true_and, and_true] at lists
              cases choice with
              | none => simp [OwnAction.disclosure] at lists
              | some other =>
                  obtain ⟨disclose, rfl⟩ := addressed owner other rfl acting
                  simp only [OwnAction.disclosure] at lists
                  rw [← lists]
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image]
            at reached choiceReached
          obtain ⟨_, inner, rfl⟩ := reached
          obtain ⟨_, choiceInner, same⟩ := choiceReached
          cases Sum.inr.inj same
          exact intended_actor_eq_choice next admission legal addressed inner choiceInner

end ActingChoice

/-- Every history has a prefix of each smaller length. -/
private theorem exists_tracePrefix_of_le {ι : Type*} {E : ExecutionProtocol ι} :
    ∀ {state : E.State} (trace : E.Trace state) {length : ℕ}, length ≤ trace.length →
      ∃ (start : E.State) (prefixTrace : E.Trace start),
        TracePrefix prefixTrace trace ∧ prefixTrace.length = length
  | _, .start, _, short => ⟨_, .start, .refl, by simp only [Trace.length] at short ⊢; omega⟩
  | _, .extend prior joint isLegal realized, length, short => by
      by_cases whole : length = prior.length + 1
      · exact ⟨_, _, .refl, by simp only [Trace.length, whole]⟩
      · simp only [Trace.length] at short
        obtain ⟨_, prefixTrace, isPrefix, same⟩ :=
          exists_tracePrefix_of_le prior (length := length) (by omega)
        exact ⟨_, prefixTrace, .extend isPrefix joint isLegal realized, same⟩

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- An intended history before setup is empty. -/
private theorem trace_length_eq_zero {state : setup.ProtocolState}
    (trace : setup.intendedProtocol.Trace state) (before : state = none) : trace.length = 0 := by
  subst before
  have count := setup.protocol_history_length _ (restrictAvailable.trace trace)
  rw [restrictAvailable.trace_length] at count
  simp only [protocolRemaining] at count
  omega

/-- An empty intended history is before setup. -/
private theorem state_eq_none_of_length {state : setup.intendedProtocol.State}
    (trace : setup.intendedProtocol.Trace state) (empty : trace.length = 0) : state = none := by
  cases trace with
  | start => rfl
  | extend => simp [Trace.length] at empty

section CellLookup

variable [DecidableEq (CellTy Player L)]

/-- The value of a cell at a setup state; nothing before setup. -/
private def foundAt (name : VarId) (kind : CellTy Player L) (state : setup.ProtocolState) :
    Option (CellVal L kind) :=
  state.bind fun point => ProtocolState.cell? setup.program point name kind

private theorem foundAt_step {before after : setup.ProtocolState}
    {joint : Player → Option (OwnAction Player L)}
    (reached : after ∈ (setup.protocolStep before joint).support) {name : VarId}
    {kind : CellTy Player L} {value : CellVal L kind}
    (found : setup.foundAt name kind before = some value) :
    setup.foundAt name kind after = some value := by
  cases before with
  | none => simp [foundAt] at found
  | some point =>
      simp only [protocolStep, PMF.support_map, Set.mem_image] at reached
      obtain ⟨_, inner, rfl⟩ := reached
      exact ProtocolState.cell?_step setup.program inner found

/-- Cells found at a prefix are found, with the same values, at its extensions. -/
private theorem foundAt_prefix {state target : setup.intendedProtocol.State}
    {prefixTrace : setup.intendedProtocol.Trace state}
    {trace : setup.intendedProtocol.Trace target} (isPrefix : TracePrefix prefixTrace trace)
    (name : VarId) (kind : CellTy Player L) {value : CellVal L kind}
    (found : setup.foundAt name kind state = some value) :
    setup.foundAt name kind target = some value := by
  induction isPrefix with
  | refl => exact found
  | extend _ joint _ realized ih => exact setup.foundAt_step (joint := joint) realized ih

/-- **Prefixes of intended histories differ by the swap between their ends.**
For two intended histories with equal length and public default record, ending
at p and q, every prefix of
the first has a prefix of the second of the same length, and the swap between
p and q maps the state of the first prefix to the state of the second. -/
theorem intended_prefix_between {first second : setup.intendedProtocol.History}
    {p q : SourceProgram.ProtocolState setup.program} (firstState : first.state = some p)
    (secondState : second.state = some q)
    (sameLength : first.trace.length = second.trace.length)
    (sameDefaults : ProtocolState.defaults setup.program p =
      ProtocolState.defaults setup.program q)
    {state : setup.ProtocolState} (prefixTrace : setup.intendedProtocol.Trace state)
    (isPrefix : TracePrefix prefixTrace first.trace) :
    ∃ (state' : setup.ProtocolState) (prefixTrace' : setup.intendedProtocol.Trace state'),
      TracePrefix prefixTrace' second.trace ∧
      prefixTrace'.length = prefixTrace.length ∧
      state' = Option.map ((CellSwap.between setup.program p q).protocolState setup.program)
        state := by
  obtain ⟨state', prefixTrace', isPrefix', sameLength'⟩ :=
    exists_tracePrefix_of_le second.trace (isPrefix.length_le.trans sameLength.le)
  refine ⟨state', prefixTrace', isPrefix', sameLength', ?_⟩
  have finalDefaults : setup.protocolDefaults first.state =
      setup.protocolDefaults second.state := by
    rw [firstState, secondState]
    exact sameDefaults
  have prefixDefaults := congrArg
    (DefaultHistory.back^[first.trace.length - prefixTrace.length]) finalDefaults
  rw [setup.protocolDefaults_prefix isPrefix] at prefixDefaults
  have distance : first.trace.length - prefixTrace.length =
      second.trace.length - prefixTrace'.length := by rw [sameLength, sameLength']
  rw [distance, setup.protocolDefaults_prefix isPrefix'] at prefixDefaults
  cases state with
  | none =>
      exact setup.state_eq_none_of_length prefixTrace'
        (sameLength'.trans (setup.trace_length_eq_zero prefixTrace rfl))
  | some a =>
      cases state' with
      | none =>
          cases setup.state_eq_none_of_length prefixTrace
            (sameLength'.symm.trans (setup.trace_length_eq_zero prefixTrace' rfl))
      | some b =>
          refine congrArg some (setup.intended_eq_swap_of_defaults (first := ⟨some a, prefixTrace⟩)
            (second := ⟨some b, prefixTrace'⟩) rfl rfl sameLength'.symm prefixDefaults _
            fun name kind value found => ?_)
          have swapped := setup.intended_eq_between_of_defaults (first := ⟨some a, prefixTrace⟩)
            (second := ⟨some b, prefixTrace'⟩) rfl rfl sameLength'.symm prefixDefaults
          have atSecond : ProtocolState.cell? setup.program b name kind =
              some ((CellSwap.between setup.program a b).cell name kind value) := by
            have lookup := congrArg
              (fun point => ProtocolState.cell? setup.program point name kind) swapped
            rw [ProtocolState.cell?_swap, found] at lookup
            exact lookup
          have atFirstEnd := setup.foundAt_prefix isPrefix name kind found
          have atSecondEnd := setup.foundAt_prefix isPrefix' name kind atSecond
          rw [firstState] at atFirstEnd
          rw [secondState] at atSecondEnd
          change ProtocolState.cell? setup.program p name kind = some value at atFirstEnd
          change ProtocolState.cell? setup.program q name kind = _ at atSecondEnd
          change swapFound (ProtocolState.cell? setup.program p name kind)
              (ProtocolState.cell? setup.program q name kind) value =
            swapFound (ProtocolState.cell? setup.program a name kind)
              (ProtocolState.cell? setup.program b name kind) value
          rw [atFirstEnd, atSecondEnd, found, atSecond]

end CellLookup

/-- **The acting choice of a realized intended step.** Let a realized step of the
intended game and the step of one choice for everybody reach the same target,
the choice being addressed to the acting site under some commitment interface.
Then every acting player plays that choice. -/
theorem intended_joint_eq_of_choice {state target : setup.ProtocolState}
    {joint : Player → Option (OwnAction Player L)}
    (legal : setup.intendedProtocol.Legal state joint)
    (realized : target ∈ (setup.intendedProtocol.step state ⟨joint, legal⟩).support)
    {admission : CommitmentInterface setup.program} {choice : Option (OwnAction Player L)}
    (addressed : ∀ who action, choice = some action →
      (setup.executionProtocol admission).active state who →
        action ∈ (setup.executionProtocol admission).available state who)
    (choiceRealized : target ∈ (setup.protocolStep state fun _ => choice).support)
    (who : Player) (acting : (setup.executionProtocol admission).active state who) :
    joint who = choice := by
  cases state with
  | none => exact acting.elim
  | some point =>
      simp only [protocolStep, PMF.support_map, Set.mem_image] at choiceRealized
      change target ∈ ((ProtocolState.step setup.program point joint).map some).support
        at realized
      simp only [PMF.support_map, Set.mem_image] at realized
      obtain ⟨_, inner, rfl⟩ := realized
      obtain ⟨_, choiceInner, same⟩ := choiceRealized
      cases Option.some.inj same
      refine ProtocolState.intended_actor_eq_choice setup.program admission (fun who => ?_)
        addressed inner choiceInner who acting
      have member := legal.2 who
      revert member
      cases joint who <;> exact id

end Setup

end Vegas.SourceProgram
