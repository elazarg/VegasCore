/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CellSwap
import Vegas.Source.IntendedGame
import Vegas.Source.DefaultControl
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Intended states at a program point differ by a cell swap

In a context with distinct names, looking a cell up by name and kind
(`Vegas.SourceProgram.State.cell?`) finds the value at the unique witness of
that cell (`Vegas.SourceProgram.State.cell?_eq_of_hasVar`).

Two states of the intended game reached in the same number of steps with the
same complete public default record carry the same static metadata and matching
own action lists. The swap between their typed cells therefore maps the complete
configurations (`Vegas.SourceProgram.Setup.intended_eq_between_of_defaults`).
The same holds for any swap agreeing on their found values
(`Vegas.SourceProgram.Setup.intended_eq_swap_of_defaults`). Equal observations
supply both equal program positions and the public default record, giving the
observation specialization without additional hypotheses
(`Vegas.SourceProgram.Setup.intended_eq_between_of_observe`).
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section CellLookup

variable [DecidableEq (CellTy Player L)]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Looking up the newest cell by its own name and kind finds its value. -/
theorem State.cell?_cons_self {Γ : SourceCtx Player L} {x : VarId}
    {kind : CellTy Player L} (value : CellVal L kind) (cells : State L Γ) :
    State.cell? (Env.cons (x := x) value cells : State L ((x, kind) :: Γ)) x kind =
      some value := by
  rw [State.cell?.eq_2]
  split_ifs with same
  · rfl
  · exact (same ⟨rfl, rfl⟩).elim

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Adding a cell under another name does not change a lookup. -/
theorem State.cell?_cons_of_ne {Γ : SourceCtx Player L} {x name : VarId}
    {head : CellTy Player L} (value : CellVal L head) (cells : State L Γ) (other : x ≠ name)
    (kind : CellTy Player L) :
    State.cell? (Env.cons (x := x) value cells : State L ((x, head) :: Γ)) name kind =
      State.cell? cells name kind := by
  rw [State.cell?.eq_2]
  split_ifs with same
  · exact (other same.1).elim
  · rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A found cell is named in the context. -/
theorem State.mem_of_cell?_eq_some {name : VarId} {kind : CellTy Player L}
    {value : CellVal L kind} :
    ∀ {Γ : SourceCtx Player L} {cells : State L Γ},
      State.cell? cells name kind = some value → name ∈ Γ.map Prod.fst
  | [], _, found => by simp [State.cell?] at found
  | (current, currentKind) :: Γ, cells, found => by
      unfold State.cell? at found
      split_ifs at found with same
      · simp [same.1]
      · exact List.mem_cons_of_mem _ (State.mem_of_cell?_eq_some found)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- **Lookup at distinct names.** When the names of the context are distinct,
the lookup of a cell by name and kind finds its value. -/
theorem State.cell?_eq_of_hasVar {Γ : SourceCtx Player L} {name : VarId}
    {kind : CellTy Player L} (source : HasVar Γ name kind) :
    (Γ.map Prod.fst).Nodup → ∀ cells : State L Γ,
      State.cell? cells name kind = some (cells name kind source) := by
  induction source with
  | here =>
      intro _ cells
      exact State.cell?_cons_self _ _
  | @there Γ name other kind otherKind source ih =>
      intro distinct cells
      obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp distinct
      have different : other ≠ name := fun same => fresh (same ▸ source.mem_map_fst)
      rw [State.cell?.eq_2]
      split_ifs with same
      · exact (different same.1).elim
      · exact ih distinct _

end CellLookup

section Matching

variable [DecidableEq (CellTy Player L)]

/-- Two recorded own actions of the same shape: commitments to the same cell
whose choices are that cell's current values, or the same reveal. -/
private inductive ActionMatched {Γ : SourceCtx Player L} (first second : State L Γ) :
    OwnAction Player L → OwnAction Player L → Prop
  | commit {owner : Player} {name : VarId} {payload : L.Ty}
      {firstChoice secondChoice : PublicationResult (L.Val payload)}
      (firstCell : State.cell? first name (.commitment owner payload) = some firstChoice)
      (secondCell : State.cell? second name (.commitment owner payload) = some secondChoice) :
      ActionMatched first second (.commit owner name payload (some firstChoice))
        (.commit owner name payload (some secondChoice))
  | reveal (owner : Player) (name : VarId) (disclose : Bool) :
      ActionMatched first second (.reveal owner name disclose) (.reveal owner name disclose)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem ActionMatched.weaken {Γ : SourceCtx Player L} {x : VarId}
    {head : CellTy Player L} (fresh : x ∉ Γ.map Prod.fst) {first second : State L Γ}
    (firstHead secondHead : CellVal L head) {firstAction secondAction : OwnAction Player L}
    (matched : ActionMatched first second firstAction secondAction) :
    ActionMatched (Env.cons (x := x) firstHead first : State L ((x, head) :: Γ))
      (Env.cons secondHead second) firstAction secondAction := by
  cases matched with
  | commit firstCell secondCell =>
      have other := fun same : x = _ => fresh (same ▸ State.mem_of_cell?_eq_some firstCell)
      exact .commit (by rw [State.cell?_cons_of_ne _ _ other, firstCell])
        (by rw [State.cell?_cons_of_ne _ _ other, secondCell])
  | reveal owner name disclose => exact .reveal owner name disclose

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem ActionMatched.swap_action {Γ : SourceCtx Player L} {first second : State L Γ}
    (swap : CellSwap Player L)
    (cells : ∀ name kind value, State.cell? first name kind = some value →
      swap.cell name kind value =
        swapFound (State.cell? first name kind) (State.cell? second name kind) value)
    {firstAction secondAction : OwnAction Player L}
    (matched : ActionMatched first second firstAction secondAction) :
    swap.action firstAction = secondAction := by
  cases matched with
  | commit firstCell secondCell =>
      simp only [CellSwap.action, Option.map_some, cells _ _ _ firstCell,
        firstCell, secondCell, swapFound,
        Equiv.swap_apply_left]
  | reveal => rfl

/-- Two configurations with equal static metadata and public default records,
whose action lists match entry by entry. -/
private def ConfigMatched {Γ : SourceCtx Player L} (first second : Config Player L Γ) : Prop :=
  first.registry = second.registry ∧
    @Config.revelations Player L Γ first = @Config.revelations Player L Γ second ∧
    first.defaults = second.defaults ∧
    ∀ who, List.Forall₂ (ActionMatched first.state second.state)
      (first.history who) (second.history who)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- At distinct names, a swap transposing the cells of two matched
configurations maps the first to the second. -/
private theorem ConfigMatched.swap_config {Γ : SourceCtx Player L}
    (distinct : (Γ.map Prod.fst).Nodup) {first second : Config Player L Γ}
    (swap : CellSwap Player L)
    (cells : ∀ name kind value, State.cell? first.state name kind = some value →
      swap.cell name kind value =
        swapFound (State.cell? first.state name kind) (State.cell? second.state name kind)
          value)
    (matched : ConfigMatched first second) : swap.config first = second := by
  obtain ⟨registry, revelations, defaults, histories⟩ := matched
  have stateEq : swap.state first.state = second.state := by
    funext name kind source
    have found := State.cell?_eq_of_hasVar source distinct first.state
    simp only [CellSwap.state, cells _ _ _ found, found,
      State.cell?_eq_of_hasVar source distinct second.state, swapFound, Equiv.swap_apply_left]
  have historyEq : swap.history first.history = second.history := by
    funext who
    simp only [CellSwap.history]
    have lists := histories who
    generalize first.history who = firstList at lists ⊢
    generalize second.history who = secondList at lists ⊢
    induction lists with
    | nil => rfl
    | cons head _ tail => rw [List.map_cons, head.swap_action swap cells, tail]
  obtain ⟨firstState, firstRegistry, firstRevelations, firstHistory, firstDefaults⟩ := first
  obtain ⟨secondState, secondRegistry, secondRevelations, secondHistory, secondDefaults⟩ := second
  simp only [CellSwap.config] at stateEq historyEq registry revelations defaults ⊢
  rw [stateEq, historyEq, registry, revelations, defaults]

/-- Two states at the same program point whose configurations there match. -/
private def Matched : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program →
      Prop
  | _, _, .ret _, first, second => ConfigMatched first second
  | _, _, .sample _ _ _ next, first, second =>
      Sum.elim (fun first => Sum.elim (fun second => ConfigMatched first second)
          (fun _ => False) second)
        (fun first => Sum.elim (fun _ => False) (fun second => Matched next first second) second)
        first
  | _, _, .commit _ _ _ _ next, first, second =>
      Sum.elim (fun first => Sum.elim (fun second => ConfigMatched first second)
          (fun _ => False) second)
        (fun first => Sum.elim (fun _ => False) (fun second => Matched next first second) second)
        first
  | _, _, .reveal _ _ _ _ _ _ next, first, second =>
      Sum.elim (fun first => Sum.elim (fun second => ConfigMatched first second)
          (fun _ => False) second)
        (fun first => Sum.elim (fun _ => False) (fun second => Matched next first second) second)
        first

private theorem matched_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) {first second : Config Player L Γ}
    (matched : ConfigMatched first second) :
    Matched program (ProtocolState.entry program first) (ProtocolState.entry program second) := by
  cases program <;> exact matched

/-- At distinct names, a swap transposing the cells of two matched states maps
the first to the second. -/
private theorem matched_swap : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (Γ.map Prod.fst).Nodup →
    (swap : CellSwap Player L) → {first second : ProtocolState program} →
    (∀ name kind value, ProtocolState.cell? program first name kind = some value →
      swap.cell name kind value = swapFound (ProtocolState.cell? program first name kind)
        (ProtocolState.cell? program second name kind) value) →
    Matched program first second → second = swap.protocolState program first
  | _, _, .ret _, distinct, swap, _, _, cells, matched =>
      (ConfigMatched.swap_config distinct swap cells matched).symm
  | _, _, .sample _ fresh _ next, distinct, swap, first, second, cells, matched => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => exact matched.elim
          | inl second =>
              exact congrArg Sum.inl (ConfigMatched.swap_config distinct swap cells matched).symm
      | inr first =>
          cases second with
          | inl _ => exact matched.elim
          | inr second =>
              exact congrArg Sum.inr (matched_swap next (List.nodup_cons.mpr ⟨fresh, distinct⟩)
                swap cells matched)
  | _, _, .commit _ _ fresh _ next, distinct, swap, first, second, cells, matched => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => exact matched.elim
          | inl second =>
              exact congrArg Sum.inl (ConfigMatched.swap_config distinct swap cells matched).symm
      | inr first =>
          cases second with
          | inl _ => exact matched.elim
          | inr second =>
              exact congrArg Sum.inr (matched_swap next (List.nodup_cons.mpr ⟨fresh, distinct⟩)
                swap cells matched)
  | _, _, .reveal _ _ _ fresh _ _ next, distinct, swap, first, second, cells, matched => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => exact matched.elim
          | inl second =>
              exact congrArg Sum.inl (ConfigMatched.swap_config distinct swap cells matched).symm
      | inr first =>
          cases second with
          | inl _ => exact matched.elim
          | inr second =>
              exact congrArg Sum.inr (matched_swap next (List.nodup_cons.mpr ⟨fresh, distinct⟩)
                swap cells matched)

omit [DecidableEq (CellTy Player L)] in
private theorem binding_of_intendedMenu {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    {config : Config Player L Γ} {joint : Player → Option (OwnAction Player L)}
    (active : owner ∉ config.defaulted)
    (legal : ProtocolView.intendedMenu owner (.commit name owner fresh guard next)
      (ProtocolState.observe owner (.commit name owner fresh guard next) (Sum.inl config))
      (joint owner)) :
    ∃ value, OwnAction.binding owner name payload (joint owner) = some (.success value) := by
  cases chosen : joint owner with
  | none =>
      rw [chosen] at legal
      exact (legal (by simp [ProtocolView.actor, ProtocolState.observe, active])).elim
  | some action =>
      rw [chosen] at legal
      obtain ⟨_, value, _, rfl⟩ := legal
      exact ⟨value, OwnAction.binding_commit ..⟩

omit [DecidableEq (CellTy Player L)] in
/-- An active owner's intended disclosure opens. -/
private theorem disclosure_of_intendedMenu {Γ : SourceCtx Player L} {O : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst} {source : HasVar Γ name (.commitment owner payload)}
    {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    {config : Config Player L Γ} {joint : Player → Option (OwnAction Player L)}
    (active : owner ∉ config.defaulted)
    (legal : ProtocolView.intendedMenu owner
      (.reveal published owner name fresh source unresolved next)
      (ProtocolState.observe owner (.reveal published owner name fresh source unresolved next)
        (Sum.inl config)) (joint owner)) :
    joint owner = some (.reveal owner name true) := by
  cases chosen : joint owner with
  | none =>
      rw [chosen] at legal
      exact (legal (by simp [ProtocolView.actor, ProtocolState.observe, active])).elim
  | some action =>
      rw [chosen] at legal
      exact congrArg some legal.2

/-- Intended steps preserve action matching when their resulting public records agree. -/
private theorem matched_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    {firstBefore secondBefore firstAfter secondAfter : ProtocolState program} →
    {firstJoint secondJoint : Player → Option (OwnAction Player L)} →
    Matched program firstBefore secondBefore →
    (∀ who, ProtocolView.intendedMenu who program
      (ProtocolState.observe who program firstBefore) (firstJoint who)) →
    (∀ who, ProtocolView.intendedMenu who program
      (ProtocolState.observe who program secondBefore) (secondJoint who)) →
    firstAfter ∈ (ProtocolState.step program firstBefore firstJoint).support →
    secondAfter ∈ (ProtocolState.step program secondBefore secondJoint).support →
    ProtocolState.defaults program firstAfter = ProtocolState.defaults program secondAfter →
    Matched program firstAfter secondAfter
  | _, _, .ret _, _, _, _, _, _, _, matched, _, _, firstReached, secondReached, _ => by
      rw [(PMF.mem_support_pure_iff _ _).mp firstReached,
        (PMF.mem_support_pure_iff _ _).mp secondReached]
      exact matched
  | _, _, .sample _ fresh _ next, firstBefore, secondBefore, _, _, _, _, matched,
      firstLegal, secondLegal, firstReached, secondReached, finalDefaults => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact matched.elim
          | inl second =>
              obtain ⟨firstValue, _, rfl⟩ := PMF.support_map .. ▸ firstReached
              obtain ⟨secondValue, _, rfl⟩ := PMF.support_map .. ▸ secondReached
              obtain ⟨registry, revelations, _, histories⟩ := matched
              exact matched_entry next ⟨by simp only [sampleSuccessor, registry],
                by simp only [sampleSuccessor, revelations],
                by simpa only [ProtocolState.defaults, Sum.elim_inr,
                  ProtocolState.defaults_entry] using finalDefaults,
                fun who => (histories who).imp fun _ _ =>
                  ActionMatched.weaken fresh (head := .publicData _) firstValue secondValue⟩
      | inr first =>
          cases secondBefore with
          | inl _ => exact matched.elim
          | inr second =>
              obtain ⟨_, firstInner, rfl⟩ := PMF.support_map .. ▸ firstReached
              obtain ⟨_, secondInner, rfl⟩ := PMF.support_map .. ▸ secondReached
              exact matched_step next matched firstLegal secondLegal firstInner secondInner
                finalDefaults
  | _, _, .commit (payload := payload) name owner fresh guard next, firstBefore, secondBefore,
      _, _, firstJoint, secondJoint, matched, firstLegal, secondLegal, firstReached,
      secondReached, finalDefaults => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact matched.elim
          | inl second =>
              have firstEq := (PMF.mem_support_pure_iff _ _).mp firstReached
              have secondEq := (PMF.mem_support_pure_iff _ _).mp secondReached
              subst firstEq secondEq
              obtain ⟨registry, revelations, defaults, histories⟩ := matched
              have status : first.defaulted = second.defaulted :=
                congrArg DefaultHistory.defaulted defaults
              refine matched_entry next ⟨by simp only [commitSuccessor, registry],
                by simp only [commitSuccessor, revelations],
                by simpa only [ProtocolState.defaults, Sum.elim_inr,
                  ProtocolState.defaults_entry] using finalDefaults, fun who => ?_⟩
              by_cases inactive : owner ∈ first.defaulted
              · have secondInactive : owner ∈ second.defaulted := status ▸ inactive
                simp only [commitSuccessor, inactive, secondInactive, ite_true]
                exact (histories who).imp fun _ _ => ActionMatched.weaken fresh _ _
              · have secondActive : owner ∉ second.defaulted := status ▸ inactive
                obtain ⟨firstValue, firstChoice⟩ :=
                  binding_of_intendedMenu inactive (firstLegal owner)
                obtain ⟨secondValue, secondChoice⟩ :=
                  binding_of_intendedMenu secondActive (secondLegal owner)
                simp only [commitSuccessor, inactive, secondActive, ite_false,
                  firstChoice, secondChoice, Option.getD_some]
                have weakened := fun player => (histories player).imp fun _ _ =>
                  ActionMatched.weaken fresh (head := .commitment owner payload)
                    (.success firstValue) (.success secondValue)
                by_cases mover : who = owner
                · subst who
                  simp only [Function.update_self]
                  exact List.rel_append (weakened owner)
                    (.cons (.commit (State.cell?_cons_self _ _) (State.cell?_cons_self _ _)) .nil)
                · simp only [Function.update_of_ne mover]
                  exact weakened who
      | inr first =>
          cases secondBefore with
          | inl _ => exact matched.elim
          | inr second =>
              obtain ⟨_, firstInner, rfl⟩ := PMF.support_map .. ▸ firstReached
              obtain ⟨_, secondInner, rfl⟩ := PMF.support_map .. ▸ secondReached
              exact matched_step next matched firstLegal secondLegal firstInner secondInner
                finalDefaults
  | _, _, .reveal published owner name fresh source _ next, firstBefore, secondBefore, _, _,
      firstJoint, secondJoint, matched, firstLegal, secondLegal, firstReached,
      secondReached, finalDefaults => by
      cases firstBefore with
      | inl first =>
          cases secondBefore with
          | inr _ => exact matched.elim
          | inl second =>
              have firstEq := (PMF.mem_support_pure_iff _ _).mp firstReached
              have secondEq := (PMF.mem_support_pure_iff _ _).mp secondReached
              subst firstEq secondEq
              obtain ⟨registry, revelations, defaults, histories⟩ := matched
              have status : first.defaulted = second.defaulted :=
                congrArg DefaultHistory.defaulted defaults
              refine matched_entry next ⟨by simp only [revealSuccessor, registry],
                by simp only [revealSuccessor, revelations],
                by simpa only [ProtocolState.defaults, Sum.elim_inr,
                  ProtocolState.defaults_entry] using finalDefaults, fun who => ?_⟩
              by_cases inactive : owner ∈ first.defaulted
              · have secondInactive : owner ∈ second.defaulted := status ▸ inactive
                simp only [revealSuccessor, inactive, secondInactive, ite_true]
                exact (histories who).imp fun _ _ => ActionMatched.weaken fresh _ _
              · have secondActive : owner ∉ second.defaulted := status ▸ inactive
                have firstChoice := disclosure_of_intendedMenu inactive (firstLegal owner)
                have secondChoice := disclosure_of_intendedMenu secondActive (secondLegal owner)
                simp only [revealSuccessor, inactive, secondActive, ite_false,
                  firstChoice, secondChoice, OwnAction.disclosure]
                by_cases mover : who = owner
                · subst who
                  simp only [Function.update_self]
                  exact List.rel_append
                    ((histories owner).imp fun _ _ => ActionMatched.weaken fresh _ _)
                    (.cons (.reveal owner name _) .nil)
                · simp only [Function.update_of_ne mover]
                  exact (histories who).imp fun _ _ => ActionMatched.weaken fresh _ _
      | inr first =>
          cases secondBefore with
          | inl _ => exact matched.elim
          | inr second =>
              obtain ⟨_, firstInner, rfl⟩ := PMF.support_map .. ▸ firstReached
              obtain ⟨_, secondInner, rfl⟩ := PMF.support_map .. ▸ secondReached
              exact matched_step next matched firstLegal secondLegal firstInner secondInner
                finalDefaults

end Matching

namespace ProtocolState

/-- Equal observations of one player are at the same program point, so the
same number of instructions remains. -/
theorem remaining_eq_of_observe (who : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    {first second : ProtocolState program} →
    observe who program first = observe who program second →
    remaining program first = remaining program second
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second <;> simp only [observe, Sum.elim_inl, Sum.elim_inr,
        reduceCtorEq, Sum.inr.injEq] at same
      · rfl
      · exact remaining_eq_of_observe who next same
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second <;> simp only [observe, Sum.elim_inl, Sum.elim_inr,
        reduceCtorEq, Sum.inr.injEq] at same
      · rfl
      · exact remaining_eq_of_observe who next same
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second <;> simp only [observe, Sum.elim_inl, Sum.elim_inr,
        reduceCtorEq, Sum.inr.injEq] at same
      · rfl
      · exact remaining_eq_of_observe who next same

end ProtocolState

namespace Setup

/-- A history prefix retains exactly the older part of the public default record. -/
theorem protocolDefaults_prefix (setup : Setup (Player := Player) (L := L))
    {state target : setup.intendedProtocol.State}
    {prefixTrace : setup.intendedProtocol.Trace state}
    {trace : setup.intendedProtocol.Trace target}
    (isPrefix : GameTheory.Protocol.ExecutionProtocol.TracePrefix prefixTrace trace) :
    (DefaultHistory.back^[trace.length - prefixTrace.length]) (setup.protocolDefaults target) =
      setup.protocolDefaults state := by
  induction isPrefix with
  | refl => simp only [Nat.sub_self, Function.iterate_zero, id_eq]
  | @extend before after prior earlier joint legal realized ih =>
      have bounded := earlier.length_le
      have backwards := setup.protocolDefaults_back_step before after joint legal.1 realized
      have distance : (prior.extend joint legal realized).length - prefixTrace.length =
          (prior.length - prefixTrace.length) + 1 := by
        simp only [GameTheory.Protocol.ExecutionProtocol.Trace.length]
        omega
      rw [distance, Function.iterate_succ_apply, backwards]
      exact ih


section Matching

variable [DecidableEq (CellTy Player L)]

/-- Matched setup states: both before the draw, or matched source states. -/
private def SetupMatched (setup : Setup (Player := Player) (L := L)) :
    setup.ProtocolState → setup.ProtocolState → Prop
  | none, none => True
  | some first, some second => Matched setup.program first second
  | _, _ => False

omit [DecidableEq (CellTy Player L)] in
private theorem intendedMenu_of_legal (setup : Setup (Player := Player) (L := L))
    {state : SourceProgram.ProtocolState setup.program}
    {joint : Player → Option (OwnAction Player L)}
    (legal : setup.intendedProtocol.Legal (some state) joint) (who : Player) :
    ProtocolView.intendedMenu who setup.program
      (ProtocolState.observe who setup.program state) (joint who) := by
  have member := legal.2 who
  revert member
  cases joint who <;> exact id

private theorem setupMatched_step (setup : Setup (Player := Player) (L := L))
    {firstBefore secondBefore firstAfter secondAfter : setup.ProtocolState}
    {firstJoint secondJoint : Player → Option (OwnAction Player L)}
    (matched : setup.SetupMatched firstBefore secondBefore)
    (firstLegal : setup.intendedProtocol.Legal firstBefore firstJoint)
    (secondLegal : setup.intendedProtocol.Legal secondBefore secondJoint)
    (firstReached : firstAfter ∈ (setup.protocolStep firstBefore firstJoint).support)
    (secondReached : secondAfter ∈ (setup.protocolStep secondBefore secondJoint).support)
    (finalDefaults : setup.protocolDefaults firstAfter = setup.protocolDefaults secondAfter) :
    setup.SetupMatched firstAfter secondAfter := by
  cases firstBefore with
  | none =>
      cases secondBefore with
      | some _ => exact matched.elim
      | none =>
          simp only [protocolStep, PMF.support_map, Set.mem_image] at firstReached secondReached
          obtain ⟨_, _, rfl⟩ := firstReached
          obtain ⟨_, _, rfl⟩ := secondReached
          exact matched_entry setup.program ⟨rfl, rfl, rfl, fun _ => .nil⟩
  | some first =>
      cases secondBefore with
      | none => exact matched.elim
      | some second =>
          simp only [protocolStep, PMF.support_map, Set.mem_image] at firstReached secondReached
          obtain ⟨_, firstInner, rfl⟩ := firstReached
          obtain ⟨_, secondInner, rfl⟩ := secondReached
          exact matched_step setup.program matched (setup.intendedMenu_of_legal firstLegal)
            (setup.intendedMenu_of_legal secondLegal) firstInner secondInner finalDefaults

/-- Intended histories of equal length reach matched states. -/
private theorem setupMatched_of_length (setup : Setup (Player := Player) (L := L)) :
    ∀ {first second : setup.ProtocolState}
      (firstTrace : setup.intendedProtocol.Trace first)
      (secondTrace : setup.intendedProtocol.Trace second),
      firstTrace.length = secondTrace.length →
      setup.protocolDefaults first = setup.protocolDefaults second → setup.SetupMatched first second
  | _, _, .start, .start, _, _ => trivial
  | _, _, .start, .extend _ _ _ _, same, _ => by simp [Trace.length] at same
  | _, _, .extend _ _ _ _, .start, same, _ => by simp [Trace.length] at same
  | _, _, .extend firstPrior firstJoint firstLegal firstReached,
      .extend secondPrior secondJoint secondLegal secondReached, same, finalDefaults => by
      simp only [Trace.length, Nat.add_right_cancel_iff] at same
      have priorDefaults := congrArg DefaultHistory.back finalDefaults
      rw [setup.protocolDefaults_back_step _ _ firstJoint firstLegal.1 firstReached,
        setup.protocolDefaults_back_step _ _ secondJoint secondLegal.1 secondReached]
        at priorDefaults
      exact setup.setupMatched_step
        (setup.setupMatched_of_length firstPrior secondPrior same priorDefaults)
        firstLegal secondLegal firstReached secondReached finalDefaults

/-- At equal history lengths and public default records, any swap transposing
the found typed values maps one complete intended state to the other. -/
theorem intended_eq_swap_of_defaults (setup : Setup (Player := Player) (L := L))
    {first second : setup.intendedProtocol.History}
    {p q : SourceProgram.ProtocolState setup.program}
    (firstState : first.state = some p) (secondState : second.state = some q)
    (sameLength : first.trace.length = second.trace.length)
    (sameDefaults : ProtocolState.defaults setup.program p =
      ProtocolState.defaults setup.program q) (swap : CellSwap Player L)
    (cells : ∀ name kind value, ProtocolState.cell? setup.program p name kind = some value →
      swap.cell name kind value = swapFound (ProtocolState.cell? setup.program p name kind)
        (ProtocolState.cell? setup.program q name kind) value) :
    q = swap.protocolState setup.program p := by
  have defaults : setup.protocolDefaults first.state = setup.protocolDefaults second.state := by
    rw [firstState, secondState]
    exact sameDefaults
  have matched := setup.setupMatched_of_length first.trace second.trace sameLength defaults
  rw [firstState, secondState] at matched
  exact matched_swap setup.program setup.namesNodup swap cells matched

/-- At equal history lengths and public default records, the swap between
intended states maps their complete configurations, including actual action recall. -/
theorem intended_eq_between_of_defaults (setup : Setup (Player := Player) (L := L))
    {first second : setup.intendedProtocol.History}
    {p q : SourceProgram.ProtocolState setup.program}
    (firstState : first.state = some p) (secondState : second.state = some q)
    (sameLength : first.trace.length = second.trace.length)
    (sameDefaults : ProtocolState.defaults setup.program p =
      ProtocolState.defaults setup.program q) :
    q = (CellSwap.between setup.program p q).protocolState setup.program p :=
  setup.intended_eq_swap_of_defaults firstState secondState sameLength sameDefaults _
    fun _ _ _ _ => rfl

end Matching

/-- **Equal observations, equal history lengths.** Two intended histories at
states one player observes alike have the same length. -/
theorem intendedProtocol_length_eq_of_observe (setup : Setup (Player := Player) (L := L))
    {first second : setup.intendedProtocol.History}
    {p q : SourceProgram.ProtocolState setup.program}
    (firstState : first.state = some p) (secondState : second.state = some q) (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q) :
    first.trace.length = second.trace.length := by
  obtain ⟨firstEnd, firstTrace⟩ := first
  obtain ⟨secondEnd, secondTrace⟩ := second
  change firstEnd = some p at firstState
  change secondEnd = some q at secondState
  subst firstState secondState
  have firstCount := setup.protocol_history_length _ (restrictAvailable.trace firstTrace)
  have secondCount := setup.protocol_history_length _ (restrictAvailable.trace secondTrace)
  rw [restrictAvailable.trace_length] at firstCount secondCount
  have sameRemaining := ProtocolState.remaining_eq_of_observe who setup.program sameView
  simp only [protocolRemaining] at firstCount secondCount
  change firstTrace.length = secondTrace.length
  omega

/-- **Intended states one player cannot tell apart differ by the swap between
them.** -/
theorem intended_eq_between_of_observe [DecidableEq (CellTy Player L)]
    (setup : Setup (Player := Player) (L := L))
    {first second : setup.intendedProtocol.History}
    {p q : SourceProgram.ProtocolState setup.program}
    (firstState : first.state = some p) (secondState : second.state = some q) (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q) :
    q = (CellSwap.between setup.program p q).protocolState setup.program p := by
  apply setup.intended_eq_between_of_defaults firstState secondState
    (setup.intendedProtocol_length_eq_of_observe firstState secondState who sameView)
  have recorded := congrArg (ProtocolView.defaults who setup.program) sameView
  simpa only [ProtocolState.defaults_observe] using recorded

end Setup

end Vegas.SourceProgram
