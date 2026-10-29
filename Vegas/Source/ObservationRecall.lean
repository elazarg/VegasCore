/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Protocol
import Vegas.Source.ProtocolTermination
import GameTheory.Math.Probability.ConditionalObservation

/-! # Recovering earlier source observations

Each instruction extends the immutable environment and public default record.
The prior public record determines whether an owned step recorded a real choice.
Dropping those extensions recovers the previous view at every supported history,
including automatic completion and histories of probability zero under a policy.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Undo one completed instruction. An own action is removed only when the
owner was active before that instruction; automatic completion chose no action. -/
def DecisionView.back {who : Player} {Γ : SourceCtx Player L} {x : VarId}
    {c : CellTy Player L} (ownStep : Bool) (view : DecisionView who ((x, c) :: Γ)) :
    DecisionView who Γ :=
  ⟨⟨fun _ cell member => view.observation.cells _ cell (.there member)⟩,
    view.defaults.back,
    if ownStep && decide (who ∉ view.defaults.back.defaulted) then
      view.history.dropLast else view.history⟩

omit [IExpr.ResultTypes L] in
@[simp] theorem sourceObserve_tail_cons {who : Player} {Γ : SourceCtx Player L} {x : VarId}
    {c : CellTy Player L} (value : CellVal L c) (state : State L Γ) :
    (SourceObservation.mk (fun name cell member =>
      (sourceObserve who (Env.cons (x := x) value state)).cells name cell (.there member))) =
      sourceObserve who state := by
  apply congrArg SourceObservation.mk
  funext name cell member
  cases cell <;> rfl

omit [IExpr.ResultTypes L] in
/-- Public-record rollback and conditional own-action rollback are exact,
without a freshness or reachability premise on the incoming record. -/
@[simp] theorem back_sourceObserve {who : Player} {Γ : SourceCtx Player L} {x : VarId}
    {c : CellTy Player L} (value : CellVal L c) (state : State L Γ)
    (defaults : DefaultHistory Player) (history : List (OwnAction Player L))
    (ownStep : Bool) (event : Option Player) (action : OwnAction Player L) :
    DecisionView.back ownStep
      ⟨sourceObserve who (Env.cons (x := x) value state), defaults.record event,
        if ownStep && decide (who ∉ defaults.defaulted) then history ++ [action] else history⟩ =
      ⟨sourceObserve who state, defaults, history⟩ := by
  by_cases active : who ∉ defaults.defaulted <;> cases ownStep <;>
    simp [DecisionView.back, active]

omit [IExpr.ResultTypes L] in
@[simp] theorem back_sample_view {Γ : SourceCtx Player L} {payload : L.Ty}
    (who : Player) (name : VarId) (config : Config Player L Γ) (value : L.Val payload) :
    ((sampleSuccessor name config value).view who).back false = config.view who := by
  simp [Config.view, sampleSuccessor, DecisionView.back]

omit [IExpr.ResultTypes L] in
@[simp] theorem back_commit_view {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} (who : Player) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : Config Player L Γ)
    (choice : Option (PublicationResult (L.Val payload))) :
    ((commitSuccessor name guard config choice).view who).back (decide (owner = who)) =
      config.view who := by
  by_cases own : owner = who
  · subst who
    by_cases inactive : owner ∈ config.defaults.defaulted <;>
      simp [Config.view, commitSuccessor, DecisionView.back, Config.defaulted, inactive]
  · by_cases inactive : owner ∈ config.defaults.defaulted
    · simp [Config.view, commitSuccessor, DecisionView.back, Config.defaulted, inactive, own]
    · simp [Config.view, commitSuccessor, DecisionView.back, Config.defaulted, inactive, own,
        Function.update_of_ne (Ne.symm own)]

omit [IExpr.ResultTypes L] in
@[simp] theorem back_reveal_view {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (who : Player) (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    ((revealSuccessor published selected config disclose).view who).back
        (decide (owner = who)) = config.view who := by
  by_cases own : owner = who
  · subst who
    by_cases inactive : owner ∈ config.defaults.defaulted <;>
      simp [Config.view, revealSuccessor, DecisionView.back, Config.defaulted, inactive]
  · by_cases inactive : owner ∈ config.defaults.defaulted
    · simp [Config.view, revealSuccessor, DecisionView.back, Config.defaulted, inactive, own]
    · simp [Config.view, revealSuccessor, DecisionView.back, Config.defaulted, inactive, own,
        Function.update_of_ne (Ne.symm own)]

omit [IExpr.ResultTypes L] in
/-- Later public default status does not erase an earlier decision view. -/
theorem reveal_view_reflects {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (who : Player) (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ) (leftChoice rightChoice : Bool)
    (same : (revealSuccessor published selected left leftChoice).view who =
      (revealSuccessor published selected right rightChoice).view who) :
    left.view who = right.view who := by
  have prior := congrArg (DecisionView.back (decide (owner = who))) same
  simpa only [back_reveal_view] using prior

namespace ProtocolView

/-- The entry view of a source suffix, read from any later observation in that
same suffix. No hidden configuration or remembered strategy is consulted. -/
def entryView (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → DecisionView who Γ
  | _, _, .ret _, view => view
  | _, _, .sample _ _ _ next, view =>
      view.elim id (fun later => (entryView who next later).back false)
  | _, _, .commit _ owner _ _ next, view =>
      view.elim id (fun later => (entryView who next later).back (decide (owner = who)))
  | _, _, .reveal _ owner _ _ _ _ next, view =>
      view.elim id (fun later => (entryView who next later).back (decide (owner = who)))

@[simp] theorem entryView_observe_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    entryView who program (ProtocolState.observe who program (ProtocolState.entry program config)) =
      config.view who := by
  cases program <;> rfl

/-- Any supported source step retains exactly the prior suffix-entry view.
The statement quantifies over all joint choices, independently of a strategy. -/
theorem entryView_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (before after : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) →
    after ∈ (ProtocolState.step program before joint).support →
    entryView who program (ProtocolState.observe who program after) =
      entryView who program (ProtocolState.observe who program before)
  | _, _, .ret _, before, after, _, supported => by
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst after
      rfl
  | _, _, .sample name fresh law next, before, after, joint, supported => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl,
            entryView, id_eq, entryView_observe_entry, back_sample_view]
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨after, reached, rfl⟩ := supported
          exact congrArg (DecisionView.back false)
            (entryView_step who next rest after joint reached)
  | _, _, .commit name owner fresh guard next, before, after, joint, supported => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.mem_support_pure_iff _ _] at supported
          subst after
          simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl,
            entryView, id_eq, entryView_observe_entry, back_commit_view]
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨after, reached, rfl⟩ := supported
          exact congrArg (DecisionView.back (decide (owner = who)))
            (entryView_step who next rest after joint reached)
  | _, _, .reveal published owner name fresh selected unresolved next,
      before, after, joint, supported => by
      cases before with
      | inl config =>
          simp only [ProtocolState.step, Sum.elim_inl, PMF.mem_support_pure_iff _ _] at supported
          subst after
          simp only [ProtocolState.observe, Sum.elim_inr, Sum.elim_inl,
            entryView, id_eq, entryView_observe_entry, back_reveal_view]
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
            Set.mem_image] at supported
          obtain ⟨after, reached, rfl⟩ := supported
          exact congrArg (DecisionView.back (decide (owner = who)))
            (entryView_step who next rest after joint reached)

/-- Position is already part of the source observation's sum constructor. -/
def position (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → Nat
  | _, _, .ret _, _ => 0
  | _, _, .sample _ _ _ next, view => view.elim (fun _ => 0) (fun v => position who next v + 1)
  | _, _, .commit _ _ _ _ next, view => view.elim (fun _ => 0) (fun v => position who next v + 1)
  | _, _, .reveal _ _ _ _ _ _ next, view =>
      view.elim (fun _ => 0) (fun v => position who next v + 1)

/-- Read an earlier observation at a specified source rank. The result keeps
the original protocol's program-point tag; a future rank returns `none`. -/
def atRank (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Nat →
      ProtocolView who program → Option (ProtocolView who program)
  | _, _, .ret _, 0, view => some view
  | _, _, .ret _, _ + 1, _ => none
  | _, _, .sample name fresh law next, 0, view =>
      some (.inl (entryView who (.sample name fresh law next) view))
  | _, _, .sample _ _ _ next, rank + 1, view =>
      view.elim (fun _ => none) (fun later => (atRank who next rank later).map Sum.inr)
  | _, _, .commit name owner fresh guard next, 0, view =>
      some (.inl (entryView who (.commit name owner fresh guard next) view))
  | _, _, .commit _ _ _ _ next, rank + 1, view =>
      view.elim (fun _ => none) (fun later => (atRank who next rank later).map Sum.inr)
  | _, _, .reveal published owner name fresh selected unresolved next, 0, view =>
      some (.inl (entryView who (.reveal published owner name fresh selected unresolved next) view))
  | _, _, .reveal _ _ _ _ _ _ next, rank + 1, view =>
      view.elim (fun _ => none) (fun later => (atRank who next rank later).map Sum.inr)

@[simp] theorem atRank_position (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
    atRank who program (position who program view) view = some view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view with
      | inl _ => rfl
      | inr later => simp only [position, Sum.elim_inr, atRank,
          atRank_position who next later, Option.map_some]
  | _, _, .commit _ _ _ _ next, view => by
      cases view with
      | inl _ => rfl
      | inr later => simp only [position, Sum.elim_inr, atRank,
          atRank_position who next later, Option.map_some]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view with
      | inl _ => rfl
      | inr later => simp only [position, Sum.elim_inr, atRank,
          atRank_position who next later, Option.map_some]

theorem position_add_remaining (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    position who program (ProtocolState.observe who program state) +
      ProtocolState.remaining program state = instructionCount program
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ => simp [position, ProtocolState.observe, ProtocolState.remaining, instructionCount]
      | inr rest =>
          have tail := position_add_remaining who next rest
          simp only [position, ProtocolState.observe, ProtocolState.remaining, Sum.elim_inr,
            instructionCount]
          omega
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl _ => simp [position, ProtocolState.observe, ProtocolState.remaining, instructionCount]
      | inr rest =>
          have tail := position_add_remaining who next rest
          simp only [position, ProtocolState.observe, ProtocolState.remaining, Sum.elim_inr,
            instructionCount]
          omega
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ => simp [position, ProtocolState.observe, ProtocolState.remaining, instructionCount]
      | inr rest =>
          have tail := position_add_remaining who next rest
          simp only [position, ProtocolState.observe, ProtocolState.remaining, Sum.elim_inr,
            instructionCount]
          omega

/-- Taking any already reached observation commutes with one actual source
transition, for every supported joint action. -/
theorem atRank_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (before after : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) →
    after ∈ (ProtocolState.step program before joint).support → (rank : Nat) →
    rank ≤ position who program (ProtocolState.observe who program before) →
    atRank who program rank (ProtocolState.observe who program after) =
      atRank who program rank (ProtocolState.observe who program before)
  | _, _, .ret _, before, after, _, supported, _, _ => by
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst after
      rfl
  | _, _, .sample name fresh law next, before, after, joint, supported, rank, within => by
      cases rank with
      | zero =>
          exact congrArg (fun view => some (Sum.inl view))
            (entryView_step who (.sample name fresh law next) before after joint supported)
      | succ rank =>
          cases before with
          | inl config => simp [ProtocolState.observe, position] at within
          | inr rest =>
              simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at supported
              obtain ⟨after, reached, rfl⟩ := supported
              have earlier : rank ≤ position who next (ProtocolState.observe who next rest) := by
                simpa only [ProtocolState.observe, Sum.elim_inr, position,
                  Nat.add_le_add_iff_right] using within
              exact congrArg (Option.map Sum.inr)
                (atRank_step who next rest after joint reached rank earlier)
  | _, _, .commit name owner fresh guard next, before, after, joint, supported, rank, within => by
      cases rank with
      | zero =>
          exact congrArg (fun view => some (Sum.inl view))
            (entryView_step who (.commit name owner fresh guard next) before after joint supported)
      | succ rank =>
          cases before with
          | inl config => simp [ProtocolState.observe, position] at within
          | inr rest =>
              simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at supported
              obtain ⟨after, reached, rfl⟩ := supported
              have earlier : rank ≤ position who next (ProtocolState.observe who next rest) := by
                simpa only [ProtocolState.observe, Sum.elim_inr, position,
                  Nat.add_le_add_iff_right] using within
              exact congrArg (Option.map Sum.inr)
                (atRank_step who next rest after joint reached rank earlier)
  | _, _, .reveal published owner name fresh selected unresolved next, before, after, joint,
      supported, rank, within => by
      cases rank with
      | zero =>
          exact congrArg (fun view => some (Sum.inl view))
            (entryView_step who (.reveal published owner name fresh selected unresolved next)
              before after joint supported)
      | succ rank =>
          cases before with
          | inl config => simp [ProtocolState.observe, position] at within
          | inr rest =>
              simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at supported
              obtain ⟨after, reached, rfl⟩ := supported
              have earlier : rank ≤ position who next (ProtocolState.observe who next rest) := by
                simpa only [ProtocolState.observe, Sum.elim_inr, position,
                  Nat.add_le_add_iff_right] using within
              exact congrArg (Option.map Sum.inr)
                (atRank_step who next rest after joint reached rank earlier)

/-- Encoding an entry configuration in the actual source protocol preserves
an observation-local auxiliary law. The source entry view is recovered from
the protocol observation, including before non-strategic instructions. -/
theorem entry_noise_factor
    {Seed : Type*} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (focal : Player)
    {Extra : Type*} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (extra : Seed → Extra) (noise : DecisionView focal Γ → PMF Extra)
    (factor : prior.map (fun seed => (source seed, extra seed)) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun value => (config, value)) :
    ∃ nextNoise : Option (ProtocolView focal program) → PMF Extra,
      let law := prior.map fun seed =>
        (some (ProtocolState.entry program (source seed)), extra seed)
      law = (law.map Prod.fst).bind fun state =>
        (nextNoise (state.map (ProtocolState.observe focal program))).map fun value =>
          (state, value) := by
  let recover := fun view : Option (ProtocolView focal program) =>
    view.elim ((source prior.support_nonempty.choose).view focal)
      (ProtocolView.entryView focal program)
  have recovered (state : Config Player L Γ) :
      recover ((some (ProtocolState.entry program state)).map
        (ProtocolState.observe focal program)) = state.view focal := by
    simp only [recover, Option.map_some, Option.elim_some,
      ProtocolView.entryView_observe_entry]
  refine ⟨fun view => noise (recover view), ?_⟩
  have result := map_observation_factor (prior.map fun seed => (source seed, extra seed))
    (fun config => config.view focal) noise (by
      simpa only [PMF.map_comp, Function.comp_def] using factor)
      (fun config => some (ProtocolState.entry program config))
      (Option.map (ProtocolState.observe focal program)) recover recovered
  simpa only [PMF.map_comp, Function.comp_def] using result

end ProtocolView

end Vegas.SourceProgram
