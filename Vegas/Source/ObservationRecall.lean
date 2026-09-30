/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding
import Vegas.Source.RevealSequence
import GameTheory.Math.Probability.ConditionalObservation
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Recovering earlier source observations

Source instructions extend the immutable environment and append only the
actor's original choice. The existing `Vegas.SourceProgram.DecisionView.back` therefore recovers
the prior view exactly, including at histories of probability zero under a
given policy. These are observation projections of the existing protocol.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
@[simp] theorem back_sample_view {Γ : SourceCtx Player L} {payload : L.Ty}
    (who : Player) (name : VarId) (config : Config Player L Γ) (value : L.Val payload) :
    ((sampleSuccessor name config value).view who).back false = config.view who := by
  exact back_sourceObserve (c := .publicData payload) value config.state (config.history who) false

omit [IExpr.ResultTypes L] in
@[simp] theorem back_commit_view {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} (who : Player) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : Config Player L Γ)
    (choice : PublicationResult (L.Val payload)) :
    ((commitSuccessor name guard config choice).view who).back (decide (owner = who)) =
      config.view who := by
  simp only [Config.view, commitSuccessor, back_sourceObserve]
  by_cases same : owner = who
  · subst who
    simp
  · simp [same, Function.update_of_ne (Ne.symm same)]

omit [IExpr.ResultTypes L] in
@[simp] theorem back_reveal_view {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (who : Player) (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    ((revealSuccessor published selected config disclose).view who).back
        (decide (owner = who)) = config.view who := by
  simp only [Config.view, revealSuccessor, back_sourceObserve]
  by_cases same : owner = who
  · subst who
    simp
  · simp [same, Function.update_of_ne (Ne.symm same)]

omit [IExpr.ResultTypes L] in
/-- Equality after a reveal implies equality before it, even when the two
supplied choices differ and even when a guard rejects the publication. -/
theorem reveal_view_reflects {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (who : Player) (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ) (leftChoice rightChoice : Bool)
    (same : (revealSuccessor published selected left leftChoice).view who =
      (revealSuccessor published selected right rightChoice).view who) :
    left.view who = right.view who := by
  have prior := congrArg (DecisionView.back (decide (owner = who))) same
  simpa only [back_reveal_view] using prior

omit [IExpr.ResultTypes L] in
/-- For successful initialized bindings and an empty guard registry, the
public result also identifies the Boolean reveal choice for every observer. -/
theorem reveal_choice_eq_of_view_eq {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (who : Player) (published : VarId)
    (selected : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ) (leftChoice rightChoice : Bool)
    (leftEmpty : left.registry = []) (rightEmpty : right.registry = [])
    (leftValue rightValue : L.Val payload)
    (leftOpen : left.state.get selected = .success leftValue)
    (rightOpen : right.state.get selected = .success rightValue)
    (same : (revealSuccessor published selected left leftChoice).view who =
      (revealSuccessor published selected right rightChoice).view who) :
    leftChoice = rightChoice := by
  have result := congrArg (fun view : DecisionView who ((published, .publication payload) :: Γ) =>
    view.1.cells.get (HasVar.here : HasVar ((published, CellTy.publication payload) :: Γ)
      published (.publication payload))) same
  change (revealSuccessor published selected left leftChoice).state.get .here =
    (revealSuccessor published selected right rightChoice).state.get .here at result
  rw [revealSuccessor_result_of_registry_empty published selected left leftEmpty leftChoice,
    revealSuccessor_result_of_registry_empty published selected right rightEmpty rightChoice,
    leftOpen, rightOpen] at result
  cases leftChoice <;> cases rightChoice <;> simp_all

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

theorem position_trace {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    {state : ProtocolState program}
    (trace : (executionProtocol program admission initial).Trace state) :
    position who program (ProtocolState.observe who program state) = trace.length := by
  have positionEq := position_add_remaining who program state
  have lengthEq := protocol_history_length program admission initial trace
  omega

theorem atRank_reaches {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    {fuel : Nat} {before after : (executionProtocol program admission initial).History}
    (reached : (executionProtocol program admission initial).ReachesWithin fuel before after)
    (rank : Nat) (within : rank ≤ before.trace.length) :
    atRank who program rank (ProtocolState.observe who program after.state) =
      atRank who program rank (ProtocolState.observe who program before.state) := by
  induction reached with
  | refl => rfl
  | @step fuel before after joint legal target realized rest ih =>
      have withinNext : rank ≤ (before.extend legal realized).trace.length := by
        simp only [ExecutionProtocol.History.extend, ExecutionProtocol.Trace.length]
        omega
      refine (ih withinNext).trans ?_
      apply atRank_step who program before.state target joint realized rank
      rw [position_trace who program admission initial before.trace]
      exact within

/-- An actual later source observation reconstructs each of its earlier
protocol observations at the requested rank. -/
theorem recover_prefix {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    {fuel : Nat} {before after : (executionProtocol program admission initial).History}
    (reached : (executionProtocol program admission initial).ReachesWithin fuel before after) :
    atRank who program before.trace.length (ProtocolState.observe who program after.state) =
      some (ProtocolState.observe who program before.state) := by
  rw [atRank_reaches who program admission initial reached _ le_rfl,
    ← position_trace who program admission initial before.trace, atRank_position]

/-- Equal endpoint observations imply equal earlier observations at matching
source ranks, even across different (possibly correlated) initial states. -/
theorem prefix_observations_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (leftInitial rightInitial : Config Player L Γ)
    {leftFuel rightFuel : Nat}
    {leftBefore leftAfter : (executionProtocol program admission leftInitial).History}
    {rightBefore rightAfter : (executionProtocol program admission rightInitial).History}
    (leftReached : (executionProtocol program admission leftInitial).ReachesWithin
      leftFuel leftBefore leftAfter)
    (rightReached : (executionProtocol program admission rightInitial).ReachesWithin
      rightFuel rightBefore rightAfter)
    (depth : leftBefore.trace.length = rightBefore.trace.length)
    (same : ProtocolState.observe who program leftAfter.state =
      ProtocolState.observe who program rightAfter.state) :
    ProtocolState.observe who program leftBefore.state =
      ProtocolState.observe who program rightBefore.state := by
  have left := recover_prefix who program admission leftInitial leftReached
  have right := recover_prefix who program admission rightInitial rightReached
  rw [depth, same] at left
  exact Option.some.inj (left.symm.trans right)

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
