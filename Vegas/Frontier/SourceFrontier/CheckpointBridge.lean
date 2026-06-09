/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.RoundView
import Vegas.Frontier.SourceFrontier.Bisimulation
import Vegas.Frontier.SourceFrontier.Checkpoint
import Vegas.Frontier.SourceFrontier.Commit
import Vegas.Frontier.SourceFrontier.Replay
import Vegas.Frontier.SourceFrontier.SourceCompletion
import Math.Coupling

/-!
# Source/frontier bisimulation via the checkpoint middle game

The full source-local ↔ behavioral-frontier Nash-deviation bisimulation is
obtained by composition, not by a direct raw bridge:

```
  sourceStrategicGame  ≈  sourceCheckpointBehavioralGame  ≈  behavioralFrontierGame
        (this file: middle bridge `S`)        (proven: `T`, in `Checkpoint.lean`)
```

The checkpoint↔frontier half (`T`,
`sourceCheckpointBehavioralFrontierNashDeviationBisimulation`) is already proven
and trivial: the checkpoint game reuses the frontier's own behavioral strategy
surface and its kernel is `PMF.map some` of the frontier kernel.  Only the
*middle* bridge `S` (`sourceStrategicGame ≈ sourceCheckpointBehavioralGame`)
carries real content, and `NashDeviationBisimulation.comp` glues them with a
`rfl` middle-view obligation (both middle views observe `Option (Outcome P)` by
`id`).

The relation is **law-based**, not functional: it bundles the base observed-law
equality with the two unilateral-deviation lifts.  This keeps both totalities
provable — a functional `rel σ τ := τ = realize σ` would make `frontier_total`
demand surjectivity of the realization map.

## Remaining proof obligations

The totality lemmas reduce to one whole-kernel adequacy theorem.  The only
remaining holes are the two pointwise strategy translations and
`sourceCheckpointAdequacy`; the six base/deviation law fields invoke that
central theorem directly.

Everything else (the middle bridge record, the `comp`, and the final
non-vacuous package) is fully discharged here.
-/

namespace Vegas

open GameTheory
open ToEventGraph.SourceFrontier

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Identity observation of the checkpoint game's optional source outcomes.

This must match the `viewG := { observe := id }` used by the proven
checkpoint↔frontier bridge `T`, so that `comp`'s middle-view obligation is
`rfl`. -/
def sourceCheckpointOptionOutcomeView
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.OutcomeView
      program.sourceCheckpointBehavioralGame (Option (Outcome P)) where
  observe := id

/-- Law-based source/checkpoint deviation relation: same base observed law, plus
matching unilateral deviations in both directions. -/
def SourceCheckpointDeviationRelated
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame horizon cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile) :
    Prop :=
  (program.sourceStrategicOptionOutcomeView horizon cutoff).law sourceProfile =
      program.sourceCheckpointOptionOutcomeView.law checkpointProfile ∧
  (∀ who
    (checkpointDeviation :
      program.sourceCheckpointBehavioralGame.Strategy who),
    ∃ sourceDeviation :
      (program.sourceStrategicGame horizon cutoff).Strategy who,
      (program.sourceStrategicOptionOutcomeView horizon cutoff).law
          (Function.update sourceProfile who sourceDeviation) =
        program.sourceCheckpointOptionOutcomeView.law
          (Function.update checkpointProfile who checkpointDeviation)) ∧
  (∀ who
    (sourceDeviation :
      (program.sourceStrategicGame horizon cutoff).Strategy who),
    ∃ checkpointDeviation :
      program.sourceCheckpointBehavioralGame.Strategy who,
      (program.sourceStrategicOptionOutcomeView horizon cutoff).law
          (Function.update sourceProfile who sourceDeviation) =
        program.sourceCheckpointOptionOutcomeView.law
          (Function.update checkpointProfile who checkpointDeviation))

/-- The middle bridge: source-local strategic play is Nash-deviation bisimilar
to checkpoint-aligned source behavioral play, observed through optional source
outcomes.  Fully discharged from the law-based relation — all content lives in
the totality lemmas below. -/
noncomputable def sourceCheckpointNashDeviationBisimulation
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P) :
    KernelGame.NashDeviationBisimulation
      (program.sourceStrategicGame horizon cutoff)
      program.sourceCheckpointBehavioralGame (Option (Outcome P)) where
  viewG := program.sourceStrategicOptionOutcomeView horizon cutoff
  viewH := program.sourceCheckpointOptionOutcomeView
  rel := SourceCheckpointDeviationRelated program horizon cutoff
  law_eq := by
    intro sourceProfile checkpointProfile hrel
    exact hrel.1
  simulate_target_deviation := by
    intro sourceProfile checkpointProfile hrel who checkpointDeviation
    exact hrel.2.1 who checkpointDeviation
  simulate_source_deviation := by
    intro sourceProfile checkpointProfile hrel who sourceDeviation
    exact hrel.2.2 who sourceDeviation

/-! ### Whole-kernel adequacy spine. -/

/-- Choose a concrete checkpoint history representing a reachable checkpoint
information state. -/
noncomputable def sourceCheckpointInfoRepresentative
    (program : WFProgram P L) [FiniteDomains program]
    (who : P)
    (info : program.SourceCheckpointInfoState who) :
    program.SourceCheckpointBehavioralHistory :=
  Classical.choose info.2

/-- The chosen checkpoint representative realizes the requested information
state. -/
theorem sourceCheckpointInfoRepresentative_info
    (program : WFProgram P L) [FiniteDomains program]
    (who : P)
    (info : program.SourceCheckpointInfoState who) :
    (program.sourceCheckpointInfoRepresentative who info).playerView who =
      info.1 :=
  Classical.choose_spec info.2

omit [DecidableEq P] [Fintype P] in
private theorem boundedLegalAction_nonempty
    {M : Machine P} (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (hterm : ¬ view.boundedTerminal horizon state) :
    Nonempty (view.BoundedLegalAction horizon state) := by
  classical
  have hmachine : ¬ M.terminal state.state := by
    intro hterminal
    exact hterm (Or.inl hterminal)
  have hcut : ¬ horizon ≤ state.depth := by
    intro hle
    exact hterm (Or.inr hle)
  rcases view.nonterminal_exists_legal
      (state := state.state) hmachine with
    ⟨action, haction⟩
  let boundedAction : JointAction view.Act := action
  have hbounded :
      JointActionLegal view.Act (view.boundedActive horizon)
        (view.boundedTerminal horizon)
        (view.boundedAvailableActions horizon) state boundedAction := by
    refine (view.boundedLegal_iff_forall horizon).2 ⟨hterm, ?_⟩
    intro player
    have hlocal := haction.2 player
    cases hmove : action player with
    | none =>
        have hnot : player ∉ view.active state.state := by
          simpa [hmove] using hlocal
        simpa [boundedAction, Machine.RoundView.boundedLocallyLegalAtState,
          Machine.RoundView.boundedActive, hcut, hmove] using hnot
    | some choice =>
        have hpair :
            player ∈ view.active state.state ∧
              choice ∈ view.availableActions state.state player := by
          simpa [hmove] using hlocal
        simpa [boundedAction, Machine.RoundView.boundedLocallyLegalAtState,
          Machine.RoundView.boundedActive,
          Machine.RoundView.boundedAvailableActions, hcut, hmove] using hpair
  exact ⟨⟨boundedAction, hbounded⟩⟩

/-- Source-induced legal joint checkpoint action law at one checkpoint
information state.

This is the hard part of `sourceToCheckpointStrategy`: for a chosen
representative checkpoint history, serialize the source strategy through the
source-order commits belonging to that checkpoint round and assemble the sampled
source choices into one legal frontier joint action.

The helper is deliberately nonterminal-indexed.  A bounded terminal/cutoff
checkpoint history has no legal joint action at all; the total strategy below
handles that branch at the local optional-move level by returning `none`. -/
noncomputable def sourceToCheckpointActionLaw
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (who : P)
    (sourceStrategy :
      (program.sourceStrategicGame horizon cutoff).Strategy who)
    (info : program.SourceCheckpointInfoState who)
    (hterm :
      ¬ Machine.RoundView.boundedTerminal
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon
          (program.sourceCheckpointInfoRepresentative who info).lastState) :
    PMF
      (Machine.RoundView.BoundedLegalAction
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon
        (program.sourceCheckpointInfoRepresentative who info).lastState) :=
  -- HONEST HOLE: the real source→checkpoint round-action serialization must use
  -- `sourceStrategy` to assemble the player's ready source-order commits in this
  -- checkpoint round into one legal frontier joint action.  The previous body
  -- (`PMF.pure (Classical.choice (boundedLegalAction_nonempty …))`) type-checked
  -- but ignored `sourceStrategy`, so it was a placeholder, not an implementation.
  sorry

/-- Source-induced local checkpoint move law.

This is the total surface required by `BoundedBehavioralStrategy`: terminal and
cutoff histories have the unique legal local move `none`; nonterminal histories
read the acting player's marginal from the nonterminal joint-action helper. -/
noncomputable def sourceToCheckpointMoveLaw
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (who : P)
    (sourceStrategy :
      (program.sourceStrategicGame horizon cutoff).Strategy who)
    (info : program.SourceCheckpointInfoState who) :
    PMF
      (Option
        ((program.frontierSemantics.behavioral.view).Act who)) := by
  classical
  let representative := program.sourceCheckpointInfoRepresentative who info
  by_cases hterm :
      Machine.RoundView.boundedTerminal
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon representative.lastState
  · exact PMF.pure none
  · exact
      PMF.map
        (fun action => action.1 who)
        (program.sourceToCheckpointActionLaw horizon cutoff who sourceStrategy
          info (by simpa [representative] using hterm))

/-- Translate one source-local strategy into the checkpoint behavioral surface.

This is the source→checkpoint direction of the whole-kernel adequacy theorem:
at a checkpoint information state it must assemble the player's full legal
frontier action law from the sequential source choices that belong to that
checkpoint round. -/
noncomputable def sourceToCheckpointStrategy
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (who : P)
    (sourceStrategy :
      (program.sourceStrategicGame horizon cutoff).Strategy who) :
    program.sourceCheckpointBehavioralGame.Strategy who where
  val := program.sourceToCheckpointMoveLaw horizon cutoff who sourceStrategy
  property := by
    classical
    intro h move hmove
    let info :=
      (program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
        program.frontierSemantics.horizon who h
    let representative :=
      program.sourceCheckpointInfoRepresentative who info
    have hinfo :
        representative.playerView who = h.playerView who := by
      simpa [info, representative] using
        program.sourceCheckpointInfoRepresentative_info who info
    by_cases hterm :
        Machine.RoundView.boundedTerminal
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon representative.lastState
    · have hmove_eq : move = none := by
        simpa [sourceToCheckpointMoveLaw, info, representative, hterm,
          PMF.support_pure, Set.mem_singleton_iff] using hmove
      subst move
      have hrepMove :
          none ∈
            (program.frontierSemantics.behavioral.view).boundedAvailableMoves
              program.frontierSemantics.horizon representative who := by
        rw [Machine.RoundView.mem_boundedAvailableMoves_iff]
        cases hterm with
        | inl hmachine =>
            simp [Machine.RoundView.boundedLocallyLegalAtState,
              Machine.RoundView.boundedActive,
              program.frontierSemantics.behavioral.view.terminal_active_eq_empty
                hmachine]
        | inr hcut =>
            simp [Machine.RoundView.boundedLocallyLegalAtState,
              Machine.RoundView.boundedActive, hcut]
      have hmenus :
          (program.frontierSemantics.behavioral.view).boundedAvailableMoves
              program.frontierSemantics.horizon representative who =
            (program.frontierSemantics.behavioral.view).boundedAvailableMoves
              program.frontierSemantics.horizon h who :=
        program.frontierSemantics.menus who representative h hinfo
      simpa [hmenus] using hrepMove
    · have hmove' :
          move ∈
            (PMF.map
              (fun action =>
                (action :
                  Machine.RoundView.BoundedLegalAction
                    program.frontierSemantics.behavioral.view
                    program.frontierSemantics.horizon
                    representative.lastState).1 who)
              (program.sourceToCheckpointActionLaw horizon cutoff who
                sourceStrategy info
                (by simpa [representative] using hterm))).support := by
        simpa [sourceToCheckpointMoveLaw, info, representative, hterm]
          using hmove
      exact
        Machine.RoundView.boundedLegalActionLaw_localSupport_of_sameInfo
          program.frontierSemantics.menus representative h who hinfo
          (program.sourceToCheckpointActionLaw horizon cutoff who
            sourceStrategy info
            (by simpa [representative] using hterm))
          hmove'

/-- A checkpoint behavioral strategy depends only on the checkpoint
information state, so any two concrete checkpoint histories with the same
player view induce the same local move law. -/
theorem checkpointStrategy_law_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    {left right : program.SourceCheckpointBehavioralHistory}
    (hview : left.playerView who = right.playerView who) :
    checkpointStrategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
          program.frontierSemantics.horizon who left) =
    checkpointStrategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
          program.frontierSemantics.horizon who right) := by
  have hinfo :
      (program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
          program.frontierSemantics.horizon who left =
        (program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
          program.frontierSemantics.horizon who right :=
    Subtype.ext hview
  exact congrArg checkpointStrategy.1 hinfo

/-- Project a checkpoint-local move law to the optional value assigned at one
compiled source-order node. -/
noncomputable def checkpointProjectedNodeOptionLaw
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    (checkpoint : program.SourceCheckpointBehavioralHistory)
    (node : Fin (ToEventGraph.compile program.core).graph.nodeCount) :
    PMF
      (Option
        (L.Val ((ToEventGraph.compile program.core).graph.nodeRow node).ty)) :=
  PMF.map
    (fun move =>
      match move with
      | some frontierAction => frontierAction.value? node
      | none => none)
    (checkpointStrategy.1
      ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
        program.frontierSemantics.horizon who checkpoint))

/-- Project a checkpoint-local move law to the optional value assigned at one
compiled source-order node, querying the checkpoint strategy directly at a
reachable checkpoint information state. -/
noncomputable def checkpointProjectedNodeOptionLawAtInfo
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    (info : program.SourceCheckpointInfoState who)
    (node : Fin (ToEventGraph.compile program.core).graph.nodeCount) :
    PMF
      (Option
        (L.Val ((ToEventGraph.compile program.core).graph.nodeRow node).ty)) :=
  PMF.map
    (fun move =>
      match move with
      | some frontierAction => frontierAction.value? node
      | none => none)
    (checkpointStrategy.1 info)

/-- The checkpoint-to-source projected node law is invariant under replacing
the concrete checkpoint representative by another history with the same player
view. -/
theorem checkpointProjectedNodeOptionLaw_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    {left right : program.SourceCheckpointBehavioralHistory}
    (hview : left.playerView who = right.playerView who)
    (node : Fin (ToEventGraph.compile program.core).graph.nodeCount) :
    program.checkpointProjectedNodeOptionLaw checkpointStrategy left node =
      program.checkpointProjectedNodeOptionLaw checkpointStrategy right node := by
  unfold checkpointProjectedNodeOptionLaw
  rw [program.checkpointStrategy_law_eq_of_playerView_eq
    checkpointStrategy hview]

/-- A concrete checkpoint representative and a directly supplied checkpoint
information state induce the same projected node law when their player views
agree. -/
theorem checkpointProjectedNodeOptionLaw_eq_of_checkpointInfo
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    (checkpoint : program.SourceCheckpointBehavioralHistory)
    (info : program.SourceCheckpointInfoState who)
    (hview : checkpoint.playerView who = info.1)
    (node : Fin (ToEventGraph.compile program.core).graph.nodeCount) :
    program.checkpointProjectedNodeOptionLaw checkpointStrategy checkpoint
        node =
      program.checkpointProjectedNodeOptionLawAtInfo checkpointStrategy info
        node := by
  unfold checkpointProjectedNodeOptionLaw
  unfold checkpointProjectedNodeOptionLawAtInfo
  have hinfo :
      (program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
          program.frontierSemantics.horizon who checkpoint =
        info :=
    Subtype.ext hview
  rw [hinfo]

/-- At an active checkpoint history where the current source-order node is
ready for `who`, the projected checkpoint-local move law has no `none` branch
at that node. -/
theorem checkpointProjectedNodeOptionLaw_support_some
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    (checkpoint : program.SourceCheckpointBehavioralHistory)
    (node : Fin (ToEventGraph.compile program.core).graph.nodeCount)
    (hactive :
      who ∈
        Machine.RoundView.boundedActive
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon checkpoint.lastState)
    (hready :
      EventGraph.ReadyCommitNode
        (ToEventGraph.compile program.core).graph
        checkpoint.lastState.state.1 who node)
    {result :
      Option
        (L.Val ((ToEventGraph.compile program.core).graph.nodeRow node).ty)}
    (hresult :
      result ∈
        (program.checkpointProjectedNodeOptionLaw
          checkpointStrategy checkpoint node).support) :
    ∃ value, result = some value := by
  classical
  cases result with
  | some value =>
      exact ⟨value, rfl⟩
  | none =>
      let view := program.frontierSemantics.behavioral.view
      let project :
          Option (view.Act who) →
            Option
              (L.Val
                ((ToEventGraph.compile program.core).graph.nodeRow node).ty) :=
        fun move =>
          match move with
          | some frontierAction => frontierAction.value? node
          | none => none
      have hmap :
          none ∈
            (PMF.map project
              (checkpointStrategy.1
                (view.reachableInfoStateOfHistory
                  program.frontierSemantics.horizon who checkpoint))).support := by
        simpa [checkpointProjectedNodeOptionLaw, view, project] using hresult
      rcases (PMF.mem_support_map_iff project
          (checkpointStrategy.1
            (view.reachableInfoStateOfHistory
              program.frontierSemantics.horizon who checkpoint))
          none).mp hmap with
        ⟨move, hmoveSupport, hproject⟩
      have hlegal :
          move ∈
            view.boundedAvailableMoves
              program.frontierSemantics.horizon checkpoint who :=
        checkpointStrategy.2 checkpoint hmoveSupport
      rw [Machine.RoundView.mem_boundedAvailableMoves_iff] at hlegal
      cases hmove : move with
      | none =>
          have hnotActive :
              who ∉
                Machine.RoundView.boundedActive view
                  program.frontierSemantics.horizon checkpoint.lastState := by
            simpa [view, Machine.RoundView.boundedLocallyLegalAtState,
              hmove] using hlegal
          exact False.elim (hnotActive (by simpa [view] using hactive))
      | some frontierAction =>
          have hlocal :
              who ∈
                  Machine.RoundView.boundedActive view
                    program.frontierSemantics.horizon checkpoint.lastState ∧
                frontierAction ∈
                  Machine.RoundView.boundedAvailableActions view
                    program.frontierSemantics.horizon
                    checkpoint.lastState who := by
            simpa [view, Machine.RoundView.boundedLocallyLegalAtState,
              hmove] using hlegal
          have hnotCutoff :
              ¬ program.frontierSemantics.horizon ≤
                checkpoint.lastState.depth := by
            intro hcutoff
            have hempty : who ∈ (∅ : Finset P) := by
              simpa [view, Machine.RoundView.boundedActive, hcutoff]
                using hlocal.1
            simp at hempty
          have hfrontierAvailable :
              EventGraph.FrontierAction.Available
                (ToEventGraph.compile program.core).graph
                checkpoint.lastState.state.1 who frontierAction := by
            have hbounded := hlocal.2
            rw [Machine.RoundView.boundedAvailableActions] at hbounded
            rw [if_neg hnotCutoff] at hbounded
            have hfrontier :
                frontierAction ∈
                  EventGraph.frontierAvailableActions
                    (ToEventGraph.compile program.core).graph
                    checkpoint.lastState.state who := by
              simpa [view, WFProgram.frontierSemantics,
                ToEventGraph.canonicalFrontierGameSemantics,
                ToEventGraph.FrontierGameSemantics.behavioral,
                EventGraph.frontierRoundView] using hbounded
            simpa [EventGraph.frontierAvailableActions] using hfrontier
          rcases
              (EventGraph.FrontierAction.Available.value?_isSome_iff_readyCommitNode
                hfrontierAvailable).2 hready with
            ⟨value, hvalue⟩
          simp [project, hmove, hvalue] at hproject

/-- Source-side replay data for a reachable source choice query.

This is the source half of the eventual source/checkpoint choice cursor: it
identifies the representative source commit, its prefix replay, and the current
source-order compiled node.  The checkpoint half still has to supply a concrete
checkpoint history internally closed from `replay.state`. -/
structure SourceChoiceReplayCursor
    (program : WFProgram P L) [FiniteDomains program]
    (who : P)
    (info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who)
    (_hchoice : info.1.currentView.point.IsChoiceFor who) where
  Γ : VCtx P L
  env : VEnv L Γ
  x : VarId
  b : L.Ty
  guard :
    L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool
  tail : VegasCore P L ((x, .sealed who b) :: Γ)
  sourceHistory : SourceHistoryPoint P L
  source_start :
    sourceHistory.start = ToEventGraph.sourceStart program.core
  source_current :
    sourceHistory.current =
      ({ ctx := Γ, env := env,
         cont := VegasCore.commit x who guard tail } :
        SourceConfig P L)
  source_view : sourceHistory.localHistoryView who = info.1
  replay :
    ToEventGraph.SourcePrefixReplay program.core
      ({ ctx := Γ, env := env,
         cont := VegasCore.commit x who guard tail } :
        SourceConfig P L)
  node : Fin (ToEventGraph.buildResult program.core).graph.nodeCount
  node_eq : (node : Nat) = replay.compilerState.nodes.length
  ready :
    EventGraph.ReadyCommitNode
      (ToEventGraph.buildResult program.core).graph
      replay.state.1 who node

omit [Fintype P] in
/-- Every reachable source choice query has source-prefix replay data at the
current source-order commit node. -/
theorem sourceChoiceReplayCursor_exists
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who)
    (hchoice : info.1.currentView.point.IsChoiceFor who) :
    Nonempty (SourceChoiceReplayCursor program who info hchoice) := by
  classical
  let history := info.representativeHistory (L := L)
  have hstart :
      history.start = ToEventGraph.sourceStart program.core :=
    info.representativeHistory_start_eq (L := L)
  have hview : history.localHistoryView who = info.1 :=
    info.representativeHistory_localHistoryView (L := L)
  have hchoiceHistory : history.IsChoiceFor who :=
    info.representativeHistory_isChoiceFor (L := L) hchoice
  rcases history with ⟨startCfg, labels, current, run⟩
  change startCfg = ToEventGraph.sourceStart program.core at hstart
  rcases current with ⟨Γ, env, cont⟩
  cases cont with
  | ret payoffs =>
      simp [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
        SourceConfig.activePlayer?, SourceConfig.programPoint,
        SourceProgramPoint.activePlayer?, SourceProgramPoint.kind]
        at hchoiceHistory
  | sample x D tail =>
      simp [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
        SourceConfig.activePlayer?, SourceConfig.programPoint,
        SourceProgramPoint.activePlayer?, SourceProgramPoint.kind]
        at hchoiceHistory
  | commit x owner guard tail =>
      have howner : owner = who := by
        simpa [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
          SourceConfig.activePlayer?, SourceConfig.programPoint,
          SourceProgramPoint.activePlayer?, SourceProgramPoint.kind]
          using hchoiceHistory
      subst owner
      have hrun :
          SourceConfig.LabeledStar
            (ToEventGraph.sourceStart program.core) labels
            ({ ctx := Γ, env := env,
               cont := VegasCore.commit x who guard tail } :
              SourceConfig P L) := by
        rw [← hstart]
        exact run
      rcases ToEventGraph.sourcePrefixReplay_exists program.core hrun with
        ⟨replay⟩
      rcases ToEventGraph.SourcePrefixReplay.readyCommitNode
          program.core replay with
        ⟨node, hnode, hready⟩
      exact
        ⟨{ Γ := Γ
           env := env
           x := x
           b := _
           guard := guard
           tail := tail
           sourceHistory :=
            { start := startCfg
              labels := labels
              current :=
                { ctx := Γ, env := env,
                  cont := VegasCore.commit x who guard tail }
              run := run }
           source_start := hstart
           source_current := rfl
           source_view := hview
           replay := replay
           node := node
           node_eq := hnode
           ready := hready }⟩
  | reveal y owner x hx tail =>
      simp [SourceHistoryPoint.IsChoiceFor, SourceConfig.IsChoiceFor,
        SourceConfig.activePlayer?, SourceConfig.programPoint,
        SourceProgramPoint.activePlayer?, SourceProgramPoint.kind]
        at hchoiceHistory

/-- Full local cursor for a checkpoint-to-source strategy query.

`SourceChoiceReplayCursor` gives the source prefix and current compiled commit
node.  This cursor adds the checkpoint history sitting after internal closure
from that replay state.  The missing global replay theorem for
`checkpointToSourceChoiceLaw` is precisely the theorem that constructs this
cursor for every reachable source information state. -/
structure SourceCheckpointChoiceCursor
    (program : WFProgram P L) [FiniteDomains program]
    (who : P)
    (info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who)
    (hchoice : info.1.currentView.point.IsChoiceFor who) where
  source : SourceChoiceReplayCursor program who info hchoice
  checkpoint : program.SourceCheckpointBehavioralHistory
  checkpointInfo : program.SourceCheckpointInfoState who
  checkpoint_view : checkpoint.playerView who = checkpointInfo.1
  node : Fin (ToEventGraph.compile program.core).graph.nodeCount
  node_eq : (node : Nat) = source.replay.compilerState.nodes.length
  fuel : Nat
  internal_support :
    checkpoint.lastState.state ∈
      (ToEventGraph.internalClosureTransition
        (ToEventGraph.compile program.core) fuel source.replay.state).support
  nonterminal :
    ¬ Machine.RoundView.boundedTerminal
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon checkpoint.lastState
  active :
    who ∈
      Machine.RoundView.boundedActive
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon checkpoint.lastState
  ready :
    EventGraph.ReadyCommitNode
      (ToEventGraph.compile program.core).graph
      checkpoint.lastState.state.1 who node
  sourceChoiceOfGuard :
    { value : L.Val source.b //
      evalGuard (Player := P) (L := L) source.guard value
        ((source.env.toView who).eraseEnv) = true } →
      SourceViewChoice (L := L) info.1 hchoice

/-- A ready commit node stays ready along an available run made only of internal
graph events: internal events complete internal nodes, never the commit node, so
its readiness is preserved by `Ready.completeNode_of_ne`. -/
private theorem ready_commitNode_persist_after_internalOnly_availableRunFrom
    (compiled : ToEventGraph.CompiledProgram P L)
    {source dst : (ToEventGraph.PrimitiveMachine compiled).State}
    {batch : List (ToEventGraph.PrimitiveMachine compiled).Event}
    {who : P} {node : Fin compiled.graph.nodeCount}
    (hcommitNode :
      ∃ row guard,
        compiled.graph.nodes[(node : Nat)]? = some row ∧
          row.sem = EventGraph.NodeSem.commit who guard)
    (hready : EventGraph.Ready compiled.graph source.1 node)
    (hinternal : ToEventGraph.InternalOnlyBatch compiled batch)
    (hrun :
      (ToEventGraph.PrimitiveMachine compiled).AvailableRunFrom
        source batch dst) :
    EventGraph.Ready compiled.graph dst.1 node := by
  obtain ⟨row, guard, hget, hsem⟩ := hcommitNode
  induction hrun with
  | nil state => exact hready
  | @cons source mid dst event events havailable hstep tail ih =>
      rcases hinternal event (by simp) with ⟨internalEvent, hevent⟩
      rw [hevent] at havailable hstep
      change EventGraph.InternalAvailable compiled.graph _ internalEvent at havailable
      have hnodeNe : node ≠ internalEvent.node := by
        intro hsame
        rcases havailable with ⟨internalStep⟩
        cases internalStep with
        | sample r _ r_get sem_eq _ _ _ =>
            have hrowGet :
                compiled.graph.nodes[(internalEvent.node : Nat)]? = some row := by
              simpa [hsame] using hget
            have hrowEq : row = r :=
              Option.some.inj (hrowGet.symm.trans r_get)
            rw [hrowEq, sem_eq] at hsem
            cases hsem
        | reveal r _ r_get sem_eq _ _ _ =>
            have hrowGet :
                compiled.graph.nodes[(internalEvent.node : Nat)]? = some row := by
              simpa [hsame] using hget
            have hrowEq : row = r :=
              Option.some.inj (hrowGet.symm.trans r_get)
            rw [hrowEq, sem_eq] at hsem
            cases hsem
      rcases
          ToEventGraph.readyInternalAtNode_step_support_completeNode
            compiled (node := internalEvent.node)
            (event :=
              Machine.Event.internal
                (M := ToEventGraph.PrimitiveMachine compiled)
                internalEvent)
            rfl havailable hstep with
        ⟨written, hmid⟩
      have hreadyMid : EventGraph.Ready compiled.graph mid.1 node := by
        rw [hmid]
        exact hready.completeNode_of_ne hnodeNe
      have htailInternal : ToEventGraph.InternalOnlyBatch compiled events := by
        intro tailEvent hmem
        exact hinternal tailEvent (by simp [hmem])
      exact ih hreadyMid htailInternal

/-- A ready commit node persists through the internal closure transition. -/
theorem readyCommitNode_persist_after_internalClosureTransition_support
    (compiled : ToEventGraph.CompiledProgram P L) (fuel : Nat)
    {state dst : (ToEventGraph.PrimitiveMachine compiled).State}
    {who : P} {node : Fin compiled.graph.nodeCount}
    (hready : EventGraph.ReadyCommitNode compiled.graph state.1 who node)
    (hsupport :
      dst ∈
        (ToEventGraph.internalClosureTransition compiled fuel state).support) :
    EventGraph.ReadyCommitNode compiled.graph dst.1 who node := by
  rcases hready with ⟨row, guard, hget, hsem, hreadyNode⟩
  rcases ToEventGraph.internalClosureTransition_support_cert
      compiled fuel hsupport with
    ⟨batch, hinternal, hrun⟩
  exact
    ⟨row, guard, hget, hsem,
      ready_commitNode_persist_after_internalOnly_availableRunFrom
        compiled ⟨row, guard, hget, hsem⟩ hreadyNode hinternal hrun⟩

/-- Graph-level reconstruction core — the intended hard part of the keystone.

Every reachable compiled config whose `who`-commit `node` is ready is internally
closed by some checkpoint `BoundedHistory` boundary state that has no ready
internal nodes and whose presentation depth is below the horizon.

WARNING — FALSE AS STATED for multi-commit rounds; do not attempt to prove it.
`JointActionLegal` forces every active player to commit, so a checkpoint round
fires every co-ready commit atomically.  Two source-independent commits `A`, `B`
(no data dependency between their nodes) are co-ready, so no checkpoint
`BoundedHistory` boundary ever has `A` committed and the co-ready `B` pending.
But `sourceChoiceCursor_exists` instantiates this at `state := B`'s source-order
`replay.state`, which has the earlier-in-source-order `A` already committed —
exactly such an unreachable mid-round state, so the `internalClosure(state)`
membership cannot hold.

The correct route is NOT reconstruction but hidden-commit view-invariance: `A`'s
commit is sealed from `B`, so `B`'s view (hence strategy query) is identical
whether or not `A` has committed, and `B`'s mid-round source choice must be
related to the checkpoint query at the *pre-round atomic boundary* (the whole
co-ready group still pending, `B` active there).  This theorem must be
reformulated to target that boundary and carry the view-invariance witness; the
persistence lemmas above remain valid regardless. -/
private theorem checkpointBoundary_covers_reachable
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (state :
      EventGraph.ReachableConfig (ToEventGraph.compile program.core).graph)
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hready :
      EventGraph.ReadyCommitNode (ToEventGraph.compile program.core).graph
        state.1 who node) :
    ∃ (checkpoint : program.SourceCheckpointBehavioralHistory) (fuel : Nat),
      checkpoint.lastState.state ∈
          (ToEventGraph.internalClosureTransition
            (ToEventGraph.compile program.core) fuel state).support ∧
        EventGraph.readyInternalNodes (ToEventGraph.compile program.core).graph
            checkpoint.lastState.state.1 = ∅ ∧
          checkpoint.lastState.depth < program.frontierSemantics.horizon := by
  sorry

/-- **Keystone — round-correspondence reconstruction.**

For any reachable compiled config carrying a ready commit node for `who`, there
is a checkpoint `BoundedHistory` whose last state internally closes the config,
is nonterminal, has `who` active, and exposes the same ready commit node.

This is the standalone forward round-simulation of the confluent-coarsening
program.  It is the shared foundation of all three remaining holes:

* it discharges `sourceChoiceCursor_exists` (specialize `state := replay.state`);
* it supplies the checkpoint→source round witness for the real
  `sourceToCheckpointActionLaw`;
* its per-round step is the diagonal-coupling step for
  `sourceCheckpointCommitBlockCoupling`.

The hard graph-level reconstruction is `checkpointBoundary_covers_reachable`;
here we discharge the round-view bounded predicates from its graph witnesses: the
ready commit node persists through the internal closure
(`readyCommitNode_persist_after_internalClosureTransition_support`), persistence
plus the depth bound rule out `boundedTerminal`, and the empty ready-internal
frontier turns `boundedActive` into `activePlayers`, which contains `who`. -/
theorem checkpointHistory_exists_of_reachable_readyCommit
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (state :
      EventGraph.ReachableConfig (ToEventGraph.compile program.core).graph)
    {node : Fin (ToEventGraph.compile program.core).graph.nodeCount}
    (hready :
      EventGraph.ReadyCommitNode (ToEventGraph.compile program.core).graph
        state.1 who node) :
    ∃ (checkpoint : program.SourceCheckpointBehavioralHistory) (fuel : Nat),
      checkpoint.lastState.state ∈
          (ToEventGraph.internalClosureTransition
            (ToEventGraph.compile program.core) fuel state).support ∧
        ¬ Machine.RoundView.boundedTerminal
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon checkpoint.lastState ∧
          who ∈
              Machine.RoundView.boundedActive
                program.frontierSemantics.behavioral.view
                program.frontierSemantics.horizon checkpoint.lastState ∧
            EventGraph.ReadyCommitNode
              (ToEventGraph.compile program.core).graph
              checkpoint.lastState.state.1 who node := by
  classical
  obtain ⟨checkpoint, fuel, hmem, hclosed, hdepth⟩ :=
    program.checkpointBoundary_covers_reachable state hready
  -- The ready commit node persists through the internal closure to the boundary.
  have hreadyAt :
      EventGraph.ReadyCommitNode (ToEventGraph.compile program.core).graph
        checkpoint.lastState.state.1 who node :=
    readyCommitNode_persist_after_internalClosureTransition_support
      (ToEventGraph.compile program.core) fuel hready hmem
  have hcut :
      ¬ program.frontierSemantics.horizon ≤ checkpoint.lastState.depth := by
    omega
  refine ⟨checkpoint, fuel, hmem, ?_, ?_, hreadyAt⟩
  · -- ¬ boundedTerminal: not at the cutoff, and a ready commit node ⇒ not terminal
    rw [Machine.RoundView.boundedTerminal]
    push_neg
    refine ⟨?_, by omega⟩
    intro hterm
    -- `hterm : M.terminal checkpoint.lastState.state` is graph terminality.
    have hgraphTerminal :
        EventGraph.Terminal (ToEventGraph.compile program.core).graph
          checkpoint.lastState.state.1 := by
      simpa [ToEventGraph.FrontierGameSemantics.behavioral,
        WFProgram.frontierSemantics, ToEventGraph.canonicalFrontierGameSemantics,
        EventGraph.frontierRoundView, EventGraph.PrimitiveMachineOf,
        ToEventGraph.primitiveMachineSpec,
        EventGraph.ToMachine.primitiveMachine] using hterm
    exact hreadyAt.ready.1 (hgraphTerminal node)
  · -- who ∈ boundedActive: below cutoff ⇒ `view.active`, which is `activePlayers`
    rw [Machine.RoundView.boundedActive, if_neg hcut]
    have hnotNonempty :
        ¬ (EventGraph.readyInternalNodes
            (ToEventGraph.compile program.core).graph
            checkpoint.lastState.state.1).Nonempty := by
      rw [hclosed]
      exact Finset.not_nonempty_empty
    show who ∈
      EventGraph.frontierActive (ToEventGraph.compile program.core).graph
        checkpoint.lastState.state
    unfold EventGraph.frontierActive
    rw [if_neg hnotNonempty]
    -- who ∈ activePlayers: the ready commit node populates `readyCommitNodes`.
    rw [EventGraph.activePlayers, Finset.mem_filter]
    exact ⟨Finset.mem_univ who,
      ⟨node, by
        rw [EventGraph.readyCommitNodes, Finset.mem_filter]
        exact ⟨Finset.mem_univ node, hreadyAt⟩⟩⟩

/-- Every reachable source choice query is contained in a checkpoint round.

This is the mid-trace reverse replay theorem: starting from a source-local
choice information state, recover a representative source commit prefix and a
checkpoint history obtained by internally closing the compiled replay state,
with a checkpoint information state suitable for querying the checkpoint
strategy. -/
theorem sourceChoiceCursor_exists
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who)
    (hchoice : info.1.currentView.point.IsChoiceFor who) :
    Nonempty (SourceCheckpointChoiceCursor program who info hchoice) := by
  classical
  sorry

/-- The checkpoint-to-source projected law can be read from the checkpoint
information state carried by a source/checkpoint choice cursor. -/
theorem checkpointProjectedNodeOptionLaw_eq_of_choiceCursor
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    {info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who}
    {hchoice : info.1.currentView.point.IsChoiceFor who}
    (cursor : SourceCheckpointChoiceCursor program who info hchoice) :
    program.checkpointProjectedNodeOptionLaw checkpointStrategy
        cursor.checkpoint cursor.node =
      program.checkpointProjectedNodeOptionLawAtInfo checkpointStrategy
        cursor.checkpointInfo cursor.node :=
  program.checkpointProjectedNodeOptionLaw_eq_of_checkpointInfo
    checkpointStrategy cursor.checkpoint cursor.checkpointInfo
    cursor.checkpoint_view cursor.node

private theorem checkpointProjectedNodeOptionLaw_sourceLegal
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    {info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who}
    {hchoice : info.1.currentView.point.IsChoiceFor who}
    (cursor : SourceCheckpointChoiceCursor program who info hchoice)
    {value :
      L.Val
        (((ToEventGraph.compile program.core).graph.nodeRow
          cursor.node).ty)}
    (hvalueSupport :
      some value ∈
        (program.checkpointProjectedNodeOptionLaw
          checkpointStrategy cursor.checkpoint cursor.node).support) :
    let sourceValue : L.Val cursor.source.b :=
      cast
        (congrArg L.Val
          (ToEventGraph.SourceFrontier.CommitBlock.currentNodeType
            program cursor.source.replay cursor.node_eq))
        value
    evalGuard (Player := P) (L := L) cursor.source.guard sourceValue
      ((cursor.source.env.toView who).eraseEnv) = true := by
  classical
  let view := program.frontierSemantics.behavioral.view
  let project :
      Option (view.Act who) →
        Option
          (L.Val
            (((ToEventGraph.compile program.core).graph.nodeRow
              cursor.node).ty)) :=
    fun move =>
      match move with
      | some frontierAction => frontierAction.value? cursor.node
      | none => none
  have hmap :
      some value ∈
        (PMF.map project
          (checkpointStrategy.1
            (view.reachableInfoStateOfHistory
              program.frontierSemantics.horizon who
              cursor.checkpoint))).support := by
    simpa [checkpointProjectedNodeOptionLaw, view, project] using
      hvalueSupport
  rcases (PMF.mem_support_map_iff project
      (checkpointStrategy.1
        (view.reachableInfoStateOfHistory
          program.frontierSemantics.horizon who cursor.checkpoint))
      (some value)).mp hmap with
    ⟨move, hmoveSupport, hproject⟩
  have hlegal :
      move ∈
        view.boundedAvailableMoves
          program.frontierSemantics.horizon cursor.checkpoint who :=
    checkpointStrategy.2 cursor.checkpoint hmoveSupport
  rw [Machine.RoundView.mem_boundedAvailableMoves_iff] at hlegal
  cases hmove : move with
  | none =>
      simp [project, hmove] at hproject
  | some frontierAction =>
      have hlocal :
          who ∈
              Machine.RoundView.boundedActive view
                program.frontierSemantics.horizon cursor.checkpoint.lastState ∧
            frontierAction ∈
              Machine.RoundView.boundedAvailableActions view
                program.frontierSemantics.horizon
                cursor.checkpoint.lastState who := by
        simpa [view, Machine.RoundView.boundedLocallyLegalAtState,
          hmove] using hlegal
      have hnotCutoff :
          ¬ program.frontierSemantics.horizon ≤
            cursor.checkpoint.lastState.depth := by
        intro hcutoff
        have hempty : who ∈ (∅ : Finset P) := by
          simpa [view, Machine.RoundView.boundedActive, hcutoff]
            using hlocal.1
        simp at hempty
      have hfrontierAvailable :
          EventGraph.FrontierAction.Available
            (ToEventGraph.compile program.core).graph
            cursor.checkpoint.lastState.state.1 who frontierAction := by
        have hbounded := hlocal.2
        rw [Machine.RoundView.boundedAvailableActions] at hbounded
        rw [if_neg hnotCutoff] at hbounded
        have hfrontier :
            frontierAction ∈
              EventGraph.frontierAvailableActions
                (ToEventGraph.compile program.core).graph
                cursor.checkpoint.lastState.state who := by
          simpa [view, WFProgram.frontierSemantics,
            ToEventGraph.canonicalFrontierGameSemantics,
            ToEventGraph.FrontierGameSemantics.behavioral,
            EventGraph.frontierRoundView] using hbounded
        simpa [EventGraph.frontierAvailableActions] using hfrontier
      have hvalue :
          frontierAction.value? cursor.node = some value := by
        simpa [project, hmove] using hproject
      simpa using
        CommitBlock.sourceLegal_of_frontierActionValue_after_internalClosure
          program cursor.source.replay cursor.node_eq cursor.fuel
          cursor.internal_support frontierAction hfrontierAvailable
          value hvalue

private noncomputable def sourceViewChoiceOfCheckpointProjection
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    {info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who}
    {hchoice : info.1.currentView.point.IsChoiceFor who}
    (cursor : SourceCheckpointChoiceCursor program who info hchoice)
    (value :
      L.Val
        (((ToEventGraph.compile program.core).graph.nodeRow
          cursor.node).ty))
    (hvalueSupport :
      some value ∈
        (program.checkpointProjectedNodeOptionLaw
          checkpointStrategy cursor.checkpoint cursor.node).support) :
    SourceViewChoice (L := L) info.1 hchoice := by
  classical
  let hty :=
    ToEventGraph.SourceFrontier.CommitBlock.currentNodeType
      program cursor.source.replay cursor.node_eq
  let sourceValue : L.Val cursor.source.b :=
    cast (congrArg L.Val hty) value
  have hguard :
      evalGuard (Player := P) (L := L) cursor.source.guard sourceValue
        ((cursor.source.env.toView who).eraseEnv) = true := by
    simpa [sourceValue, hty] using
      program.checkpointProjectedNodeOptionLaw_sourceLegal
        checkpointStrategy cursor hvalueSupport
  exact cursor.sourceChoiceOfGuard ⟨sourceValue, hguard⟩

/-- Checkpoint-to-source local choice law under an explicit source/checkpoint
cursor.

This proves the real local payload of the checkpoint→source translation:
support of the checkpoint player's projected move law at the replayed commit
node is turned into support of the source guard menu.  The total
`checkpointToSourceChoiceLaw` still needs the separate replay theorem that
constructs such a cursor for each reachable source information state. -/
noncomputable def checkpointToSourceChoiceLawOfCursor
    (program : WFProgram P L) [FiniteDomains program]
    {who : P}
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    {info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who}
    {hchoice : info.1.currentView.point.IsChoiceFor who}
    (cursor : SourceCheckpointChoiceCursor program who info hchoice) :
    PMF (SourceViewChoice (L := L) info.1 hchoice) := by
  classical
  let optionLaw :=
    program.checkpointProjectedNodeOptionLawAtInfo
      checkpointStrategy cursor.checkpointInfo cursor.node
  have hoptionLaw :
      optionLaw =
        program.checkpointProjectedNodeOptionLaw
          checkpointStrategy cursor.checkpoint cursor.node := by
    exact
      (program.checkpointProjectedNodeOptionLaw_eq_of_choiceCursor
        checkpointStrategy cursor).symm
  let htotal :
      ∀ result ∈ optionLaw.support,
        ∃ value, result = some value :=
    fun result hresult =>
      program.checkpointProjectedNodeOptionLaw_support_some
        checkpointStrategy cursor.checkpoint cursor.node cursor.active
        cursor.ready (by simpa [optionLaw, hoptionLaw] using hresult)
  let valueLaw :=
    ToEventGraph.eraseNonePMF optionLaw htotal
  exact
    valueLaw.bindOnSupport fun value hvalueSupport =>
      let hsomeSupport :
          some value ∈ optionLaw.support :=
        (ToEventGraph.mem_support_eraseNonePMF_iff
          (dist := optionLaw) (htotal := htotal)).mp hvalueSupport
      PMF.pure
        (program.sourceViewChoiceOfCheckpointProjection
          checkpointStrategy cursor value
          (by simpa [optionLaw, hoptionLaw] using hsomeSupport))

/-- Translate one checkpoint behavioral strategy into the source-local surface.

This is the checkpoint→source direction of the whole-kernel adequacy theorem:
at a source commit query it serializes the checkpoint-local frontier action law
through the current source-order commit. -/
noncomputable def checkpointToSourceChoiceLaw
    (program : WFProgram P L) [FiniteDomains program]
    (_horizon : Nat) (_cutoff : Payoff P)
    (who : P)
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who)
    (info :
      SourceReachableInfoState (L := L)
        (ToEventGraph.sourceStart program.core) who)
    (hchoice : info.1.currentView.point.IsChoiceFor who) :
    PMF (SourceViewChoice (L := L) info.1 hchoice) := by
  classical
  exact
    program.checkpointToSourceChoiceLawOfCursor checkpointStrategy
      (Classical.choice
        (program.sourceChoiceCursor_exists info hchoice))

/-- Translate one checkpoint behavioral strategy into the source-local surface.

The hard work is isolated in `checkpointToSourceChoiceLaw`, which must choose a
represented checkpoint cursor for the source information state, project the
checkpoint action law to the current source-order node, and condition on the
already-serialized commits from the same checkpoint round. -/
noncomputable def checkpointToSourceStrategy
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (who : P)
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who) :
    (program.sourceStrategicGame horizon cutoff).Strategy who :=
  fun info hchoice =>
    program.checkpointToSourceChoiceLaw horizon cutoff who checkpointStrategy
      info hchoice

/-- Pointwise source/checkpoint strategy adequacy.

The whole-kernel theorem works for mixed profiles: each player's strategy pair
may be related by either canonical translation direction.  This is what makes
the unilateral-deviation clauses reduce to the same theorem instead of needing
separate proofs. -/
def SourceCheckpointStrategyAdequate
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (who : P)
    (sourceStrategy :
      (program.sourceStrategicGame horizon cutoff).Strategy who)
    (checkpointStrategy :
      program.sourceCheckpointBehavioralGame.Strategy who) :
    Prop :=
  checkpointStrategy =
      program.sourceToCheckpointStrategy horizon cutoff who sourceStrategy ∨
    sourceStrategy =
      program.checkpointToSourceStrategy horizon cutoff who checkpointStrategy

/-- A legal checkpoint joint-action law at a concrete checkpoint cursor. -/
abbrev SourceCheckpointActionLaw
    (program : WFProgram P L) [FiniteDomains program]
    (checkpoint : program.SourceCheckpointBehavioralHistory) : Type :=
  PMF
    (Machine.RoundView.BoundedLegalAction
      program.frontierSemantics.behavioral.view
      program.frontierSemantics.horizon checkpoint.lastState)

/-- A mid-trace source/checkpoint cursor for the generalized adequacy
induction.

The public theorem starts from the initial source history and the empty
checkpoint history, but the induction cannot.  During a checkpoint round the
source side may be inside the serialized commit block for that round while the
checkpoint side still sits at the pre-round history.  `residualActionLaw`
records that phase: `none` means both sides are at a checkpoint boundary; `some`
law means the remaining source commits are being generated from one checkpoint
round-action law. -/
structure SourceCheckpointCursor
    (program : WFProgram P L) [FiniteDomains program] where
  source :
    SourceStrategicHistory (L := L)
      (ToEventGraph.sourceStart program.core)
  checkpoint : program.SourceCheckpointBehavioralHistory
  replay : ToEventGraph.SourcePrefixReplay program.core source.history.current
  residualActionLaw : Option (SourceCheckpointActionLaw program checkpoint)

omit [Fintype P] in
/-- A terminal source cursor replay has completed every compiled graph node.

This is the prefix-level terminal fact used by block-fuel existence: at a
checkpoint boundary, a nonterminal checkpoint cannot be paired with a terminal
source prefix. -/
private theorem sourcePrefixReplay_graphTerminal_of_sourceTerminal
    (program : WFProgram P L) [FiniteDomains program]
    {source :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)}
    (replay :
      ToEventGraph.SourcePrefixReplay program.core source.history.current)
    (hterminal : source.history.current.IsTerminal) :
    EventGraph.Terminal (ToEventGraph.compile program.core).graph
      replay.state.1 := by
  have hcount :
      source.history.current.cont.instrCount = 0 :=
    SourceStrategicHistory.instrCount_eq_zero_of_terminal hterminal
  have hnodes :
      replay.compilerState.nodes.length =
        (ToEventGraph.buildResult program.core).graph.nodeCount := by
    let tailResult :=
      ToEventGraph.compileCore source.history.current.cont
        replay.remainingFresh replay.remainingNormalized
        replay.compilerState
    have hlen :
        tailResult.nodes.length =
          replay.compilerState.nodes.length +
            source.history.current.cont.instrCount :=
      ToEventGraph.compileCore_nodes_length
        source.history.current.cont replay.remainingFresh
        replay.remainingNormalized replay.compilerState
    have hgraph : ToEventGraph.BuildResult.graph tailResult =
        (ToEventGraph.buildResult program.core).graph := by
      simpa [tailResult] using replay.compiledGraph_eq
    have hnodeCount :
        tailResult.nodes.length =
          (ToEventGraph.buildResult program.core).graph.nodeCount := by
      have hnodesEq :
          (ToEventGraph.BuildResult.graph tailResult).nodes =
            (ToEventGraph.buildResult program.core).graph.nodes :=
        congrArg EventGraph.Graph.nodes hgraph
      simpa [ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]
        using congrArg List.length hnodesEq
    omega
  intro node
  have hdone := (replay.donePrefix node).mpr (by
    rw [hnodes]
    exact node.2)
  simpa [ToEventGraph.compile, ToEventGraph.buildResult] using hdone

/-- Concrete replay certificate for the empty source prefix.  Keeping this
explicit avoids hiding the initial compiled state behind an arbitrary choice
when instantiating the public adequacy theorem. -/
noncomputable def sourceCheckpointInitialReplay
    (program : WFProgram P L) [FiniteDomains program] :
    ToEventGraph.SourcePrefixReplay program.core
      (ToEventGraph.sourceStart program.core) := by
  let init :=
    ToEventGraph.initialState program.core.Γ program.core.env program.core.wctx
  let compilerState := ToEventGraph.BuildState.fromInitial init
  let result :=
    ToEventGraph.compileCore program.core.prog program.core.fresh
      program.core.normalized compilerState
  let state : EventGraph.ReachableConfig
      (ToEventGraph.buildResult program.core).graph :=
    ⟨EventGraph.Config.initial (ToEventGraph.buildResult program.core).graph,
      EventGraph.Reachable.initial⟩
  refine
    { compilerState := compilerState
      remainingFresh := program.core.fresh
      remainingNormalized := program.core.normalized
      compiledGraph_eq := by
        simp [ToEventGraph.sourceStart, compilerState, init,
          ToEventGraph.buildResult]
      state := state
      donePrefix := ?_
      storeAgree := ?_ }
  · simpa [state, compilerState, init] using
      ToEventGraph.DonePrefix.initial
        (ToEventGraph.buildResult program.core).graph
  · intro name bindTy h
    have hagree :=
      ToEventGraph.StoreAgree_fromInitial_initialStore
        program.core.env program.core.wctx result.nodes h
    simpa [state, compilerState, init, ToEventGraph.sourceStart,
      ToEventGraph.buildResult, EventGraph.Config.initial, result,
      ToEventGraph.BuildResult.graph,
      ToEventGraph.compileCore_initialFields] using hagree

/-- Initial source/checkpoint cursor used to instantiate the generalized
adequacy invariant. -/
noncomputable def sourceCheckpointInitialCursor
    (program : WFProgram P L) [FiniteDomains program] :
    SourceCheckpointCursor program where
  source :=
    SourceStrategicHistory.initial (L := L)
      (ToEventGraph.sourceStart program.core)
      program.core.normalized
  checkpoint :=
    Machine.RoundView.BoundedHistory.nil
      program.frontierSemantics.behavioral.view
      program.frontierSemantics.horizon
  replay := program.sourceCheckpointInitialReplay
  residualActionLaw := none

/-- If the source start is already a `ret`, the empty checkpoint history reports
the same source outcome.

The proof destructs the checked program so the source body and its dependent
freshness/normalization certificates reduce together.  This is the terminal
zero-instruction base case needed by the public initial cursor invariant. -/
theorem sourceCheckpointInitialOutcome_ret
    (program : WFProgram P L) [FiniteDomains program]
    (payoffs : List (P × L.Expr (erasePubVCtx program.core.Γ) L.int))
    (hret : program.core.prog = VegasCore.ret payoffs) :
    (ToEventGraph.sourceStart program.core).outcome? =
      ToEventGraph.sourceOutcomeOptionAtHistory program.core
        (Machine.RoundView.BoundedHistory.nil
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon) := by
  rcases program with ⟨⟨Γ, prog, env, wctx, fresh, normalized⟩,
    reveals, legal⟩
  dsimp at payoffs hret ⊢
  cases prog with
  | ret sourcePayoffs =>
      cases hret
      simp only [ToEventGraph.sourceStart, SourceConfig.outcome?_ret,
        ToEventGraph.sourceOutcomeOptionAtHistory,
        ToEventGraph.compile, ToEventGraph.BuildState.fromInitial,
        ToEventGraph.compileCore, EventGraph.ToMachine.primitiveMachine,
        EventGraph.Config.initial, ToEventGraph.primitiveMachineSpec,
        Machine.RoundView.BoundedHistory.lastState,
        WFProgram.frontierSemantics,
        ToEventGraph.canonicalFrontierGameSemantics,
        ToEventGraph.FrontierGameSemantics.behavioral,
        Machine.BoundedState.init,
        ToEventGraph.FrontierGameSemantics.horizon,
        Machine.RoundView.BoundedHistory.steps_nil,
        Machine.RoundView.lastStateFrom,
        ToEventGraph.sourceOutcomeAtTerminal, ToEventGraph.buildResult,
        ToEventGraph.sourceEnvAtTerminal,
        Machine.RoundView.BoundedHistory.lastState_nil,
        Option.some_eq_dite_none_right, Option.some.injEq]
      refine ⟨?_, ?_⟩
      · intro node
        have hnode : (node : Nat) < 0 := by
          simpa [EventGraph.Graph.nodeCount] using node.2
        omega
      · let init := ToEventGraph.initialState Γ env wctx
        let state := ToEventGraph.BuildState.fromInitial init
        let store : EventGraph.Store L :=
          (({ initialFields := init.initialFields,
              nodes := ([] : List (EventGraph.EventNode P L)) } :
              EventGraph.Graph P L).initialStore)
        have hagree : ToEventGraph.StoreAgree state env store := by
          intro name bindTy h
          exact
            ToEventGraph.StoreAgree_fromInitial_initialStore env wctx
              ([] : List (EventGraph.EventNode P L)) h
        let available :
            ∀ {name bindTy} (h : VHasVar Γ name bindTy),
              ∃ value,
                store.getAs (state.fieldOf h) bindTy.base = some value := by
          intro name bindTy h
          exact ⟨env.get h, hagree h⟩
        have henv :
            ToEventGraph.sourceEnvOfStore state store available = env :=
          ToEventGraph.sourceEnvOfStore_eq_of_storeAgree hagree available
        change evalPayoffs payoffs env =
          evalPayoffs payoffs
            (ToEventGraph.sourceEnvOfStore state store available)
        rw [henv]
  | sample _ _ _ =>
      cases hret
  | commit _ _ _ _ =>
      cases hret
  | reveal _ _ _ _ _ =>
      cases hret

/-- Explicit fallback-unreachability side condition for the generalized cursor
invariant.

`checkpointToSourceStrategy` will need a default branch for reachable source
information states that are not represented by the current checkpoint cursor.
The induction must prove that branch is never queried on the support of the
source distribution.  This condition packages that obligation at the exact
shape used by the source step kernel: every supported source choice state can
be re-equipped with a checkpoint cursor. -/
def SourceCheckpointFallbackUnreachable
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel : Nat)
    (cursor : SourceCheckpointCursor program) : Prop :=
  ∀ sourceState,
    sourceState ∈
        (SourceStrategicHistory.traceDistFrom
          (L := L) sourceProfile sourceFuel cursor.source).support →
      ∀ who,
        sourceState.history.IsChoiceFor who →
          ∃ represented : SourceCheckpointCursor program,
            represented.source = sourceState ∧
              represented.checkpoint ∈
                (Machine.RoundView.BoundedHistory.runDistFrom
                  program.frontierSemantics.behavioral.view
                  program.frontierSemantics.horizon checkpointProfile
                  checkpointFuel cursor.checkpoint).support

/-- Source fuel and checkpoint fuel are synchronized at a cursor, and a
checkpoint-boundary cursor is the internal closure of its source replay.

The public theorem is not true for arbitrary source/checkpoint cursors and
arbitrary fuel.  This invariant is the induction hypothesis boundary: it says
the remaining source steps and remaining checkpoint rounds are the suffixes of
one execution prefix, and it exposes the internal-closure fact used to enter a
checkpoint round. -/
structure SourceCheckpointCursorInvariant
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel : Nat)
    (cursor : SourceCheckpointCursor program) : Prop where
  sourceFuel_balance :
    cursor.source.history.labels.length + sourceFuel =
      program.core.prog.instrCount
  checkpointFuel_balance :
    cursor.checkpoint.steps.length + checkpointFuel =
      program.frontierSemantics.horizon
  boundary_replay :
    cursor.residualActionLaw = none →
      cursor.checkpoint.lastState.state = cursor.replay.state
  terminal_alignment :
    cursor.residualActionLaw = none →
      Machine.RoundView.boundedTerminal
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon cursor.checkpoint.lastState →
        cursor.source.history.current.IsTerminal ∧
          cursor.source.history.current.outcome? =
            ToEventGraph.sourceOutcomeOptionAtHistory program.core
              cursor.checkpoint
  fallback_unreachable :
    SourceCheckpointFallbackUnreachable program cutoff sourceProfile
      checkpointProfile sourceFuel checkpointFuel cursor

/-- Source/checkpoint successor states are represented by a cursor satisfying
the invariant for the remaining fuels. -/
def SourceCheckpointSuccessorRelated
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel : Nat) :
    SourceStrategicHistory (L := L)
      (ToEventGraph.sourceStart program.core) →
      program.SourceCheckpointBehavioralHistory → Prop :=
  fun sourceState checkpointHistory =>
    ∃ cursor : SourceCheckpointCursor program,
      cursor.source = sourceState ∧
        cursor.checkpoint = checkpointHistory ∧
          SourceCheckpointCursorInvariant program cutoff sourceProfile
            checkpointProfile sourceFuel checkpointFuel cursor ∧
            cursor.residualActionLaw = none

private noncomputable def couplingOfSupportRelation
    {α β : Type*} (R : α → β → Prop) (left : PMF α) (right : PMF β)
    (hrel :
      ∀ leftValue,
        leftValue ∈ left.support →
          ∀ rightValue,
            rightValue ∈ right.support →
              R leftValue rightValue) :
    Math.Coupling.HasCoupling R left right where
  joint := Math.ProbabilityMassFunction.prod left right
  marginal_fst := Math.ProbabilityMassFunction.prod_map_fst left right
  marginal_snd := Math.ProbabilityMassFunction.prod_map_snd left right
  rel_holds := by
    intro pair hpair
    have hleft :
        pair.1 ∈ left.support := by
      have hmapped :
          pair.1 ∈
            ((Math.ProbabilityMassFunction.prod left right).map
                Prod.fst).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨pair, hpair, rfl⟩
      simpa [Math.ProbabilityMassFunction.prod_map_fst left right] using
        hmapped
    have hright :
        pair.2 ∈ right.support := by
      have hmapped :
          pair.2 ∈
            ((Math.ProbabilityMassFunction.prod left right).map
                Prod.snd).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨pair, hpair, rfl⟩
      simpa [Math.ProbabilityMassFunction.prod_map_snd left right] using
        hmapped
    exact hrel pair.1 hleft pair.2 hright

omit [DecidableEq P] in
private theorem boundedRunDistFrom_one_support_steps_length
    {M : Machine P} (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (profile : view.BoundedBehavioralProfile horizon)
    (history : view.BoundedHistory horizon)
    (hnonterminal : ¬ view.boundedTerminal horizon history.lastState)
    {dstHistory : view.BoundedHistory horizon}
    (hsupport :
      dstHistory ∈
        (Machine.RoundView.BoundedHistory.runDistFrom
          view horizon profile 1 history).support) :
    dstHistory.steps.length = history.steps.length + 1 := by
  classical
  have hsupport' :
      dstHistory ∈
        ((Machine.RoundView.legalActionLaw
            view horizon profile history hnonterminal).bind fun action =>
          (Machine.RoundView.boundedTransition
            view horizon history.lastState action).bind fun dst =>
            Machine.RoundView.BoundedHistory.runDistFrom
              view horizon profile 0
              (history.extendByOutcome action dst)).support := by
    simpa [Machine.RoundView.BoundedHistory.runDistFrom,
      hnonterminal] using hsupport
  rw [PMF.mem_support_bind_iff] at hsupport'
  rcases hsupport' with ⟨action, _hactionSupport, hdstSupport⟩
  rw [PMF.mem_support_bind_iff] at hdstSupport
  rcases hdstSupport with ⟨dst, hdstSupport, htailSupport⟩
  have hdstMass :
      Machine.RoundView.boundedTransition
          view horizon history.lastState action dst ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hdstSupport
  have hhistory_eq :
      dstHistory = history.extendByOutcome action dst := by
    simpa [Machine.RoundView.BoundedHistory.runDistFrom,
      PMF.support_pure, Set.mem_singleton_iff] using htailSupport
  subst dstHistory
  rw [Machine.RoundView.BoundedHistory.extendByOutcome_of_support
    history action dst hdstMass]
  simp [Machine.RoundView.BoundedHistory.snoc]

/-- After `sourceBlockFuel` source steps, every supported source successor has
advanced to a new checkpoint-boundary cursor. -/
def SourceCheckpointSourceBoundaryAfter
    (program : WFProgram P L) [FiniteDomains program]
    (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (cursor : SourceCheckpointCursor program)
    (sourceBlockFuel : Nat) : Prop :=
  ∀ sourceState,
    sourceState ∈
        (SourceStrategicHistory.traceDistFrom
          (L := L) sourceProfile sourceBlockFuel cursor.source).support →
      cursor.source.history.labels.length <
          sourceState.history.labels.length ∧
        ∃ represented : SourceCheckpointCursor program,
          represented.source = sourceState ∧
            represented.residualActionLaw = none

/-- After one checkpoint round, every supported checkpoint successor has
advanced to a new checkpoint-boundary cursor. -/
def SourceCheckpointCheckpointBoundaryAfter
    (program : WFProgram P L) [FiniteDomains program]
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (cursor : SourceCheckpointCursor program) : Prop :=
  ∀ checkpointHistory,
    checkpointHistory ∈
        (Machine.RoundView.BoundedHistory.runDistFrom
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon checkpointProfile 1
          cursor.checkpoint).support →
      cursor.checkpoint.steps.length < checkpointHistory.steps.length ∧
        ∃ represented : SourceCheckpointCursor program,
          represented.checkpoint = checkpointHistory ∧
            represented.residualActionLaw = none

/-- Exact source fuel consumed by the next checkpoint round from a boundary
cursor.

This is the structural block-length obligation.  It splits the remaining fuels
into "one source-order block plus the suffix" and "one checkpoint round plus
the suffix", and it requires `sourceBlockFuel` to be the first source fuel that
reaches the next checkpoint boundary on support. -/
structure SourceCheckpointCommitBlockFuel
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (cursor : SourceCheckpointCursor program)
    (sourceFuel checkpointFuel sourceBlockFuel
      sourceFuelAfter checkpointFuelAfter : Nat) : Prop where
  boundary : cursor.residualActionLaw = none
  sourceFuel_split : sourceFuel = sourceBlockFuel + sourceFuelAfter
  checkpointFuel_split : checkpointFuel = checkpointFuelAfter + 1
  checkpoint_nonterminal :
    ¬ Machine.RoundView.boundedTerminal
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon cursor.checkpoint.lastState
  source_boundary :
    SourceCheckpointSourceBoundaryAfter program cutoff sourceProfile
      cursor sourceBlockFuel
  checkpoint_boundary :
    SourceCheckpointCheckpointBoundaryAfter program checkpointProfile cursor
  source_minimal :
    ∀ shorter,
      shorter < sourceBlockFuel →
        ¬ SourceCheckpointSourceBoundaryAfter program cutoff sourceProfile
          cursor shorter

/-- The current block predicate is only a one-source-step predicate.

This exposes the remaining adequacy gap sharply: a true checkpoint-round
stutter lemma needs a block length characterized by the whole frontier round,
not merely the first source step that advances. -/
theorem sourceCheckpointCommitBlockFuel_eq_one
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel sourceBlockFuel
      sourceFuelAfter checkpointFuelAfter : Nat)
    (cursor : SourceCheckpointCursor program)
    (hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile sourceFuel checkpointFuel cursor)
    (hblock :
      SourceCheckpointCommitBlockFuel program cutoff sourceProfile
        checkpointProfile cursor sourceFuel checkpointFuel sourceBlockFuel
        sourceFuelAfter checkpointFuelAfter) :
    sourceBlockFuel = 1 := by
  classical
  have hsource_not_terminal :
      ¬ cursor.source.history.current.IsTerminal := by
    intro hsource_terminal
    have hgraph_terminal :
        EventGraph.Terminal (ToEventGraph.compile program.core).graph
          cursor.replay.state.1 :=
      sourcePrefixReplay_graphTerminal_of_sourceTerminal
        program cursor.replay hsource_terminal
    have hcheckpoint_graph_terminal :
        EventGraph.Terminal (ToEventGraph.compile program.core).graph
          cursor.checkpoint.lastState.state.1 := by
      rw [hcursor.boundary_replay hblock.boundary]
      exact hgraph_terminal
    exact hblock.checkpoint_nonterminal
      (Or.inl (by
        simpa [ToEventGraph.FrontierGameSemantics.behavioral,
          WFProgram.frontierSemantics, ToEventGraph.canonicalFrontierGameSemantics,
          EventGraph.frontierRoundView, EventGraph.PrimitiveMachineOf,
          ToEventGraph.primitiveMachineSpec,
          EventGraph.ToMachine.primitiveMachine] using
          hcheckpoint_graph_terminal))
  have hboundary_one :
      SourceCheckpointSourceBoundaryAfter program cutoff sourceProfile
        cursor 1 := by
    intro sourceState hsupport
    have hsupport_step :
        sourceState ∈
          (SourceStrategicHistory.stepKernel sourceProfile
            cursor.source).support := by
      simpa [SourceStrategicHistory.traceDistFrom] using hsupport
    have hcount_step :
        cursor.source.history.current.cont.instrCount =
          sourceState.history.current.cont.instrCount + 1 :=
      SourceStrategicHistory.instrCount_stepKernel_support_of_not_terminal
        sourceProfile hsource_not_terminal hsupport_step
    have hlen_cursor :=
      SourceConfig.LabeledStar.length_add_instrCount
        cursor.source.history.run
    have hlen_cursor' :
        cursor.source.history.labels.length +
            cursor.source.history.current.cont.instrCount =
          program.core.prog.instrCount := by
      rw [cursor.source.start_eq] at hlen_cursor
      simpa [ToEventGraph.sourceStart] using hlen_cursor
    have hlen_source :=
      SourceConfig.LabeledStar.length_add_instrCount
        sourceState.history.run
    have hlen_source' :
        sourceState.history.labels.length +
            sourceState.history.current.cont.instrCount =
          program.core.prog.instrCount := by
      rw [sourceState.start_eq] at hlen_source
      simpa [ToEventGraph.sourceStart] using hlen_source
    rcases program.sourceStrategicHistory_prefixReplay sourceState with
      ⟨replay⟩
    refine ⟨by omega, ?_⟩
    let represented : SourceCheckpointCursor program :=
      { source := sourceState
        checkpoint := cursor.checkpoint
        replay := replay
        residualActionLaw := none }
    exact ⟨represented, rfl, rfl⟩
  have hpositive : 0 < sourceBlockFuel := by
    by_contra hnot
    have hzero : sourceBlockFuel = 0 := Nat.eq_zero_of_not_pos hnot
    subst sourceBlockFuel
    have hself :
        cursor.source ∈
          (SourceStrategicHistory.traceDistFrom
            (L := L) sourceProfile 0 cursor.source).support := by
      simp [SourceStrategicHistory.traceDistFrom]
    have hbad := hblock.source_boundary cursor.source hself
    exact Nat.lt_irrefl _ hbad.1
  have hle_one : sourceBlockFuel ≤ 1 := by
    by_contra hnot
    have hone_lt : 1 < sourceBlockFuel := by omega
    exact hblock.source_minimal 1 hone_lt hboundary_one
  omega

private theorem sourceCheckpoint_sourceBlock_support_fuel_balance
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel sourceBlockFuel
      sourceFuelAfter checkpointFuelAfter : Nat)
    (cursor : SourceCheckpointCursor program)
    (hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile sourceFuel checkpointFuel cursor)
    (hblock :
      SourceCheckpointCommitBlockFuel program cutoff sourceProfile
        checkpointProfile cursor sourceFuel checkpointFuel sourceBlockFuel
        sourceFuelAfter checkpointFuelAfter)
    {sourceState :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)}
    (hsupport :
      sourceState ∈
        (SourceStrategicHistory.traceDistFrom
          (L := L) sourceProfile sourceBlockFuel cursor.source).support) :
    sourceState.history.labels.length + sourceFuelAfter =
      program.core.prog.instrCount := by
  classical
  have hblock_one :
      sourceBlockFuel = 1 :=
    sourceCheckpointCommitBlockFuel_eq_one
      program cutoff sourceProfile checkpointProfile sourceFuel
      checkpointFuel sourceBlockFuel sourceFuelAfter checkpointFuelAfter
      cursor hcursor hblock
  have hsource_not_terminal :
      ¬ cursor.source.history.current.IsTerminal := by
    intro hsource_terminal
    have hgraph_terminal :
        EventGraph.Terminal (ToEventGraph.compile program.core).graph
          cursor.replay.state.1 :=
      sourcePrefixReplay_graphTerminal_of_sourceTerminal
        program cursor.replay hsource_terminal
    have hcheckpoint_graph_terminal :
        EventGraph.Terminal (ToEventGraph.compile program.core).graph
          cursor.checkpoint.lastState.state.1 := by
      rw [hcursor.boundary_replay hblock.boundary]
      exact hgraph_terminal
    exact hblock.checkpoint_nonterminal
      (Or.inl (by
        simpa [ToEventGraph.FrontierGameSemantics.behavioral,
          WFProgram.frontierSemantics, ToEventGraph.canonicalFrontierGameSemantics,
          EventGraph.frontierRoundView, EventGraph.PrimitiveMachineOf,
          ToEventGraph.primitiveMachineSpec,
          EventGraph.ToMachine.primitiveMachine] using
          hcheckpoint_graph_terminal))
  have hsupport_one :
      sourceState ∈
        (SourceStrategicHistory.traceDistFrom
          (L := L) sourceProfile 1 cursor.source).support := by
    simpa [hblock_one] using hsupport
  have hsupport_step :
      sourceState ∈
        (SourceStrategicHistory.stepKernel sourceProfile
          cursor.source).support := by
    simpa [SourceStrategicHistory.traceDistFrom] using hsupport_one
  have hcount_step :
      cursor.source.history.current.cont.instrCount =
        sourceState.history.current.cont.instrCount + 1 :=
    SourceStrategicHistory.instrCount_stepKernel_support_of_not_terminal
      sourceProfile hsource_not_terminal hsupport_step
  have hlen_cursor :=
    SourceConfig.LabeledStar.length_add_instrCount
      cursor.source.history.run
  have hlen_cursor' :
      cursor.source.history.labels.length +
          cursor.source.history.current.cont.instrCount =
        program.core.prog.instrCount := by
    rw [cursor.source.start_eq] at hlen_cursor
    simpa [ToEventGraph.sourceStart] using hlen_cursor
  have hlen_source :=
    SourceConfig.LabeledStar.length_add_instrCount
      sourceState.history.run
  have hlen_source' :
      sourceState.history.labels.length +
          sourceState.history.current.cont.instrCount =
        program.core.prog.instrCount := by
    rw [sourceState.start_eq] at hlen_source
    simpa [ToEventGraph.sourceStart] using hlen_source
  have hsourceFuelSplit :
      sourceFuel = 1 + sourceFuelAfter := by
    simpa [hblock_one] using hblock.sourceFuel_split
  have hcursorBalance := hcursor.sourceFuel_balance
  omega

private theorem sourceCheckpoint_checkpointRound_support_fuel_balance
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel sourceBlockFuel
      sourceFuelAfter checkpointFuelAfter : Nat)
    (cursor : SourceCheckpointCursor program)
    (hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile sourceFuel checkpointFuel cursor)
    (hblock :
      SourceCheckpointCommitBlockFuel program cutoff sourceProfile
        checkpointProfile cursor sourceFuel checkpointFuel sourceBlockFuel
        sourceFuelAfter checkpointFuelAfter)
    {checkpointHistory : program.SourceCheckpointBehavioralHistory}
    (hsupport :
      checkpointHistory ∈
        (Machine.RoundView.BoundedHistory.runDistFrom
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon checkpointProfile 1
          cursor.checkpoint).support) :
    checkpointHistory.steps.length + checkpointFuelAfter =
      program.frontierSemantics.horizon := by
  have hlength :
      checkpointHistory.steps.length =
        cursor.checkpoint.steps.length + 1 :=
    boundedRunDistFrom_one_support_steps_length
      program.frontierSemantics.behavioral.view
      program.frontierSemantics.horizon checkpointProfile cursor.checkpoint
      hblock.checkpoint_nonterminal hsupport
  have hsplit := hblock.checkpointFuel_split
  have hbalance := hcursor.checkpointFuel_balance
  omega

/-- The next checkpoint round has an exact source-order block length.

This is a core obligation, not induction bookkeeping.  It must be proved from
Replay/source-completion facts: starting from a checkpoint-boundary cursor at a
nonterminal checkpoint state, there is a least positive source fuel that
finishes serializing the current frontier round and returns to a boundary
cursor. -/
theorem sourceCheckpointCommitBlockFuel_exists
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel : Nat)
    (cursor : SourceCheckpointCursor program)
    (hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile sourceFuel checkpointFuel cursor)
    (hboundary : cursor.residualActionLaw = none)
    (hcheckpoint_nonterminal :
      ¬ Machine.RoundView.boundedTerminal
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon cursor.checkpoint.lastState) :
    ∃ sourceBlockFuel sourceFuelAfter checkpointFuelAfter,
      SourceCheckpointCommitBlockFuel program cutoff sourceProfile
        checkpointProfile cursor sourceFuel checkpointFuel sourceBlockFuel
        sourceFuelAfter checkpointFuelAfter := by
  classical
  have hsource_not_terminal :
      ¬ cursor.source.history.current.IsTerminal := by
    intro hsource_terminal
    have hgraph_terminal :
        EventGraph.Terminal (ToEventGraph.compile program.core).graph
          cursor.replay.state.1 :=
      sourcePrefixReplay_graphTerminal_of_sourceTerminal
        program cursor.replay hsource_terminal
    have hcheckpoint_graph_terminal :
        EventGraph.Terminal (ToEventGraph.compile program.core).graph
          cursor.checkpoint.lastState.state.1 := by
      rw [hcursor.boundary_replay hboundary]
      exact hgraph_terminal
    exact hcheckpoint_nonterminal
      (Or.inl (by
        simpa [ToEventGraph.FrontierGameSemantics.behavioral,
          WFProgram.frontierSemantics, ToEventGraph.canonicalFrontierGameSemantics,
          EventGraph.frontierRoundView, EventGraph.PrimitiveMachineOf,
          ToEventGraph.primitiveMachineSpec,
          EventGraph.ToMachine.primitiveMachine] using
          hcheckpoint_graph_terminal))
  have hsourceFuel_count :
      sourceFuel = cursor.source.history.current.cont.instrCount := by
    have hlen :=
      SourceConfig.LabeledStar.length_add_instrCount
        cursor.source.history.run
    have hlen' :
        cursor.source.history.labels.length +
            cursor.source.history.current.cont.instrCount =
          program.core.prog.instrCount := by
      rw [cursor.source.start_eq] at hlen
      simpa [ToEventGraph.sourceStart] using hlen
    have hbalance := hcursor.sourceFuel_balance
    omega
  have hsourceFuel_pos : 0 < sourceFuel := by
    have hcount_ne :
        cursor.source.history.current.cont.instrCount ≠ 0 := by
      intro hzero
      exact hsource_not_terminal
        (SourceStrategicHistory.terminal_of_instrCount_eq_zero hzero)
    omega
  have hcheckpointFuel_pos : 0 < checkpointFuel := by
    by_contra hnot
    have hzero : checkpointFuel = 0 := Nat.eq_zero_of_not_pos hnot
    have hdepth :
        cursor.checkpoint.lastState.depth =
          cursor.checkpoint.steps.length :=
      Machine.RoundView.history_depth
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon cursor.checkpoint
    have hcut :
        program.frontierSemantics.horizon ≤
          cursor.checkpoint.lastState.depth := by
      have hbalance := hcursor.checkpointFuel_balance
      rw [hzero] at hbalance
      rw [hdepth]
      omega
    exact hcheckpoint_nonterminal (Or.inr hcut)
  refine ⟨1, sourceFuel - 1, checkpointFuel - 1, ?_⟩
  refine
    { boundary := hboundary
      sourceFuel_split := by omega
      checkpointFuel_split := by omega
      checkpoint_nonterminal := hcheckpoint_nonterminal
      source_boundary := ?_
      checkpoint_boundary := ?_
      source_minimal := ?_ }
  · intro sourceState hsupport
    have hsupport_step :
        sourceState ∈
          (SourceStrategicHistory.stepKernel sourceProfile
            cursor.source).support := by
      simpa [SourceStrategicHistory.traceDistFrom] using hsupport
    have hcount_step :
        cursor.source.history.current.cont.instrCount =
          sourceState.history.current.cont.instrCount + 1 :=
      SourceStrategicHistory.instrCount_stepKernel_support_of_not_terminal
        sourceProfile hsource_not_terminal hsupport_step
    have hlen_cursor :=
      SourceConfig.LabeledStar.length_add_instrCount
        cursor.source.history.run
    have hlen_cursor' :
        cursor.source.history.labels.length +
            cursor.source.history.current.cont.instrCount =
          program.core.prog.instrCount := by
      rw [cursor.source.start_eq] at hlen_cursor
      simpa [ToEventGraph.sourceStart] using hlen_cursor
    have hlen_source :=
      SourceConfig.LabeledStar.length_add_instrCount
        sourceState.history.run
    have hlen_source' :
        sourceState.history.labels.length +
            sourceState.history.current.cont.instrCount =
          program.core.prog.instrCount := by
      rw [sourceState.start_eq] at hlen_source
      simpa [ToEventGraph.sourceStart] using hlen_source
    rcases program.sourceStrategicHistory_prefixReplay sourceState with
      ⟨replay⟩
    refine ⟨by omega, ?_⟩
    let represented : SourceCheckpointCursor program :=
      { source := sourceState
        checkpoint := cursor.checkpoint
        replay := replay
        residualActionLaw := none }
    exact ⟨represented, rfl, rfl⟩
  · intro checkpointHistory hsupport
    have hsupport' :
        checkpointHistory ∈
          ((Machine.RoundView.legalActionLaw
              program.frontierSemantics.behavioral.view
              program.frontierSemantics.horizon checkpointProfile
              cursor.checkpoint hcheckpoint_nonterminal).bind fun action =>
            (Machine.RoundView.boundedTransition
              program.frontierSemantics.behavioral.view
              program.frontierSemantics.horizon cursor.checkpoint.lastState
              action).bind fun dst =>
              Machine.RoundView.BoundedHistory.runDistFrom
                program.frontierSemantics.behavioral.view
                program.frontierSemantics.horizon checkpointProfile 0
                (cursor.checkpoint.extendByOutcome action dst)).support := by
      simpa [Machine.RoundView.BoundedHistory.runDistFrom,
        hcheckpoint_nonterminal] using hsupport
    rw [PMF.mem_support_bind_iff] at hsupport'
    rcases hsupport' with ⟨action, _haction, hdstSupport⟩
    rw [PMF.mem_support_bind_iff] at hdstSupport
    rcases hdstSupport with ⟨dst, hdst, htail⟩
    have hdstMass :
        Machine.RoundView.boundedTransition
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon cursor.checkpoint.lastState
            action dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdst
    have hcheckpoint_eq :
        checkpointHistory =
          cursor.checkpoint.extendByOutcome action dst := by
      simpa [Machine.RoundView.BoundedHistory.runDistFrom,
        PMF.support_pure, Set.mem_singleton_iff] using htail
    subst checkpointHistory
    have hlen :
        cursor.checkpoint.steps.length <
          (cursor.checkpoint.extendByOutcome action dst).steps.length := by
      rw [Machine.RoundView.BoundedHistory.extendByOutcome_of_support
        cursor.checkpoint action dst hdstMass]
      simp [Machine.RoundView.BoundedHistory.snoc]
    refine ⟨hlen, ?_⟩
    let represented : SourceCheckpointCursor program :=
      { source := cursor.source
        checkpoint := cursor.checkpoint.extendByOutcome action dst
        replay := cursor.replay
        residualActionLaw := none }
    exact ⟨represented, rfl, rfl⟩
  · intro shorter hshorter hboundary_short
    have hzero : shorter = 0 := by omega
    subst shorter
    have hself :
        cursor.source ∈
          (SourceStrategicHistory.traceDistFrom
            (L := L) sourceProfile 0 cursor.source).support := by
      simp [SourceStrategicHistory.traceDistFrom]
    have hbad := hboundary_short cursor.source hself
    exact (Nat.lt_irrefl _ hbad.1)

/-- One checkpoint round, viewed at a cursor boundary, couples to exactly one
source-order block.

This is intentionally kernel-level, not an observed-outcome statement.  The
global adequacy induction consumes this coupling, then recursively pushes the
remaining source/checkpoint fuels through the successor cursors. -/
theorem sourceCheckpointCommitBlockCoupling
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel sourceBlockFuel
      sourceFuelAfter checkpointFuelAfter : Nat)
    (cursor : SourceCheckpointCursor program)
    (hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile sourceFuel checkpointFuel cursor)
    (hblock :
      SourceCheckpointCommitBlockFuel program cutoff sourceProfile
        checkpointProfile cursor sourceFuel checkpointFuel sourceBlockFuel
        sourceFuelAfter checkpointFuelAfter)
    (_hadequate :
      ∀ who,
        SourceCheckpointStrategyAdequate program
          program.core.prog.instrCount cutoff who
          (sourceProfile who) (checkpointProfile who)) :
    Nonempty
      (Math.Coupling.HasCoupling
        (SourceCheckpointSuccessorRelated program cutoff sourceProfile
          checkpointProfile sourceFuelAfter checkpointFuelAfter)
        (SourceStrategicHistory.traceDistFrom
          (L := L) sourceProfile sourceBlockFuel cursor.source)
        (Machine.RoundView.BoundedHistory.runDistFrom
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon checkpointProfile 1
          cursor.checkpoint)) := by
  classical
  refine ⟨couplingOfSupportRelation _ _ _ ?_⟩
  intro sourceState hsourceSupport checkpointHistory hcheckpointSupport
  rcases hblock.source_boundary sourceState hsourceSupport with
    ⟨hsourceAdvanced, sourceCursor, hsourceEq, hsourceBoundary⟩
  rcases hblock.checkpoint_boundary checkpointHistory hcheckpointSupport with
    ⟨hcheckpointAdvanced, checkpointCursor, hcheckpointEq,
      hcheckpointBoundary⟩
  subst sourceState
  subst checkpointHistory
  let nextCursor : SourceCheckpointCursor program :=
    { source := sourceCursor.source
      checkpoint := checkpointCursor.checkpoint
      replay := sourceCursor.replay
      residualActionLaw := none }
  refine ⟨nextCursor, rfl, rfl, ?_, rfl⟩
  sorry

/-- Terminal cursor case for the generalized adequacy induction. -/
theorem sourceCheckpointTerminalCursorLaw
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel : Nat)
    (cursor : SourceCheckpointCursor program)
    (hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile sourceFuel checkpointFuel cursor)
    (hboundary : cursor.residualActionLaw = none)
    (hcheckpoint_terminal :
      Machine.RoundView.boundedTerminal
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon cursor.checkpoint.lastState) :
    PMF.map (fun state => state.history.current.outcome?)
      (SourceStrategicHistory.traceDistFrom
        (L := L) sourceProfile sourceFuel cursor.source) =
    PMF.map (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        (Machine.RoundView.BoundedHistory.runDistFrom
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon checkpointProfile checkpointFuel
          cursor.checkpoint) := by
  rcases hcursor.terminal_alignment hboundary hcheckpoint_terminal with
    ⟨hsource_terminal, houtcome⟩
  rw [SourceStrategicHistory.traceDistFrom_terminal sourceProfile sourceFuel
    cursor.source hsource_terminal]
  rw [Machine.RoundView.BoundedHistory.runDistFrom_terminal
    program.frontierSemantics.behavioral.view
    program.frontierSemantics.horizon checkpointProfile checkpointFuel
    cursor.checkpoint hcheckpoint_terminal]
  have hsourceMap :
      PMF.map (fun state => state.history.current.outcome?)
          (PMF.pure cursor.source) =
        PMF.pure cursor.source.history.current.outcome? :=
    PMF.pure_map (fun state => state.history.current.outcome?) cursor.source
  have hcheckpointMap :
      PMF.map (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
          (PMF.pure cursor.checkpoint) =
        PMF.pure
          (ToEventGraph.sourceOutcomeOptionAtHistory program.core
            cursor.checkpoint) :=
    PMF.pure_map (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
      cursor.checkpoint
  exact hsourceMap.trans ((congrArg PMF.pure houtcome).trans hcheckpointMap.symm)

/-- Generalized source/checkpoint adequacy invariant over corresponding
mid-trace cursors.

This is the statement the proof should induct on.  The public
`sourceCheckpointAdequacy` is the initial-cursor instance at source horizon
`instrCount` and checkpoint horizon `program.frontierSemantics.horizon`; the
deviation totality fields should remain thin wrappers around that public
theorem. -/
theorem sourceCheckpointAdequacyFromCursor
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (sourceFuel checkpointFuel : Nat)
    (cursor : SourceCheckpointCursor program)
    (hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile sourceFuel checkpointFuel cursor)
    (hboundary : cursor.residualActionLaw = none)
    (hadequate :
      ∀ who,
        SourceCheckpointStrategyAdequate program
          program.core.prog.instrCount cutoff who
          (sourceProfile who) (checkpointProfile who)) :
    PMF.map (fun state => state.history.current.outcome?)
        (SourceStrategicHistory.traceDistFrom
          (L := L) sourceProfile sourceFuel cursor.source) =
      PMF.map (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        (Machine.RoundView.BoundedHistory.runDistFrom
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon checkpointProfile checkpointFuel
          cursor.checkpoint) := by
  classical
  induction checkpointFuel generalizing sourceFuel cursor with
  | zero =>
      by_cases hterminal :
        Machine.RoundView.boundedTerminal
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon cursor.checkpoint.lastState
      · exact
          program.sourceCheckpointTerminalCursorLaw cutoff sourceProfile
            checkpointProfile sourceFuel 0 cursor hcursor hboundary hterminal
      · obtain ⟨sourceBlockFuel, sourceFuelAfter, checkpointFuelAfter,
            hblock⟩ :=
          program.sourceCheckpointCommitBlockFuel_exists cutoff sourceProfile
            checkpointProfile sourceFuel 0 cursor hcursor hboundary hterminal
        have hsplit : 0 = checkpointFuelAfter + 1 :=
          hblock.checkpointFuel_split
        omega
  | succ checkpointFuel ih =>
      by_cases hterminal :
        Machine.RoundView.boundedTerminal
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon cursor.checkpoint.lastState
      · exact
          program.sourceCheckpointTerminalCursorLaw cutoff sourceProfile
            checkpointProfile sourceFuel (checkpointFuel + 1) cursor hcursor
            hboundary hterminal
      · obtain ⟨sourceBlockFuel, sourceFuelAfter, checkpointFuelAfter,
            hblock⟩ :=
          program.sourceCheckpointCommitBlockFuel_exists cutoff sourceProfile
            checkpointProfile sourceFuel (checkpointFuel + 1) cursor hcursor
            hboundary hterminal
        have hcheckpointFuelAfter :
            checkpointFuelAfter = checkpointFuel := by
          have hsplit :
              checkpointFuel + 1 = checkpointFuelAfter + 1 :=
            hblock.checkpointFuel_split
          omega
        subst checkpointFuelAfter
        have hcoupling :
            Nonempty
              (Math.Coupling.HasCoupling
                (SourceCheckpointSuccessorRelated program cutoff sourceProfile
                  checkpointProfile sourceFuelAfter checkpointFuel)
                (SourceStrategicHistory.traceDistFrom
                  (L := L) sourceProfile sourceBlockFuel cursor.source)
                (Machine.RoundView.BoundedHistory.runDistFrom
                  program.frontierSemantics.behavioral.view
                  program.frontierSemantics.horizon checkpointProfile 1
                  cursor.checkpoint)) :=
          program.sourceCheckpointCommitBlockCoupling cutoff sourceProfile
            checkpointProfile sourceFuel (checkpointFuel + 1) sourceBlockFuel
            sourceFuelAfter checkpointFuel cursor hcursor hblock hadequate
        have hsourceSplit :
            (SourceStrategicHistory.traceDistFrom
              (L := L) sourceProfile sourceBlockFuel cursor.source).bind
                (SourceStrategicHistory.traceDistFrom
                  (L := L) sourceProfile sourceFuelAfter) =
              SourceStrategicHistory.traceDistFrom
                (L := L) sourceProfile sourceFuel cursor.source := by
          rw [SourceStrategicHistory.traceDistFrom_bind_traceDistFrom]
          rw [← hblock.sourceFuel_split]
        have hcheckpointSplit :
            (Machine.RoundView.BoundedHistory.runDistFrom
              program.frontierSemantics.behavioral.view
              program.frontierSemantics.horizon checkpointProfile 1
              cursor.checkpoint).bind
                (fun checkpointHistory =>
                  Machine.RoundView.BoundedHistory.runDistFrom
                    program.frontierSemantics.behavioral.view
                    program.frontierSemantics.horizon checkpointProfile
                    checkpointFuel checkpointHistory) =
              Machine.RoundView.BoundedHistory.runDistFrom
                program.frontierSemantics.behavioral.view
                program.frontierSemantics.horizon checkpointProfile
                (checkpointFuel + 1) cursor.checkpoint := by
          rw [Machine.RoundView.BoundedHistory.runDistFrom_bind_runDistFrom]
          rw [Nat.add_comm 1 checkpointFuel]
        have hbind :
            (SourceStrategicHistory.traceDistFrom
              (L := L) sourceProfile sourceBlockFuel cursor.source).bind
                (fun sourceState =>
                  PMF.map (fun state => state.history.current.outcome?)
                    (SourceStrategicHistory.traceDistFrom
                      (L := L) sourceProfile sourceFuelAfter sourceState)) =
              (Machine.RoundView.BoundedHistory.runDistFrom
                program.frontierSemantics.behavioral.view
                program.frontierSemantics.horizon checkpointProfile 1
                cursor.checkpoint).bind
                (fun checkpointHistory =>
                  PMF.map
                    (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
                    (Machine.RoundView.BoundedHistory.runDistFrom
                      program.frontierSemantics.behavioral.view
                      program.frontierSemantics.horizon checkpointProfile
                      checkpointFuel checkpointHistory)) := by
          exact
            Math.Coupling.HasCoupling.bind_eq_of_nonempty_rel hcoupling
              (fun sourceState =>
                PMF.map (fun state => state.history.current.outcome?)
                  (SourceStrategicHistory.traceDistFrom
                    (L := L) sourceProfile sourceFuelAfter sourceState))
              (fun checkpointHistory =>
                PMF.map
                  (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
                  (Machine.RoundView.BoundedHistory.runDistFrom
                    program.frontierSemantics.behavioral.view
                    program.frontierSemantics.horizon checkpointProfile
                    checkpointFuel checkpointHistory))
              (by
                intro sourceState checkpointHistory hrelated
                rcases hrelated with
                  ⟨nextCursor, hsource, hcheckpoint, hnextCursor,
                    hnextBoundary⟩
                subst sourceState
                subst checkpointHistory
                exact ih sourceFuelAfter nextCursor hnextCursor hnextBoundary)
        calc
          PMF.map (fun state => state.history.current.outcome?)
              (SourceStrategicHistory.traceDistFrom
                (L := L) sourceProfile sourceFuel cursor.source)
            = PMF.map (fun state => state.history.current.outcome?)
                ((SourceStrategicHistory.traceDistFrom
                  (L := L) sourceProfile sourceBlockFuel cursor.source).bind
                    (SourceStrategicHistory.traceDistFrom
                      (L := L) sourceProfile sourceFuelAfter)) := by
                rw [hsourceSplit]
          _ =
              (SourceStrategicHistory.traceDistFrom
                (L := L) sourceProfile sourceBlockFuel cursor.source).bind
                (fun sourceState =>
                  PMF.map (fun state => state.history.current.outcome?)
                    (SourceStrategicHistory.traceDistFrom
                      (L := L) sourceProfile sourceFuelAfter sourceState)) := by
                rw [PMF.map_bind]
          _ =
              (Machine.RoundView.BoundedHistory.runDistFrom
                program.frontierSemantics.behavioral.view
                program.frontierSemantics.horizon checkpointProfile 1
                cursor.checkpoint).bind
                (fun checkpointHistory =>
                  PMF.map
                    (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
                    (Machine.RoundView.BoundedHistory.runDistFrom
                      program.frontierSemantics.behavioral.view
                      program.frontierSemantics.horizon checkpointProfile
                      checkpointFuel checkpointHistory)) := hbind
          _ = PMF.map
              (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
              ((Machine.RoundView.BoundedHistory.runDistFrom
                program.frontierSemantics.behavioral.view
                program.frontierSemantics.horizon checkpointProfile 1
                cursor.checkpoint).bind
                (fun checkpointHistory =>
                  Machine.RoundView.BoundedHistory.runDistFrom
                    program.frontierSemantics.behavioral.view
                    program.frontierSemantics.horizon checkpointProfile
                    checkpointFuel checkpointHistory)) := by
                rw [PMF.map_bind]
          _ = PMF.map
              (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
              (Machine.RoundView.BoundedHistory.runDistFrom
                program.frontierSemantics.behavioral.view
                program.frontierSemantics.horizon checkpointProfile
                (checkpointFuel + 1) cursor.checkpoint) := by
                exact
                  congrArg
                    (PMF.map
                      (ToEventGraph.sourceOutcomeOptionAtHistory program.core))
                    hcheckpointSplit

/-- Central whole-kernel source/checkpoint adequacy theorem.

At the completed source horizon, any pointwise adequate source/checkpoint
profile pair induces the same observed optional source-outcome law.  The proof
is the stuttering simulation: serialize a checkpoint round into source-order
commits, close internal frontier work, and induct over the checkpoint horizon. -/
theorem sourceCheckpointAdequacy
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile)
    (hadequate :
      ∀ who,
        SourceCheckpointStrategyAdequate program
          program.core.prog.instrCount cutoff who
          (sourceProfile who) (checkpointProfile who)) :
    (program.sourceStrategicOptionOutcomeView
        program.core.prog.instrCount cutoff).law sourceProfile =
      program.sourceCheckpointOptionOutcomeView.law checkpointProfile := by
  classical
  let cursor := program.sourceCheckpointInitialCursor
  have hcursor :
      SourceCheckpointCursorInvariant program cutoff sourceProfile
        checkpointProfile program.core.prog.instrCount
        program.frontierSemantics.horizon cursor := by
    refine
      { sourceFuel_balance := ?_
        checkpointFuel_balance := ?_
        boundary_replay := ?_
        terminal_alignment := ?_
        fallback_unreachable := ?_ }
    · simp [cursor, sourceCheckpointInitialCursor,
        SourceStrategicHistory.initial, SourceHistoryPoint.refl]
    · simp [cursor, sourceCheckpointInitialCursor]
    · intro _hboundary
      rfl
    · intro _hboundary hterminal
      have hzero : program.core.prog.instrCount = 0 := by
        rcases hterminal with hmachine | hcutoff
        · have hnodeCount :
              (ToEventGraph.compile program.core).graph.nodeCount = 0 := by
            by_contra hne
            have hpos :
                0 < (ToEventGraph.compile program.core).graph.nodeCount :=
              Nat.pos_of_ne_zero hne
            let node : Fin (ToEventGraph.compile program.core).graph.nodeCount :=
              ⟨0, hpos⟩
            have hdone := hmachine node
            have hfalse : node ∈
                (∅ :
                  Finset (Fin (ToEventGraph.compile program.core).graph.nodeCount)) := by
              simpa [EventGraph.Config.initial,
                Machine.BoundedState.init, cursor,
                sourceCheckpointInitialCursor,
                Machine.RoundView.BoundedHistory.lastState,
                Machine.RoundView.lastStateFrom,
                sourceCheckpointInitialReplay,
                ToEventGraph.compile,
                EventGraph.ToMachine.primitiveMachine] using hdone
            simp at hfalse
          have hcompiled :=
            ToEventGraph.compile_graph_nodeCount program.core
          omega
        · have hhorizon :
              program.frontierSemantics.horizon = program.core.prog.instrCount := by
            simpa [ToEventGraph.FrontierGameSemantics.horizon,
              ToEventGraph.completionBound] using
              ToEventGraph.compile_graph_nodeCount program.core
          have hdepth :
              cursor.checkpoint.lastState.depth = 0 := by
            simp [cursor, sourceCheckpointInitialCursor]
          omega
      have hsource_terminal :
          cursor.source.history.current.IsTerminal := by
        simpa [cursor, sourceCheckpointInitialCursor,
          ToEventGraph.sourceStart] using
          SourceStrategicHistory.terminal_of_instrCount_eq_zero
            (L := L) (P := P) hzero
      refine ⟨hsource_terminal, ?_⟩
      rcases hsource_terminal with ⟨payoffs, hret⟩
      have hprogRet : program.core.prog = .ret payoffs := by
        simpa [cursor, sourceCheckpointInitialCursor,
          SourceStrategicHistory.initial, SourceHistoryPoint.refl,
          ToEventGraph.sourceStart] using hret
      simpa [cursor, sourceCheckpointInitialCursor,
        SourceStrategicHistory.initial, SourceHistoryPoint.refl] using
        program.sourceCheckpointInitialOutcome_ret payoffs hprogRet
    · intro sourceState hsupport who hchoice
      have hterminal :
          sourceState.history.current.IsTerminal :=
        SourceStrategicHistory.traceDistFrom_support_terminal_of_instrCount_le
          sourceProfile program.core.prog.instrCount cursor.source sourceState
          (by
            simpa [cursor, sourceCheckpointInitialCursor] using hsupport)
          (by
            simp [cursor, sourceCheckpointInitialCursor,
              SourceStrategicHistory.initial, SourceHistoryPoint.refl,
              ToEventGraph.sourceStart])
      have hchoiceCurrent :
          sourceState.history.current.IsChoiceFor who := by
        simpa [SourceHistoryPoint.IsChoiceFor] using hchoice
      rcases hterminal with ⟨payoffs, hret⟩
      unfold SourceConfig.IsChoiceFor SourceConfig.activePlayer?
        SourceConfig.programPoint at hchoiceCurrent
      rw [hret] at hchoiceCurrent
      simp [SourceProgramPoint.kind,
        SourceProgramPoint.activePlayer?] at hchoiceCurrent
  have hcursorLaw :=
    program.sourceCheckpointAdequacyFromCursor cutoff sourceProfile
      checkpointProfile program.core.prog.instrCount
      program.frontierSemantics.horizon cursor hcursor rfl hadequate
  change
    PMF.map (fun state => state.history.current.outcome?)
        (SourceStrategicHistory.traceDistFrom sourceProfile
          program.core.prog.instrCount
          (SourceStrategicHistory.initial (L := L)
            (ToEventGraph.sourceStart program.core)
            program.core.normalized)) =
      PMF.map id
        (PMF.map
          (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
          (Machine.RoundView.BoundedHistory.runDistFrom
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon checkpointProfile
            program.frontierSemantics.horizon
            (Machine.RoundView.BoundedHistory.nil
              program.frontierSemantics.behavioral.view
              program.frontierSemantics.horizon)))
  rw [PMF.map_id]
  exact hcursorLaw

/-! ### Profile realizations and totalities. -/

/-- Realize a source profile as a checkpoint behavioral profile. -/
noncomputable def sourceToCheckpointProfile
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (sourceProfile :
      (program.sourceStrategicGame horizon cutoff).Profile) :
    program.sourceCheckpointBehavioralGame.Profile :=
  fun who =>
    program.sourceToCheckpointStrategy horizon cutoff who
      (sourceProfile who)

/-- Realize a checkpoint behavioral profile as a source profile.  This is where
the frontier→source per-node machinery (`currentSourceCommitValueLaw`,
`legalActionLaw_disintegrate`, the conditioned-query laws) is assembled into a
full `SourceStrategy` for each player. -/
noncomputable def checkpointToSourceProfile
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P)
    (checkpointProfile : program.sourceCheckpointBehavioralGame.Profile) :
    (program.sourceStrategicGame horizon cutoff).Profile :=
  fun who =>
    program.checkpointToSourceStrategy horizon cutoff who
      (checkpointProfile who)

/-- Every source profile is deviation-related to its canonical checkpoint
realization (at the source-instruction-count horizon, where source support is
terminal). -/
theorem sourceCheckpoint_source_total
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P) :
    ∀ sourceProfile :
      (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile,
      ∃ checkpointProfile : program.sourceCheckpointBehavioralGame.Profile,
        SourceCheckpointDeviationRelated program
          program.core.prog.instrCount cutoff sourceProfile checkpointProfile := by
  intro sourceProfile
  refine
    ⟨program.sourceToCheckpointProfile program.core.prog.instrCount cutoff
        sourceProfile,
      ?baseLaw, ?targetLift, ?sourceLift⟩
  · -- baseLaw: observed-law equality at the canonical checkpoint realization
    exact
      program.sourceCheckpointAdequacy cutoff sourceProfile
        (program.sourceToCheckpointProfile program.core.prog.instrCount cutoff
          sourceProfile)
        (by
          intro who
          exact Or.inl rfl)
  · -- targetLift: checkpoint→source deviation (reuse per-node law machinery)
    intro who checkpointDeviation
    refine
      ⟨program.checkpointToSourceStrategy program.core.prog.instrCount cutoff
          who checkpointDeviation,
        ?_⟩
    exact
      program.sourceCheckpointAdequacy cutoff
        (Function.update sourceProfile who
          (program.checkpointToSourceStrategy
            program.core.prog.instrCount cutoff who checkpointDeviation))
        (Function.update
          (program.sourceToCheckpointProfile program.core.prog.instrCount cutoff
            sourceProfile)
          who checkpointDeviation)
        (by
          intro player
          by_cases hplayer : player = who
          · subst player
            simp [SourceCheckpointStrategyAdequate]
          · simp [SourceCheckpointStrategyAdequate,
              sourceToCheckpointProfile, Function.update, hplayer])
  · -- sourceLift: source→checkpoint deviation (assemble a legal round-action;
    -- the load-bearing new construction)
    intro who sourceDeviation
    refine
      ⟨program.sourceToCheckpointStrategy program.core.prog.instrCount cutoff
          who sourceDeviation,
        ?_⟩
    exact
      program.sourceCheckpointAdequacy cutoff
        (Function.update sourceProfile who sourceDeviation)
        (Function.update
          (program.sourceToCheckpointProfile program.core.prog.instrCount cutoff
            sourceProfile)
          who
          (program.sourceToCheckpointStrategy
            program.core.prog.instrCount cutoff who sourceDeviation))
        (by
          intro player
          by_cases hplayer : player = who
          · subst player
            simp [SourceCheckpointStrategyAdequate,
              Function.update]
          · simp [SourceCheckpointStrategyAdequate,
              sourceToCheckpointProfile, Function.update, hplayer])

/-- Every checkpoint behavioral profile is deviation-related to a source
realization. -/
theorem sourceCheckpoint_checkpoint_total
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P) :
    ∀ checkpointProfile : program.sourceCheckpointBehavioralGame.Profile,
      ∃ sourceProfile :
        (program.sourceStrategicGame program.core.prog.instrCount cutoff).Profile,
        SourceCheckpointDeviationRelated program
          program.core.prog.instrCount cutoff sourceProfile checkpointProfile := by
  intro checkpointProfile
  refine
    ⟨program.checkpointToSourceProfile program.core.prog.instrCount cutoff
        checkpointProfile,
      ?baseLaw, ?targetLift, ?sourceLift⟩
  · -- baseLaw
    exact
      program.sourceCheckpointAdequacy cutoff
        (program.checkpointToSourceProfile program.core.prog.instrCount cutoff
          checkpointProfile)
        checkpointProfile
        (by
          intro who
          exact Or.inr rfl)
  · -- targetLift
    intro who checkpointDeviation
    refine
      ⟨program.checkpointToSourceStrategy program.core.prog.instrCount cutoff
          who checkpointDeviation,
        ?_⟩
    exact
      program.sourceCheckpointAdequacy cutoff
        (Function.update
          (program.checkpointToSourceProfile program.core.prog.instrCount cutoff
            checkpointProfile)
          who
          (program.checkpointToSourceStrategy
            program.core.prog.instrCount cutoff who checkpointDeviation))
        (Function.update checkpointProfile who checkpointDeviation)
        (by
          intro player
          by_cases hplayer : player = who
          · subst player
            simp [SourceCheckpointStrategyAdequate,
              Function.update]
          · simp [SourceCheckpointStrategyAdequate,
              checkpointToSourceProfile, Function.update, hplayer])
  · -- sourceLift
    intro who sourceDeviation
    refine
      ⟨program.sourceToCheckpointStrategy program.core.prog.instrCount cutoff
          who sourceDeviation,
        ?_⟩
    exact
      program.sourceCheckpointAdequacy cutoff
        (Function.update
          (program.checkpointToSourceProfile program.core.prog.instrCount cutoff
            checkpointProfile)
          who sourceDeviation)
        (Function.update checkpointProfile who
          (program.sourceToCheckpointStrategy
            program.core.prog.instrCount cutoff who sourceDeviation))
        (by
          intro player
          by_cases hplayer : player = who
          · subst player
            simp [SourceCheckpointStrategyAdequate]
          · simp [SourceCheckpointStrategyAdequate,
              checkpointToSourceProfile, Function.update, hplayer])

/-- Final non-vacuous source/frontier Nash-deviation bisimulation, obtained by
composing the middle bridge with the proven checkpoint↔frontier bridge. -/
noncomputable def sourceFrontierNashDeviationBisimulationViaCheckpoint
    (program : WFProgram P L) [FiniteDomains program] (cutoff : Payoff P) :
    SourceFrontierNashDeviationBisimulation
      program program.core.prog.instrCount cutoff where
  bisimulation :=
    KernelGame.NashDeviationBisimulation.comp
      program.sourceCheckpointBehavioralFrontierNashDeviationBisimulation
      (program.sourceCheckpointNashDeviationBisimulation
        program.core.prog.instrCount cutoff)
      (fun _ => rfl)
  source_view_eq := rfl
  frontier_view_eq := rfl
  source_total := by
    intro sourceProfile
    obtain ⟨checkpointProfile, hrel⟩ :=
      program.sourceCheckpoint_source_total cutoff sourceProfile
    exact ⟨checkpointProfile, checkpointProfile, hrel, rfl⟩
  frontier_total := by
    intro frontierProfile
    obtain ⟨sourceProfile, hrel⟩ :=
      program.sourceCheckpoint_checkpoint_total cutoff frontierProfile
    exact ⟨sourceProfile, frontierProfile, hrel, rfl⟩

end WFProgram

end Vegas
