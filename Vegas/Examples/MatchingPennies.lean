import Vegas.Examples.DependencySemantics

/-!
# Matching Pennies

Build-tested checked-program examples for the canonical frontier EventGraph
semantics.
-/

namespace Vegas
namespace Examples

open GameTheory
open ToEventGraph

def matchingPenniesSame :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .bool :=
  .eq (.var 2 (.there .here)) (.var 3 .here)

def matchingPenniesAlicePayoff :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .int :=
  .ite matchingPenniesSame (.constInt 1) (.constInt (-1))

def matchingPenniesBobPayoff :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .int :=
  .ite matchingPenniesSame (.constInt (-1)) (.constInt 1)

def matchingPenniesPayoffEnv (alice bob : Bool) :
    Env simpleExpr.Val [(3, BaseTy.bool), (2, BaseTy.bool)] :=
  Env.cons (x := 3) bob
    (Env.cons (x := 2) alice (Env.empty simpleExpr.Val))

theorem matchingPennies_payoffs_zero_sum (alice bob : Bool) :
    evalExpr matchingPenniesAlicePayoff
        (matchingPenniesPayoffEnv alice bob) +
      evalExpr matchingPenniesBobPayoff
        (matchingPenniesPayoffEnv alice bob) = 0 := by
  cases alice <;> cases bob <;> rfl

/-- Complete payoff table of the source-level Boolean choices. -/
theorem matchingPennies_payoff_table (alice bob : Bool) :
    (evalExpr matchingPenniesAlicePayoff
        (matchingPenniesPayoffEnv alice bob),
      evalExpr matchingPenniesBobPayoff
        (matchingPenniesPayoffEnv alice bob)) =
      match alice, bob with
      | true, true => (1, -1)
      | true, false => (-1, 1)
      | false, true => (-1, 1)
      | false, false => (1, -1) := by
  cases alice <;> cases bob <;> rfl

theorem bob_switch_from_match_gt (choice : Bool) :
    evalExpr matchingPenniesBobPayoff
        (matchingPenniesPayoffEnv choice (!choice)) >
      evalExpr matchingPenniesBobPayoff
        (matchingPenniesPayoffEnv choice choice) := by
  cases choice <;> decide

theorem alice_switch_from_mismatch_gt
    (alice bob : Bool) (h : alice ≠ bob) :
    evalExpr matchingPenniesAlicePayoff
        (matchingPenniesPayoffEnv bob bob) >
      evalExpr matchingPenniesAlicePayoff
        (matchingPenniesPayoffEnv alice bob) := by
  cases alice <;> cases bob <;> simp at h <;> decide

abbrev MatchingPenniesActionProfile := Player → Bool

def matchingPenniesActionPayoff
    (σ : MatchingPenniesActionProfile) : Player → Int
  | Player.alice =>
      evalExpr matchingPenniesAlicePayoff
        (matchingPenniesPayoffEnv (σ Player.alice) (σ Player.bob))
  | Player.bob =>
      evalExpr matchingPenniesBobPayoff
        (matchingPenniesPayoffEnv (σ Player.alice) (σ Player.bob))

def MatchingPennies.IsActionNash
    (σ : MatchingPenniesActionProfile) : Prop :=
  ∀ who alt, matchingPenniesActionPayoff σ who ≥
    matchingPenniesActionPayoff (Function.update σ who alt) who

theorem matchingPennies_no_actionNash
    (σ : MatchingPenniesActionProfile) :
    ¬ MatchingPennies.IsActionNash σ := by
  intro hσ
  by_cases hmatch : σ Player.alice = σ Player.bob
  · have hdev := hσ Player.bob (!(σ Player.bob))
    have hbad :
        evalExpr matchingPenniesBobPayoff
            (matchingPenniesPayoffEnv
              (σ Player.alice) (!(σ Player.bob))) ≤
          evalExpr matchingPenniesBobPayoff
            (matchingPenniesPayoffEnv
              (σ Player.alice) (σ Player.bob)) := by
      simpa [matchingPenniesActionPayoff, hmatch] using hdev
    exact
      (not_le_of_gt
        (by
          simpa [hmatch] using
            bob_switch_from_match_gt (σ Player.bob))) hbad
  · have hdev := hσ Player.alice (σ Player.bob)
    have hbad :
        evalExpr matchingPenniesAlicePayoff
            (matchingPenniesPayoffEnv
              (σ Player.bob) (σ Player.bob)) ≤
          evalExpr matchingPenniesAlicePayoff
            (matchingPenniesPayoffEnv
              (σ Player.alice) (σ Player.bob)) := by
      simpa [matchingPenniesActionPayoff] using hdev
    exact
      (not_le_of_gt
        (alice_switch_from_mismatch_gt
          (σ Player.alice) (σ Player.bob) hmatch)) hbad

/-- Matching Pennies as a sealed simultaneous-move protocol:
Alice commits, Bob commits without seeing Alice's choice, then both choices
are revealed publicly before payoffs are computed. -/
def matchingPenniesCore : VegasCore Player L [] :=
  .commit 0 .alice (trueGuard (x := 0))
    (.commit 1 .bob (trueGuard (x := 1))
      (.reveal 2 .alice 0 (.there .here)
        (.reveal 3 .bob 1 (.there .here)
          (.ret
            [(.alice, matchingPenniesAlicePayoff),
             (.bob, matchingPenniesBobPayoff)]))))

noncomputable def matchingPenniesProgram : GraphProgram Player L where
  Γ := []
  prog := matchingPenniesCore
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    simp [matchingPenniesCore, FreshBindings, Fresh]
  normalized := by
    simp [matchingPenniesCore, NormalizedDists]

noncomputable def matchingPenniesChecked : WFProgram Player L where
  core := matchingPenniesProgram
  reveals := by
    decide
  legal := by
    constructor
    · intro _env
      exact ⟨true, rfl⟩
    · constructor
      · intro _env
        exact ⟨true, rfl⟩
      · trivial

noncomputable instance matchingPenniesFiniteDomains :
    FiniteDomains matchingPenniesChecked where
  context := inferInstanceAs (FiniteVCtx ([] : VCtx Player L))
  program :=
    { proof :=
        .commit inferInstance
          (.commit inferInstance
            (.reveal inferInstance
              (.reveal inferInstance .ret))) }

noncomputable def matchingPenniesCompiled : CompiledProgram Player L :=
  compile matchingPenniesProgram

noncomputable def matchingPenniesFrontierGame :
    CompletedFrontierPureKernelGame (compile matchingPenniesChecked.core)
      (frontierPresentation
        (compile matchingPenniesChecked.core)
        (compile_guardLive matchingPenniesChecked)) :=
  canonicalFrontierPureKernelGame matchingPenniesChecked

noncomputable def matchingPenniesBehavioralFrontierGame :
    CompletedFrontierBehavioralKernelGame
      (compile matchingPenniesChecked.core)
      (frontierPresentation
        (compile matchingPenniesChecked.core)
        (compile_guardLive matchingPenniesChecked)) :=
  canonicalFrontierBehavioralKernelGame matchingPenniesChecked

noncomputable def matchingPenniesKuhnGames :
    CompletedFrontierKuhnGames (compile matchingPenniesChecked.core)
      (frontierPresentation
        (compile matchingPenniesChecked.core)
        (compile_guardLive matchingPenniesChecked)) :=
  canonicalFrontierKuhnGames matchingPenniesChecked

noncomputable def matchingPenniesSemantics :
    FrontierGameSemantics matchingPenniesChecked :=
  canonicalFrontierGameSemantics matchingPenniesChecked

theorem matchingPennies_mixedPureToBehavioral_realizable :
    MixedPureToBehavioralOutcomeKernelRealizable matchingPenniesChecked :=
  MixedPureToBehavioralOutcomeKernelRealizable.canonical
    matchingPenniesChecked

theorem matchingPenniesKuhnMenus :
    matchingPenniesKuhnGames.view.MenusObservable
      (completionBound matchingPenniesCompiled) := by
  exact canonicalFrontierKuhnGames_menusObservable matchingPenniesChecked

example : MixedPureToBehavioralOutcomeKernelRealizable matchingPenniesChecked :=
  matchingPennies_mixedPureToBehavioral_realizable

example
    (adapterBehavioral :
      (matchingPenniesKuhnGames.view.kuhnModel
        (completionBound matchingPenniesCompiled)
        matchingPenniesKuhnMenus).BehavioralProfile) :
    ∃ correlated : PMF matchingPenniesKuhnGames.pure.game.Profile,
      matchingPenniesKuhnGames.behavioral.game.outcomeKernel
          (by
            exact
              matchingPenniesKuhnGames.view.behavioralProfileOfKuhn
                (completionBound matchingPenniesCompiled)
                matchingPenniesKuhnMenus adapterBehavioral) =
        correlated.bind fun pureProfile =>
          matchingPenniesKuhnGames.pure.game.outcomeKernel pureProfile :=
  matchingPenniesKuhnGames.adapterBehavioralToCorrelatedPureOutcomeKernel
    matchingPenniesKuhnMenus adapterBehavioral

example
    (behavioralProfile : matchingPenniesKuhnGames.behavioral.game.Profile) :
    ∃ correlated : PMF matchingPenniesKuhnGames.pure.game.Profile,
      matchingPenniesKuhnGames.behavioral.game.outcomeKernel
          behavioralProfile =
        correlated.bind fun pureProfile =>
          matchingPenniesKuhnGames.pure.game.outcomeKernel pureProfile :=
  matchingPenniesKuhnGames.behavioralToCorrelatedPureOutcomeKernel
    matchingPenniesKuhnMenus behavioralProfile

theorem matchingPennies_behavioralToCorrelatedPure
    (behavioralProfile :
      ((canonicalFrontierKuhnGames matchingPenniesChecked).behavioral.game).Profile) :
    ∃ correlated :
        PMF ((canonicalFrontierKuhnGames matchingPenniesChecked).pure.game).Profile,
      ((canonicalFrontierKuhnGames matchingPenniesChecked).behavioral.game).outcomeKernel
          behavioralProfile =
        correlated.bind fun pureProfile =>
          ((canonicalFrontierKuhnGames matchingPenniesChecked).pure.game).outcomeKernel
            pureProfile :=
  behavioralToCorrelatedPureOutcomeKernel matchingPenniesChecked behavioralProfile

theorem matchingPennies_behavioralToMixedPure_outcomeKernel
    (behavioralProfile :
      ((canonicalFrontierKuhnGames matchingPenniesChecked).behavioral.game).Profile) :
    ((canonicalFrontierKuhnGames matchingPenniesChecked).behavioral.game).outcomeKernel
        behavioralProfile =
      (Math.PMFProduct.pmfPi
        ((canonicalFrontierKuhnGames matchingPenniesChecked).behavioralToMixedPure
          (canonicalFrontierKuhnGames_menusObservable matchingPenniesChecked)
          behavioralProfile)).bind fun pureProfile =>
        ((canonicalFrontierKuhnGames matchingPenniesChecked).pure.game).outcomeKernel
          pureProfile :=
  behavioralToProductMixedOutcomeKernel matchingPenniesChecked behavioralProfile

/-- The checked Matching Pennies program reaches the native frontier kernel
game surface for pure strategies. -/
noncomputable example : KernelGame Player :=
  matchingPenniesFrontierGame.game

/-- The checked Matching Pennies program also reaches the native behavioral
frontier kernel game surface. -/
noncomputable example : KernelGame Player :=
  matchingPenniesBehavioralFrontierGame.game

noncomputable example : KernelGame Player :=
  matchingPenniesSemantics.pureGame

noncomputable example : KernelGame Player :=
  matchingPenniesSemantics.behavioralGame

noncomputable example : KernelGame Player :=
  matchingPenniesChecked.pureFrontierGame

noncomputable example : KernelGame Player :=
  matchingPenniesChecked.behavioralFrontierGame

noncomputable example : KernelGame Player :=
  matchingPenniesChecked.mixedPureFrontierGame

noncomputable example : GameForm Player :=
  matchingPenniesChecked.pureFrontierHistoryGameForm

noncomputable example : GameForm Player :=
  matchingPenniesChecked.behavioralFrontierHistoryGameForm

noncomputable example : GameForm Player :=
  matchingPenniesChecked.pureFrontierPublicHistoryGameForm

noncomputable example : GameForm Player :=
  matchingPenniesChecked.behavioralFrontierPublicHistoryGameForm

noncomputable example : GameForm Player :=
  matchingPenniesChecked.pureFrontierTerminalPublicGameForm

noncomputable example : GameForm Player :=
  matchingPenniesChecked.behavioralFrontierTerminalPublicGameForm

noncomputable example : KernelGame Player :=
  matchingPenniesChecked.pureFrontierHistoryKernelGame

noncomputable example : KernelGame Player :=
  matchingPenniesChecked.behavioralFrontierHistoryKernelGame

noncomputable example : KernelGame Player :=
  matchingPenniesChecked.behavioralTerminalPublicFrontierGame

noncomputable def matchingPenniesFOSG :=
  matchingPenniesChecked.frontierFOSG

noncomputable local instance matchingPenniesFOSGTerminalDecidable :
    DecidablePred matchingPenniesChecked.frontierFOSG.terminal :=
  Classical.decPred _

noncomputable def matchingPenniesFOSGHistoryKernelGame :
    KernelGame Player :=
  matchingPenniesChecked.frontierFOSGHistoryKernelGame

noncomputable def matchingPenniesFOSGMachinePayoffHistoryKernelGame :
    KernelGame Player :=
  matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame

noncomputable def matchingPenniesPlainEFG : EFG.EFGGame :=
  matchingPenniesChecked.frontierPlainEFG

noncomputable def matchingPenniesPlainEFGMachinePayoffKernelGame :
    KernelGame Player :=
  matchingPenniesChecked.frontierPlainEFGMachinePayoffKernelGame

theorem matchingPenniesFOSG_boundedHorizon :
    matchingPenniesFOSG.BoundedHorizon matchingPenniesSemantics.horizon := by
  exact matchingPenniesChecked.frontierFOSG_boundedHorizon

theorem matchingPenniesFOSG_runDist_behavioral
    (profile : matchingPenniesChecked.BehavioralFrontierProfile)
    (steps : Nat) :
    PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0))
        ((matchingPenniesChecked.frontierSemantics.behavioral.view).runDist
          matchingPenniesChecked.frontierSemantics.horizon steps profile) =
      matchingPenniesChecked.frontierFOSG.runDist steps
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
          profile).extend :=
  matchingPenniesChecked
    |>.frontierFOSG_runDist_eq_map_behavioralHistory profile steps

theorem matchingPenniesFOSG_historyKernel_behavioral
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.frontierFOSGHistoryKernelGame.outcomeKernel
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0))
        ((matchingPenniesChecked.frontierSemantics.behavioral.view).runDist
          matchingPenniesChecked.frontierSemantics.horizon
          matchingPenniesChecked.frontierSemantics.horizon profile) :=
  matchingPenniesChecked
    |>.frontierFOSGHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
      profile

theorem matchingPenniesFOSG_machinePayoffHistoryKernel_behavioral
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0))
        ((matchingPenniesChecked.frontierSemantics.behavioral.view).runDist
          matchingPenniesChecked.frontierSemantics.horizon
          matchingPenniesChecked.frontierSemantics.horizon profile) :=
  matchingPenniesChecked
    |>.frontierFOSGMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
      profile

theorem matchingPenniesFOSG_machinePayoffHistoryKernel_udist
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  matchingPenniesChecked
    |>.frontierFOSGMachinePayoffHistoryKernelGame_udist_behavioralGame
      profile

theorem matchingPenniesPlainEFG_udist_fosg
    (profile :
      matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    matchingPenniesChecked.frontierPlainEFGMachinePayoffKernelGame.udist
        (matchingPenniesChecked.frontierPlainEFGTranslateProfile profile) =
      matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame.udist
        profile :=
  matchingPenniesChecked
    |>.frontierPlainEFGMachinePayoffKernelGame_udist_eq_fosg profile

theorem matchingPenniesPlainEFG_udist_behavioralGame
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.frontierPlainEFGMachinePayoffKernelGame.udist
        (matchingPenniesChecked.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            matchingPenniesChecked.frontierSemantics.behavioral.view
            matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  matchingPenniesChecked
    |>.frontierPlainEFGMachinePayoffKernelGame_udist_behavioralGame profile

theorem matchingPenniesPlainEFG_support_nativeHistory
    (profile : matchingPenniesChecked.BehavioralFrontierProfile)
    {history :
      matchingPenniesChecked.frontierPlainEFGMachinePayoffKernelGame.Outcome}
    (hsupport :
      history ∈
        (matchingPenniesChecked.frontierPlainEFGMachinePayoffKernelGame.outcomeKernel
          (matchingPenniesChecked.frontierPlainEFGTranslateProfile
            (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
              matchingPenniesChecked.frontierSemantics.behavioral.view
              matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
              profile).extend)).support) :
    ∃ nativeHistory : matchingPenniesChecked.BehavioralFrontierHistory,
      nativeHistory ∈
        ((matchingPenniesChecked.frontierSemantics.behavioral.view).runDist
          matchingPenniesChecked.frontierSemantics.horizon
          matchingPenniesChecked.frontierSemantics.horizon profile).support ∧
      Machine.RoundView.ToFOSG.historyOfBoundedHistory
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
          nativeHistory = history ∧
      EventGraph.Terminal matchingPenniesCompiled.graph
        nativeHistory.lastState.state.1 ∧
      (PrimitiveMachine matchingPenniesCompiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine matchingPenniesCompiled)
          matchingPenniesChecked.frontierSemantics.horizon).state)
        (Machine.RoundView.boundedHistoryEventBatches
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon nativeHistory)
        nativeHistory.lastState.state :=
  matchingPenniesChecked
    |>.frontierPlainEFGMachinePayoffKernelGame_support_nativeHistory
      profile hsupport

theorem matchingPenniesFOSG_machinePayoffHistoryKernel_support_nativeHistory
    (profile : matchingPenniesChecked.BehavioralFrontierProfile)
    {history :
      matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame.Outcome}
    (hsupport :
      history ∈
        (matchingPenniesChecked.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            matchingPenniesChecked.frontierSemantics.behavioral.view
            matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
            profile).extend).support) :
    ∃ nativeHistory : matchingPenniesChecked.BehavioralFrontierHistory,
      nativeHistory ∈
        ((matchingPenniesChecked.frontierSemantics.behavioral.view).runDist
          matchingPenniesChecked.frontierSemantics.horizon
          matchingPenniesChecked.frontierSemantics.horizon profile).support ∧
      Machine.RoundView.ToFOSG.historyOfBoundedHistory
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon (fun _ => 0)
          nativeHistory = history ∧
      EventGraph.Terminal matchingPenniesCompiled.graph
        nativeHistory.lastState.state.1 ∧
      (PrimitiveMachine matchingPenniesCompiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine matchingPenniesCompiled)
          matchingPenniesChecked.frontierSemantics.horizon).state)
        (Machine.RoundView.boundedHistoryEventBatches
          matchingPenniesChecked.frontierSemantics.behavioral.view
          matchingPenniesChecked.frontierSemantics.horizon nativeHistory)
        nativeHistory.lastState.state :=
  matchingPenniesChecked
    |>.frontierFOSGMachinePayoffHistoryKernelGame_support_nativeHistory
      profile hsupport

noncomputable def matchingPenniesPureFrontierExport :
    Export.KernelGameExport Player :=
  Export.pureFrontierGame matchingPenniesChecked

noncomputable def matchingPenniesPureTerminalPublicFrontierExport :
    Export.KernelGameExport Player :=
  Export.pureTerminalPublicFrontierGame matchingPenniesChecked

noncomputable def matchingPenniesPureFrontierHistoryExport :
    Export.KernelGameExport Player :=
  Export.pureFrontierHistoryGame matchingPenniesChecked

noncomputable def matchingPenniesFOSGExport :
    Export.FOSGExport Player :=
  Export.frontierFOSG matchingPenniesChecked

noncomputable def matchingPenniesPlainEFGExport :
    Export.EFGExport Player :=
  Export.frontierPlainEFG matchingPenniesChecked

noncomputable def matchingPenniesPureHistoryGameForm : GameForm Player :=
  matchingPenniesSemantics.pureHistoryGameForm

noncomputable def matchingPenniesBehavioralHistoryGameForm : GameForm Player :=
  matchingPenniesSemantics.behavioralHistoryGameForm

noncomputable def matchingPenniesPureHistoryKernelGame :
    KernelGame Player :=
  matchingPenniesSemantics.pureHistoryKernelGame

noncomputable def matchingPenniesBehavioralHistoryKernelGame :
    KernelGame Player :=
  matchingPenniesSemantics.behavioralHistoryKernelGame

noncomputable def matchingPenniesPurePublicHistoryGameForm : GameForm Player :=
  matchingPenniesSemantics.purePublicHistoryGameForm

noncomputable def matchingPenniesBehavioralPublicHistoryGameForm :
    GameForm Player :=
  matchingPenniesSemantics.behavioralPublicHistoryGameForm

noncomputable def matchingPenniesPureTerminalPublicGameForm :
    GameForm Player :=
  matchingPenniesSemantics.pureTerminalPublicGameForm

noncomputable def matchingPenniesBehavioralTerminalPublicGameForm :
    GameForm Player :=
  matchingPenniesSemantics.behavioralTerminalPublicGameForm

noncomputable def matchingPenniesPureTerminalPublicKernelGame :
    KernelGame Player :=
  matchingPenniesSemantics.pureTerminalPublicKernelGame

noncomputable def matchingPenniesBehavioralTerminalPublicKernelGame :
    KernelGame Player :=
  matchingPenniesSemantics.behavioralTerminalPublicKernelGame

noncomputable example (player : Player) :
    Fintype (matchingPenniesSemantics.pureGame.Strategy player) :=
  matchingPenniesSemantics.pureStrategyFintype player

noncomputable example (player : Player) :
    Fintype (matchingPenniesChecked.PureFrontierStrategy player) :=
  matchingPenniesChecked.pureFrontierStrategyFintype player

noncomputable example (player : Player) :
    Nonempty (matchingPenniesSemantics.pureGame.Strategy player) :=
  matchingPenniesSemantics.pureStrategyNonempty player

noncomputable example (player : Player) :
    Nonempty (matchingPenniesChecked.PureFrontierStrategy player) :=
  matchingPenniesChecked.pureFrontierStrategyNonempty player

noncomputable example : KernelGame Player :=
  matchingPenniesSemantics.mixedPureGame

noncomputable example : KernelGame Player :=
  matchingPenniesSemantics.mixedPureTerminalPublicGame

example
    (profile : matchingPenniesSemantics.pureGame.Profile) :
    matchingPenniesSemantics.pureHistoryKernelGame.udist profile =
      matchingPenniesSemantics.pureGame.udist profile :=
  matchingPenniesSemantics.pureHistoryKernelGame_udist profile

example
    (profile : matchingPenniesSemantics.behavioralGame.Profile) :
    matchingPenniesSemantics.behavioralHistoryKernelGame.udist profile =
      matchingPenniesSemantics.behavioralGame.udist profile :=
  matchingPenniesSemantics.behavioralHistoryKernelGame_udist profile

abbrev MatchingPennies.MixedNashProfiles : Type :=
  { σ : matchingPenniesSemantics.mixedPureGame.Profile //
    matchingPenniesSemantics.mixedPureGame.IsNash σ }

abbrev MatchingPennies.ProgramMixedNashProfiles : Type :=
  { σ : matchingPenniesChecked.MixedPureFrontierProfile //
    matchingPenniesChecked.MixedPureFrontierNash σ }

abbrev MatchingPennies.BehavioralCorrelatedProfiles : Type :=
  matchingPenniesChecked.BehavioralFrontierCorrelatedProfile

example
    (profile : matchingPenniesChecked.PureFrontierProfile)
    (hNash : matchingPenniesChecked.PureFrontierNash profile) :
    matchingPenniesChecked.PureFrontierεNash 0 profile :=
  matchingPenniesChecked.pureFrontier_nash_is_epsilonNash hNash
    (by norm_num)

example
    (profile : matchingPenniesChecked.BehavioralFrontierProfile)
    (hNash : matchingPenniesChecked.BehavioralFrontierNash profile) :
    matchingPenniesChecked.BehavioralFrontierεNash 0 profile :=
  matchingPenniesChecked.behavioralFrontier_nash_is_epsilonNash hNash
    (by norm_num)

example
    (profile : matchingPenniesChecked.PureFrontierProfile)
    (hdom :
      ∀ player,
        matchingPenniesChecked.PureFrontierDominant player
          (profile player)) :
    matchingPenniesChecked.PureFrontierNash profile :=
  matchingPenniesChecked.pureFrontier_dominant_profile_is_nash
    profile hdom

example
    (profile : matchingPenniesChecked.BehavioralFrontierProfile)
    (hdom :
      ∀ player,
        matchingPenniesChecked.BehavioralFrontierDominant player
          (profile player)) :
    matchingPenniesChecked.BehavioralFrontierNash profile :=
  matchingPenniesChecked.behavioralFrontier_dominant_profile_is_nash
    profile hdom

example
    (profile : matchingPenniesChecked.PureFrontierProfile)
    (reservation : Player → ℝ) : Prop :=
  matchingPenniesChecked.PureFrontierIndividuallyRational
    reservation profile

example
    (profile : matchingPenniesChecked.BehavioralFrontierProfile)
    (reservation : Player → ℝ) : Prop :=
  matchingPenniesChecked.BehavioralFrontierIndividuallyRational
    reservation profile

example : Prop :=
  matchingPenniesChecked.PureFrontierZeroSum

example : Prop :=
  matchingPenniesChecked.BehavioralFrontierZeroSum

example
    (potential : matchingPenniesChecked.PureFrontierProfile → ℝ) :
    Prop :=
  matchingPenniesChecked.PureFrontierExactPotential potential

example
    (potential : matchingPenniesChecked.BehavioralFrontierProfile → ℝ) :
    Prop :=
  matchingPenniesChecked.BehavioralFrontierExactPotential potential

example
    {C : Player → ℝ}
    (hbd :
      ∀ who outcome,
        |matchingPenniesSemantics.pureGame.utility outcome who| ≤ C who) :
    ∃ mixed : matchingPenniesSemantics.mixedPureGame.Profile,
      matchingPenniesSemantics.mixedPureGame.IsNash mixed :=
  matchingPenniesSemantics.mixedPureNash_exists_of_bounded hbd

example
    {C : Player → ℝ}
    (hbd :
      ∀ who outcome,
        |matchingPenniesChecked.pureFrontierGame.utility outcome who| ≤
          C who) :
    ∃ mixed : matchingPenniesChecked.MixedPureFrontierProfile,
      matchingPenniesChecked.MixedPureFrontierNash mixed :=
  matchingPenniesChecked.mixedPureFrontier_nash_exists_of_bounded hbd

/-- The compiled Matching Pennies frontier game has a mixed pure Nash
equilibrium whenever the compiled payoff utility is bounded. -/
theorem matchingPennies_mixedPureFrontierNash_exists_of_bounded
    {C : Player → ℝ}
    (hbd :
      ∀ who outcome,
        |matchingPenniesChecked.pureFrontierGame.utility outcome who| ≤
          C who) :
    ∃ mixed : matchingPenniesChecked.MixedPureFrontierProfile,
      matchingPenniesChecked.MixedPureFrontierNash mixed :=
  matchingPenniesChecked.mixedPureFrontier_nash_exists_of_bounded hbd

example :
    ∃ mixed : matchingPenniesSemantics.mixedPureTerminalPublicGame.Profile,
      matchingPenniesSemantics.mixedPureTerminalPublicGame.IsNash mixed :=
  matchingPenniesSemantics.terminalPublicMixedNash_exists

example :
    ∃ mixed :
        matchingPenniesChecked.mixedPureTerminalPublicFrontierGame.Profile,
      matchingPenniesChecked.mixedPureTerminalPublicFrontierGame.IsNash
        mixed :=
  matchingPenniesChecked.mixedPureTerminalPublicFrontier_nash_exists

example :
    ∃ correlated :
        PMF matchingPenniesChecked.PureTerminalPublicFrontierProfile,
      matchingPenniesChecked.PureTerminalPublicFrontierCorrelatedEq
        correlated :=
  matchingPenniesChecked.pureTerminalPublicFrontier_correlatedEq_exists

example :
    ∃ correlated :
        PMF matchingPenniesChecked.PureTerminalPublicFrontierProfile,
      WFProgram.PureTerminalPublicFrontierCoarseCorrelatedEq
        matchingPenniesChecked correlated :=
  matchingPenniesChecked
    |>.pureTerminalPublicFrontier_coarseCorrelatedEq_exists

example
    (behavioralProfile : matchingPenniesSemantics.behavioralGame.Profile) :
    ∃ correlated : PMF matchingPenniesSemantics.pureGame.Profile,
      matchingPenniesSemantics.behavioralGame.outcomeKernel
          behavioralProfile =
        correlated.bind fun pureProfile =>
          matchingPenniesSemantics.pureGame.outcomeKernel pureProfile :=
  matchingPenniesSemantics.behavioralToCorrelatedPure behavioralProfile

example
    (behavioralProfile : matchingPenniesSemantics.behavioralGame.Profile) :
    matchingPenniesSemantics.behavioralGame.outcomeKernel
        behavioralProfile =
      matchingPenniesSemantics.mixedPureGame.outcomeKernel
        (matchingPenniesSemantics.behavioralToMixedPure
          behavioralProfile) :=
  matchingPenniesSemantics
    |>.behavioralToMixedPureOutcomeKernel behavioralProfile

example
    (behavioralProfile :
      matchingPenniesChecked.BehavioralFrontierProfile) :
    ∃ correlated : PMF matchingPenniesChecked.PureFrontierProfile,
      matchingPenniesChecked.behavioralFrontierGame.outcomeKernel
          behavioralProfile =
        correlated.bind fun pureProfile =>
          matchingPenniesChecked.pureFrontierGame.outcomeKernel
            pureProfile :=
  matchingPenniesChecked
    |>.behavioralFrontier_to_correlatedPure behavioralProfile

example
    (behavioralProfile :
      matchingPenniesChecked.BehavioralFrontierProfile) :
    matchingPenniesChecked.behavioralFrontierGame.outcomeKernel
        behavioralProfile =
      matchingPenniesChecked.mixedPureFrontierGame.outcomeKernel
        (matchingPenniesChecked.behavioralFrontierToMixedPure
          behavioralProfile) :=
  matchingPenniesChecked
    |>.behavioralFrontier_to_mixedPure_outcomeKernel behavioralProfile

example
    (behavioralProfile : matchingPenniesSemantics.behavioralGame.Profile) :
    ∀ player,
      matchingPenniesSemantics.behavioralGame.eu
          behavioralProfile player =
        matchingPenniesSemantics.mixedPureGame.eu
          (matchingPenniesSemantics.behavioralToMixedPure
            behavioralProfile) player :=
  matchingPenniesSemantics
    |>.behavioralToMixedPureEU behavioralProfile

example
    (behavioralProfile : matchingPenniesSemantics.behavioralGame.Profile)
    (hNash :
      matchingPenniesSemantics.mixedPureGame.IsNash
        (matchingPenniesSemantics.behavioralToMixedPure
          behavioralProfile)) :
    matchingPenniesSemantics.behavioralGame.IsNash behavioralProfile :=
  matchingPenniesSemantics
    |>.behavioralNash_of_inducedMixedPureNash hNash

noncomputable example :
    matchingPenniesSemantics.MixedPureToBehavioralDeviationSimulation :=
  matchingPenniesSemantics.canonicalMixedPureToBehavioralDeviationSimulation

noncomputable example :
    WFProgram.MixedPureToBehavioralFrontierDeviationSimulation
      matchingPenniesChecked :=
  matchingPenniesChecked
    |>.canonicalMixedPureToBehavioralFrontierDeviationSimulation

example
    (simulation :
      matchingPenniesSemantics.MixedPureToBehavioralDeviationSimulation)
    {mixed : matchingPenniesSemantics.mixedPureGame.Profile}
    (hNash : matchingPenniesSemantics.mixedPureGame.IsNash mixed) :
    matchingPenniesSemantics.behavioralGame.IsNash
      (simulation.realize mixed) :=
  simulation.behavioralNash_of_mixedPureNash hNash

example
    (simulation :
      WFProgram.MixedPureToBehavioralFrontierDeviationSimulation
        matchingPenniesChecked)
    {mixed : matchingPenniesChecked.MixedPureFrontierProfile}
    (hNash : matchingPenniesChecked.MixedPureFrontierNash mixed) :
    matchingPenniesChecked.BehavioralFrontierNash
      (simulation.realize mixed) :=
  matchingPenniesChecked
    |>.behavioralFrontier_nash_of_mixedPure_nash simulation hNash

example
    (simulation :
      matchingPenniesSemantics.MixedPureToBehavioralDeviationSimulation)
    {C : Player → ℝ}
    (hbd :
      ∀ who outcome,
        |matchingPenniesSemantics.pureGame.utility outcome who| ≤ C who) :
    ∃ behavioral : matchingPenniesSemantics.behavioralGame.Profile,
      matchingPenniesSemantics.behavioralGame.IsNash behavioral :=
  simulation.behavioralNash_exists_of_bounded hbd

example
    (simulation :
      WFProgram.MixedPureToBehavioralFrontierDeviationSimulation
        matchingPenniesChecked)
    {C : Player → ℝ}
    (hbd :
      ∀ who outcome,
        |matchingPenniesChecked.pureFrontierGame.utility outcome who| ≤
          C who) :
    ∃ behavioral : matchingPenniesChecked.BehavioralFrontierProfile,
      matchingPenniesChecked.BehavioralFrontierNash behavioral :=
  matchingPenniesChecked
    |>.behavioralFrontier_nash_exists_of_bounded simulation hbd

/-- The compiled Matching Pennies frontier game has a behavioral Nash
equilibrium by finite mixed Nash existence plus the canonical Kuhn
deviation-simulation bridge. -/
theorem matchingPennies_behavioralFrontierNash_exists_of_bounded
    {C : Player → ℝ}
    (hbd :
      ∀ who outcome,
        |matchingPenniesChecked.pureFrontierGame.utility outcome who| ≤
          C who) :
  ∃ behavioral : matchingPenniesChecked.BehavioralFrontierProfile,
      matchingPenniesChecked.BehavioralFrontierNash behavioral :=
  matchingPenniesChecked.behavioralFrontier_nash_exists_of_bounded
    matchingPenniesChecked.canonicalMixedPureToBehavioralFrontierDeviationSimulation
    hbd

example
    (mixed : matchingPenniesSemantics.mixedPureGame.Profile) :
    matchingPenniesSemantics.behavioralGame.outcomeKernel
        (matchingPenniesSemantics.mixedToBehavioralProfile mixed) =
      matchingPenniesSemantics.mixedPureGame.outcomeKernel mixed :=
  matchingPenniesSemantics.mixedToBehavioralProfileOutcomeKernel mixed

example
    (mixed : matchingPenniesSemantics.mixedPureGame.Profile) :
    ∃ behavioralProfile : matchingPenniesSemantics.behavioralGame.Profile,
      matchingPenniesSemantics.behavioralGame.outcomeKernel
          behavioralProfile =
        matchingPenniesSemantics.mixedPureGame.outcomeKernel mixed ∧
      ∀ player,
        matchingPenniesSemantics.behavioralGame.eu behavioralProfile player =
          matchingPenniesSemantics.mixedPureGame.eu mixed player :=
  matchingPenniesSemantics.mixedToBehavioralEU mixed

example
    (mixed : matchingPenniesChecked.MixedPureFrontierProfile) :
    matchingPenniesChecked.behavioralFrontierGame.outcomeKernel
        (matchingPenniesChecked.mixedPureToBehavioralFrontierProfile mixed) =
      matchingPenniesChecked.mixedPureFrontierGame.outcomeKernel mixed :=
  matchingPenniesChecked
    |>.mixedPureToBehavioralFrontierProfile_outcomeKernel mixed

example
    (mixed : matchingPenniesChecked.MixedPureFrontierProfile) :
    ∃ behavioral : matchingPenniesChecked.BehavioralFrontierProfile,
      matchingPenniesChecked.MixedPureToBehavioralFrontierProfileRealizes
        mixed behavioral :=
  matchingPenniesChecked
    |>.mixedPureToBehavioralFrontierProfileRealizes_exists mixed

noncomputable example :
    KernelGame.Realization
      matchingPenniesChecked.mixedPureFrontierGame
      matchingPenniesChecked.behavioralFrontierGame
      (GameForm.ViewFamily.const
        (F := matchingPenniesChecked.mixedPureFrontierGame.toGameForm)
        (U := Player) id)
      (GameForm.ViewFamily.const
        (F := matchingPenniesChecked.behavioralFrontierGame.toGameForm)
        (U := Player) id) :=
  matchingPenniesChecked.mixedPureToBehavioralFrontierRealization

noncomputable example :
    KernelGame.NashDeviationSimulation
      matchingPenniesChecked.mixedPureFrontierGame
      matchingPenniesChecked.behavioralFrontierGame
      matchingPenniesChecked.mixedPureFrontierGame.Outcome :=
  matchingPenniesChecked.behavioralToMixedPureFrontierNashDeviationSimulation

example :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      matchingPenniesChecked.BehavioralFrontierProfile
      (∀ player, PMF (matchingPenniesChecked.PureFrontierStrategy player))
      matchingPenniesChecked.PureFrontierProfile
      matchingPenniesChecked.pureFrontierGame.Outcome
      (fun behavioral =>
        Math.PMFProduct.pmfPi
          (matchingPenniesChecked.behavioralFrontierToMixedPure behavioral))
      Math.PMFProduct.pmfPi
      matchingPenniesChecked.behavioralFrontierGame.outcomeKernel
      matchingPenniesChecked.pureFrontierGame.outcomeKernel :=
  matchingPenniesChecked.frontierCompleteOutcomeKuhn

/-- The compiled Matching Pennies frontier games satisfy the two-direction
outcome-kernel Kuhn schema. -/
theorem matchingPennies_frontierCompleteOutcomeKuhn :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      matchingPenniesChecked.BehavioralFrontierProfile
      (∀ player, PMF (matchingPenniesChecked.PureFrontierStrategy player))
      matchingPenniesChecked.PureFrontierProfile
      matchingPenniesChecked.pureFrontierGame.Outcome
      (fun behavioral =>
        Math.PMFProduct.pmfPi
          (matchingPenniesChecked.behavioralFrontierToMixedPure behavioral))
      Math.PMFProduct.pmfPi
      matchingPenniesChecked.behavioralFrontierGame.outcomeKernel
      matchingPenniesChecked.pureFrontierGame.outcomeKernel :=
  matchingPenniesChecked.frontierCompleteOutcomeKuhn

example
    (behavioralProfile : matchingPenniesSemantics.behavioralGame.Profile) :
    matchingPenniesSemantics.behavioral.optionOutcomeKernel
        behavioralProfile =
      PMF.map
        (sourceOutcomeOptionAtHistory matchingPenniesChecked.core)
        ((matchingPenniesSemantics.behavioral.view).runDist
          (completionBound (compile matchingPenniesChecked.core))
          (completionBound (compile matchingPenniesChecked.core))
          behavioralProfile) :=
  matchingPenniesSemantics
    |>.behavioralOptionOutcomeKernel_eq_sourceMap behavioralProfile

example :
    completionBound matchingPenniesCompiled =
      matchingPenniesCompiled.graph.nodeCount := by
  rfl

example
    (history :
      matchingPenniesFrontierGame.view.BoundedHistory
        (completionBound matchingPenniesCompiled))
    (hlen : history.steps.length = completionBound matchingPenniesCompiled) :
    EventGraph.Terminal matchingPenniesCompiled.graph
      history.lastState.state.1 := by
  exact
    matchingPenniesFrontierGame
      |>.boundedHistory_terminal_of_length_completionBound history hlen

example
    (action :
      {a : JointAction (FrontierAct matchingPenniesCompiled) //
        JointActionLegal
          (FrontierAct matchingPenniesCompiled)
          (frontierActive matchingPenniesCompiled)
          (PrimitiveMachine matchingPenniesCompiled).terminal
          (frontierAvailableActions matchingPenniesCompiled)
          (PrimitiveMachine matchingPenniesCompiled).init a})
    {dst : (PrimitiveMachine matchingPenniesCompiled).State}
    (hsupport :
      matchingPenniesFrontierGame.semantics.transition
        (PrimitiveMachine matchingPenniesCompiled).init action dst ≠ 0) :
    EventGraph.readyInternalNodes matchingPenniesCompiled.graph dst.1 = ∅ := by
  exact
    canonicalFrontierPureKernelGame_transition_support_closed
      matchingPenniesChecked action hsupport

example
    (σ : matchingPenniesFrontierGame.game.Profile)
    {result : Option (PrimitiveMachine matchingPenniesCompiled).Outcome}
    (hsupport :
      result ∈
        (matchingPenniesFrontierGame.optionOutcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  exact matchingPenniesFrontierGame.optionOutcomeKernel_support_some σ hsupport

example
    (σ : matchingPenniesFrontierGame.game.Profile) :
    none ∉
      (matchingPenniesFrontierGame.optionOutcomeKernel σ).support := by
  exact
    matchingPenniesFrontierGame
      |>.none_not_mem_outcomeKernel_support σ

example
    (σ : matchingPenniesFrontierGame.game.Profile)
    (outcome : (PrimitiveMachine matchingPenniesCompiled).Outcome) :
    outcome ∈
        (matchingPenniesFrontierGame.game.outcomeKernel σ).support ↔
      some outcome ∈
        (matchingPenniesFrontierGame.optionOutcomeKernel σ).support :=
  matchingPenniesFrontierGame.outcomeKernel_support_iff σ outcome

example
    (σ : matchingPenniesFrontierGame.game.Profile)
    (outcome : (PrimitiveMachine matchingPenniesCompiled).Outcome) :
    matchingPenniesFrontierGame.game.outcomeKernel σ outcome =
      matchingPenniesFrontierGame.optionOutcomeKernel σ
        (some outcome) :=
  matchingPenniesFrontierGame.outcomeKernel_apply σ outcome

example
    (σ : matchingPenniesFrontierGame.game.Profile)
    (who : Player) (cutoff : Payoff Player) :
    PMF.map
        (fun outcome =>
          (PrimitiveMachine matchingPenniesCompiled).utility outcome who)
        (matchingPenniesFrontierGame.game.outcomeKernel σ) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine matchingPenniesCompiled) cutoff result who)
        (matchingPenniesFrontierGame.optionOutcomeKernel σ) :=
  matchingPenniesFrontierGame
    |>.utilityDistribution_eq_optionUtilityDistribution σ who cutoff

example
    (σ : matchingPenniesFrontierGame.game.Profile)
    (who : Player) (cutoff : Payoff Player) {C : ℝ}
    (hbd :
      ∀ outcome,
        |(PrimitiveMachine matchingPenniesCompiled).utility outcome who| ≤ C) :
    matchingPenniesFrontierGame.game.eu σ who =
      Math.Probability.expect
        (matchingPenniesFrontierGame.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine matchingPenniesCompiled) cutoff result who) :=
  matchingPenniesFrontierGame
    |>.eu_eq_optionKernel_expect σ who cutoff hbd

example
    (σ : matchingPenniesFrontierGame.game.Profile)
    {outcome : (PrimitiveMachine matchingPenniesCompiled).Outcome}
    (hsupport :
      outcome ∈
        (matchingPenniesFrontierGame.game.outcomeKernel σ).support) :
    ∃ history :
        matchingPenniesFrontierGame.view.BoundedHistory
          (completionBound matchingPenniesCompiled),
      EventGraph.Terminal matchingPenniesCompiled.graph
        history.lastState.state.1 ∧
      (PrimitiveMachine matchingPenniesCompiled).outcome
        history.lastState.state = some outcome := by
  rcases matchingPenniesFrontierGame
      |>.outcomeKernel_support_history σ hsupport with
    ⟨history, _hhistory, hterminal, houtcome, _hrun⟩
  exact ⟨history, hterminal, houtcome⟩

noncomputable def matchingPenniesNode0 :
    Fin matchingPenniesCompiled.graph.nodeCount :=
  ⟨0, by
    simp [matchingPenniesCompiled, compile, matchingPenniesProgram,
      matchingPenniesCore, trueGuard, compileCore,
      EventGraph.Graph.nodeCount]⟩

noncomputable def matchingPenniesNode1 :
    Fin matchingPenniesCompiled.graph.nodeCount :=
  ⟨1, by
    simp [matchingPenniesCompiled, compile, matchingPenniesProgram,
      matchingPenniesCore, trueGuard, compileCore,
      EventGraph.Graph.nodeCount]⟩

noncomputable def matchingPenniesNode2 :
    Fin matchingPenniesCompiled.graph.nodeCount :=
  ⟨2, by
    simp [matchingPenniesCompiled, compile, matchingPenniesProgram,
      matchingPenniesCore, trueGuard, compileCore,
      EventGraph.Graph.nodeCount]⟩

noncomputable def matchingPenniesNode3 :
    Fin matchingPenniesCompiled.graph.nodeCount :=
  ⟨3, by
    simp [matchingPenniesCompiled, compile, matchingPenniesProgram,
      matchingPenniesCore, trueGuard, compileCore,
      EventGraph.Graph.nodeCount]⟩

example :
    matchingPenniesCompiled.graph.nodeCount = 4 := by
  simp [matchingPenniesCompiled, compile, matchingPenniesProgram,
    matchingPenniesCore, trueGuard, compileCore, EventGraph.Graph.nodeCount]

/-- The second initial commitment is independent of the first. -/
example :
    matchingPenniesCompiled.graph.prereqs matchingPenniesNode1 = ∅ := by
  decide

/-- The first reveal waits for both prior commitments, but not for source
order beyond the explicit commit/reveal barrier. -/
example :
    matchingPenniesCompiled.graph.prereqs matchingPenniesNode2 =
      {matchingPenniesNode0, matchingPenniesNode1} := by
  decide

/-- The second reveal also waits for both prior commitments; it is not ordered
after the first reveal merely because that reveal has already happened. -/
example :
    matchingPenniesCompiled.graph.prereqs matchingPenniesNode3 =
      {matchingPenniesNode0, matchingPenniesNode1} := by
  decide

example :
    matchingPenniesCompiled.payoffs.length = 2 := by
  simp [matchingPenniesCompiled, compile, matchingPenniesProgram,
    matchingPenniesCore, trueGuard, compileCore]

end Examples
end Vegas
