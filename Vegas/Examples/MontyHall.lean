import Vegas.Examples.DependencySemantics

/-!
# Monty Hall

Build-tested checked-program examples for the canonical frontier EventGraph
semantics.
-/

namespace Vegas
namespace Examples

open GameTheory
open ToEventGraph

/-! ## Monty Hall -/

namespace MontyHall

inductive Player where
  | guest
  | host
deriving DecidableEq, Repr, Fintype

abbrev DoorTy : BaseTy := .range 0 2
abbrev Door : Type := Val DoorTy

def door0 : Door := ⟨0, by decide⟩
def door1 : Door := ⟨1, by decide⟩
def door2 : Door := ⟨2, by decide⟩

lemma door_cases (d : Door) :
    d = door0 ∨ d = door1 ∨ d = door2 := by
  obtain ⟨i, hi⟩ := d
  have hlo : 0 ≤ i := hi.1
  have hhi : i ≤ 2 := hi.2
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
    omega
  rcases hcases with h | h | h <;> subst h
  · left
    rfl
  · right
    left
    rfl
  · right
    right
    rfl

lemma existsDoor_ne_two (a b : Door) :
    ∃ c : Door, c ≠ a ∧ c ≠ b := by
  rcases door_cases a with rfl | rfl | rfl <;>
    rcases door_cases b with rfl | rfl | rfl
  · exact ⟨door1, by decide, by decide⟩
  · exact ⟨door2, by decide, by decide⟩
  · exact ⟨door1, by decide, by decide⟩
  · exact ⟨door2, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩
  · exact ⟨door1, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩
  · exact ⟨door0, by decide, by decide⟩

def carSecret : VarId := 0
def firstSecret : VarId := 1
def firstPublic : VarId := 2
def openedSecret : VarId := 3
def openedPublic : VarId := 4
def switchSecret : VarId := 5
def switchPublic : VarId := 6
def carPublic : VarId := 7

abbrev Γ0 : VCtx Player L := []
abbrev Γ1 : VCtx Player L :=
  [(carSecret, .hidden Player.host DoorTy)]
abbrev Γ2 : VCtx Player L :=
  [(firstSecret, .hidden Player.guest DoorTy),
   (carSecret, .hidden Player.host DoorTy)]
abbrev Γ3 : VCtx Player L :=
  [(firstPublic, .pub DoorTy),
   (firstSecret, .hidden Player.guest DoorTy),
   (carSecret, .hidden Player.host DoorTy)]
abbrev Γ4 : VCtx Player L :=
  [(openedSecret, .hidden Player.host DoorTy),
   (firstPublic, .pub DoorTy),
   (firstSecret, .hidden Player.guest DoorTy),
   (carSecret, .hidden Player.host DoorTy)]
abbrev Γ5 : VCtx Player L :=
  [(openedPublic, .pub DoorTy),
   (openedSecret, .hidden Player.host DoorTy),
   (firstPublic, .pub DoorTy),
   (firstSecret, .hidden Player.guest DoorTy),
   (carSecret, .hidden Player.host DoorTy)]
abbrev Γ6 : VCtx Player L :=
  [(switchSecret, .hidden Player.guest .bool),
   (openedPublic, .pub DoorTy),
   (openedSecret, .hidden Player.host DoorTy),
   (firstPublic, .pub DoorTy),
   (firstSecret, .hidden Player.guest DoorTy),
   (carSecret, .hidden Player.host DoorTy)]
abbrev Γ7 : VCtx Player L :=
  [(switchPublic, .pub .bool),
   (switchSecret, .hidden Player.guest .bool),
   (openedPublic, .pub DoorTy),
   (openedSecret, .hidden Player.host DoorTy),
   (firstPublic, .pub DoorTy),
   (firstSecret, .hidden Player.guest DoorTy),
   (carSecret, .hidden Player.host DoorTy)]
abbrev Γ8 : VCtx Player L :=
  [(carPublic, .pub DoorTy),
   (switchPublic, .pub .bool),
   (switchSecret, .hidden Player.guest .bool),
   (openedPublic, .pub DoorTy),
   (openedSecret, .hidden Player.host DoorTy),
   (firstPublic, .pub DoorTy),
   (firstSecret, .hidden Player.guest DoorTy),
   (carSecret, .hidden Player.host DoorTy)]

def hFirstSecretΓ2 :
    VHasVar Γ2 firstSecret (.hidden Player.guest DoorTy) :=
  .here

def hOpenedSecretΓ4 :
    VHasVar Γ4 openedSecret (.hidden Player.host DoorTy) :=
  .here

def hSwitchSecretΓ6 :
    VHasVar Γ6 switchSecret (.hidden Player.guest .bool) :=
  .here

def hCarSecretΓ7 :
    VHasVar Γ7 carSecret (.hidden Player.host DoorTy) :=
  .there (.there (.there (.there (.there (.there .here)))))

def hOpenedCandidateGuard :
    HasVar ((openedSecret, DoorTy) ::
      eraseVCtx (viewVCtx Player.host Γ3)) openedSecret DoorTy :=
  .here

def hFirstPublicHostView :
    HasVar (eraseVCtx (viewVCtx Player.host Γ3)) firstPublic DoorTy :=
  .here

def hCarSecretHostView :
    HasVar (eraseVCtx (viewVCtx Player.host Γ3)) carSecret DoorTy :=
  .there .here

def hFirstPublicGuard :
    HasVar ((openedSecret, DoorTy) ::
      eraseVCtx (viewVCtx Player.host Γ3)) firstPublic DoorTy :=
  .there hFirstPublicHostView

def hCarSecretGuard :
    HasVar ((openedSecret, DoorTy) ::
      eraseVCtx (viewVCtx Player.host Γ3)) carSecret DoorTy :=
  .there hCarSecretHostView

def openedCandidate :
    Expr ((openedSecret, DoorTy) ::
      eraseVCtx (viewVCtx Player.host Γ3)) DoorTy :=
  .var openedSecret hOpenedCandidateGuard

def firstPublicAtHost :
    Expr ((openedSecret, DoorTy) ::
      eraseVCtx (viewVCtx Player.host Γ3)) DoorTy :=
  .var firstPublic hFirstPublicGuard

def carSecretAtHost :
    Expr ((openedSecret, DoorTy) ::
      eraseVCtx (viewVCtx Player.host Γ3)) DoorTy :=
  .var carSecret hCarSecretGuard

/-- The host must open a door that is neither the guest's first door nor the
car door. -/
def hostOpenGuard :
    Expr ((openedSecret, DoorTy) ::
      eraseVCtx (viewVCtx Player.host Γ3)) .bool :=
  .andBool
    (.notBool (.eq openedCandidate firstPublicAtHost))
    (.notBool (.eq openedCandidate carSecretAtHost))

def hCarPublicPayoff :
    HasVar (erasePubVCtx Γ8) carPublic DoorTy :=
  .here

def hSwitchPublicPayoff :
    HasVar (erasePubVCtx Γ8) switchPublic .bool :=
  .there .here

def hOpenedPublicPayoff :
    HasVar (erasePubVCtx Γ8) openedPublic DoorTy :=
  .there (.there .here)

def hFirstPublicPayoff :
    HasVar (erasePubVCtx Γ8) firstPublic DoorTy :=
  .there (.there (.there .here))

def carChoice : Expr (erasePubVCtx Γ8) DoorTy :=
  .var carPublic hCarPublicPayoff

def switchChoice : Expr (erasePubVCtx Γ8) .bool :=
  .var switchPublic hSwitchPublicPayoff

def openedChoice : Expr (erasePubVCtx Γ8) DoorTy :=
  .var openedPublic hOpenedPublicPayoff

def firstChoice : Expr (erasePubVCtx Γ8) DoorTy :=
  .var firstPublic hFirstPublicPayoff

def firstEqualsCar : Expr (erasePubVCtx Γ8) .bool :=
  .eq firstChoice carChoice

def guestWins : Expr (erasePubVCtx Γ8) .bool :=
  .ite switchChoice (.notBool firstEqualsCar) firstEqualsCar

def guestPayoff : Expr (erasePubVCtx Γ8) .int :=
  .ite guestWins (.constInt 1) (.constInt 0)

def hostPayoff : Expr (erasePubVCtx Γ8) .int :=
  .ite guestWins (.constInt 0) (.constInt 1)

def hostGuardEnv (first car : Door) :
    Env simpleExpr.Val (eraseVCtx (viewVCtx Player.host Γ3)) :=
  Env.cons (x := firstPublic) first
    (Env.cons (x := carSecret) car (Env.empty simpleExpr.Val))

def payoffEnv (first opened car : Door) (switch : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ8) :=
  Env.cons (x := carPublic) car
    (Env.cons (x := switchPublic) switch
      (Env.cons (x := openedPublic) opened
        (Env.cons (x := firstPublic) first (Env.empty simpleExpr.Val))))

theorem switching_wins_iff_first_guess_wrong
    (first opened car : Door) :
    evalExpr guestPayoff (payoffEnv first opened car true) =
      if first = car then 0 else 1 := by
  by_cases h : first = car <;>
    simp [guestPayoff, guestWins, firstEqualsCar, firstChoice, carChoice,
      switchChoice, payoffEnv, hFirstPublicPayoff, hCarPublicPayoff,
      hSwitchPublicPayoff, h, Env.get, Env.cons, evalExpr]

theorem staying_wins_iff_first_guess_right
    (first opened car : Door) :
    evalExpr guestPayoff (payoffEnv first opened car false) =
      if first = car then 1 else 0 := by
  by_cases h : first = car <;>
    simp [guestPayoff, guestWins, firstEqualsCar, firstChoice, carChoice,
      switchChoice, payoffEnv, hFirstPublicPayoff, hCarPublicPayoff,
      hSwitchPublicPayoff, h, Env.get, Env.cons, evalExpr]

def doors : List Door :=
  [door0, door1, door2]

/-- Over the nine equally weighted first-choice/car-position pairs, switching
wins in six cases. The opened door is irrelevant to the payoff expression once
the host has revealed some legal non-winning door. -/
theorem switch_payoff_count :
    (doors.map fun first =>
      (doors.map fun car =>
        evalExpr guestPayoff
          (payoffEnv first door0 car true)).sum).sum = 6 := by
  rfl

/-- Over the same nine equally weighted pairs, staying wins in three cases. -/
theorem stay_payoff_count :
    (doors.map fun first =>
      (doors.map fun car =>
        evalExpr guestPayoff
          (payoffEnv first door0 car false)).sum).sum = 3 := by
  rfl

theorem switch_payoff_average :
    (((doors.map fun first =>
      (doors.map fun car =>
        evalExpr guestPayoff
          (payoffEnv first door0 car true)).sum).sum : Int) : ℚ) / 9 =
      2 / 3 := by
  rw [switch_payoff_count]
  norm_num

theorem stay_payoff_average :
    (((doors.map fun first =>
      (doors.map fun car =>
        evalExpr guestPayoff
          (payoffEnv first door0 car false)).sum).sum : Int) : ℚ) / 9 =
      1 / 3 := by
  rw [stay_payoff_count]
  norm_num

theorem switch_average_gt_stay_average :
    (((doors.map fun first =>
      (doors.map fun car =>
        evalExpr guestPayoff
          (payoffEnv first door0 car true)).sum).sum : Int) : ℚ) / 9 >
      (((doors.map fun first =>
        (doors.map fun car =>
          evalExpr guestPayoff
            (payoffEnv first door0 car false)).sum).sum : Int) : ℚ) / 9 := by
  rw [switch_payoff_average, stay_payoff_average]
  norm_num

/-- If the guest first picked door 0 and the host opened door 1, a biased
host policy is summarized by `q`: when the car is behind door 0, the host
opens door 1 with weight `q`; when the car is behind door 2, opening door 1 is
forced. The posterior switch value is `1 / (q + 1)`. -/
theorem biased_open1_switch_value (q : ℚ) :
    (q * evalExpr guestPayoff
          (payoffEnv door0 door1 door0 true) +
        evalExpr guestPayoff
          (payoffEnv door0 door1 door2 true)) / (q + 1) =
      1 / (q + 1) := by
  have h02 : door0 ≠ door2 := by decide
  norm_num [switching_wins_iff_first_guess_wrong, h02]

theorem biased_open1_stay_value (q : ℚ) :
    (q * evalExpr guestPayoff
          (payoffEnv door0 door1 door0 false) +
        evalExpr guestPayoff
          (payoffEnv door0 door1 door2 false)) / (q + 1) =
      q / (q + 1) := by
  have h02 : door0 ≠ door2 := by decide
  norm_num [staying_wins_iff_first_guess_right, h02]

theorem biased_open1_switch_ge_stay
    (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    1 / (q + 1) ≥ q / (q + 1) := by
  have hden : 0 ≤ q + 1 := by linarith
  exact div_le_div_of_nonneg_right h1 hden

def core : VegasCore Player L Γ0 :=
  .commit carSecret Player.host (b := DoorTy) (.constBool true)
    (.commit firstSecret Player.guest (b := DoorTy) (.constBool true)
      (.reveal firstPublic Player.guest firstSecret hFirstSecretΓ2
        (.commit openedSecret Player.host (b := DoorTy) hostOpenGuard
          (.reveal openedPublic Player.host openedSecret hOpenedSecretΓ4
            (.commit switchSecret Player.guest (b := .bool) (.constBool true)
              (.reveal switchPublic Player.guest switchSecret hSwitchSecretΓ6
                (.reveal carPublic Player.host carSecret hCarSecretΓ7
                  (.ret [(Player.guest, guestPayoff),
                    (Player.host, hostPayoff)]))))))))

def legal : Legal core := by
  dsimp [core, Legal]
  constructor
  · intro _env
    exact ⟨door0, rfl⟩
  · constructor
    · intro _env
      exact ⟨door0, rfl⟩
    · constructor
      · intro env
        let first : Door := env.get hFirstPublicHostView
        let car : Door := env.get hCarSecretHostView
        obtain ⟨opened, hneFirst, hneCar⟩ :=
          existsDoor_ne_two first car
        refine ⟨opened, ?_⟩
        change ((!decide (opened = env.get hFirstPublicHostView)) &&
          (!decide (opened = env.get hCarSecretHostView))) = true
        simp [first, car, hneFirst, hneCar]
      · constructor
        · intro _env
          exact ⟨true, rfl⟩
        · trivial

noncomputable def graphProgram : GraphProgram Player L where
  Γ := Γ0
  prog := core
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    decide
  normalized := by
    trivial

noncomputable def checkedProgram : WFProgram Player L where
  core := graphProgram
  reveals := by
    decide
  legal := legal

noncomputable instance instFiniteDomains : FiniteDomains checkedProgram where
  context := inferInstanceAs (FiniteVCtx Γ0)
  program :=
    { proof :=
        .commit inferInstance
          (.commit inferInstance
            (.reveal inferInstance
              (.commit inferInstance
                (.reveal inferInstance
                  (.commit inferInstance
                    (.reveal inferInstance
                      (.reveal inferInstance .ret))))))) }

noncomputable def compiled : CompiledProgram Player L :=
  compile graphProgram

noncomputable def checkpointModel : CheckpointModel Player L :=
  primitiveDownsetCheckpointModel checkedProgram

noncomputable def frontierGame :
    CompletedFrontierBehavioralKernelGame (compile checkedProgram.core)
      (frontierPresentation
        (compile checkedProgram.core)
        (compile_guardLive checkedProgram)) :=
  canonicalFrontierBehavioralKernelGame checkedProgram

noncomputable def pureFrontierGame :
    CompletedFrontierPureKernelGame (compile checkedProgram.core)
      (frontierPresentation
        (compile checkedProgram.core)
        (compile_guardLive checkedProgram)) :=
  canonicalFrontierPureKernelGame checkedProgram

noncomputable def kuhnGames :
    CompletedFrontierKuhnGames (compile checkedProgram.core)
      (frontierPresentation
        (compile checkedProgram.core)
        (compile_guardLive checkedProgram)) :=
  canonicalFrontierKuhnGames checkedProgram

noncomputable def semantics :
    FrontierGameSemantics checkedProgram :=
  canonicalFrontierGameSemantics checkedProgram

theorem mixedPureToBehavioral_realizable :
    MixedPureToBehavioralOutcomeKernelRealizable checkedProgram :=
  MixedPureToBehavioralOutcomeKernelRealizable.canonical checkedProgram

theorem kuhnMenus :
    kuhnGames.view.MenusObservable
      (completionBound compiled) := by
  simpa [kuhnGames, compiled] using
    canonicalFrontierKuhnGames_menusObservable checkedProgram

/-- Monty Hall reaches the native behavioral frontier kernel game surface. -/
noncomputable example : KernelGame Player :=
  frontierGame.game

/-- Monty Hall also reaches the native pure frontier kernel game surface. -/
noncomputable example : KernelGame Player :=
  pureFrontierGame.game

noncomputable example : KernelGame Player :=
  semantics.behavioralGame

noncomputable example : KernelGame Player :=
  checkedProgram.frontierFOSGHistoryKernelGame

noncomputable example : KernelGame Player :=
  checkedProgram.frontierFOSGMachinePayoffHistoryKernelGame

noncomputable def plainEFG : EFG.EFGGame :=
  checkedProgram.frontierPlainEFG

noncomputable def plainEFGMachinePayoffKernelGame : KernelGame Player :=
  checkedProgram.frontierPlainEFGMachinePayoffKernelGame

noncomputable local instance fosgTerminalDecidable :
    DecidablePred checkedProgram.frontierFOSG.terminal :=
  Classical.decPred _

example : MixedPureToBehavioralOutcomeKernelRealizable checkedProgram :=
  mixedPureToBehavioral_realizable

theorem fosg_runDist_behavioral
    (behavioralProfile : semantics.behavioralGame.Profile)
    (steps : Nat) :
    PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0))
        ((checkedProgram.frontierSemantics.behavioral.view).runDist
          checkedProgram.frontierSemantics.horizon steps behavioralProfile) =
      checkedProgram.frontierFOSG.runDist steps
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0)
          behavioralProfile).extend :=
  checkedProgram.frontierFOSG_runDist_eq_map_behavioralHistory
    behavioralProfile steps

theorem fosgHistoryKernel_behavioral
    (behavioralProfile : semantics.behavioralGame.Profile) :
    checkedProgram.frontierFOSGHistoryKernelGame.outcomeKernel
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0)
          behavioralProfile).extend =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0))
        ((checkedProgram.frontierSemantics.behavioral.view).runDist
          checkedProgram.frontierSemantics.horizon
          checkedProgram.frontierSemantics.horizon behavioralProfile) :=
  checkedProgram
    |>.frontierFOSGHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
      behavioralProfile

theorem fosgMachinePayoffHistoryKernel_behavioral
    (behavioralProfile : semantics.behavioralGame.Profile) :
    checkedProgram.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0)
          behavioralProfile).extend =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0))
        ((checkedProgram.frontierSemantics.behavioral.view).runDist
          checkedProgram.frontierSemantics.horizon
          checkedProgram.frontierSemantics.horizon behavioralProfile) :=
  checkedProgram
    |>.frontierFOSGMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
      behavioralProfile

theorem fosgMachinePayoffHistoryKernel_udist
    (behavioralProfile : semantics.behavioralGame.Profile) :
    checkedProgram.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0)
          behavioralProfile).extend =
      checkedProgram.behavioralFrontierGame.udist behavioralProfile :=
  checkedProgram
    |>.frontierFOSGMachinePayoffHistoryKernelGame_udist_behavioralGame
      behavioralProfile

theorem plainEFGMachinePayoffKernel_udist
    (behavioralProfile : semantics.behavioralGame.Profile) :
    checkedProgram.frontierPlainEFGMachinePayoffKernelGame.udist
        (checkedProgram.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            checkedProgram.frontierSemantics.behavioral.view
            checkedProgram.frontierSemantics.horizon (fun _ => 0)
            behavioralProfile).extend) =
      checkedProgram.behavioralFrontierGame.udist behavioralProfile :=
  checkedProgram
    |>.frontierPlainEFGMachinePayoffKernelGame_udist_behavioralGame
      behavioralProfile

theorem plainEFGMachinePayoffKernel_udist_pure
    (pureProfile : semantics.pureGame.Profile) :
    checkedProgram.frontierPlainEFGMachinePayoffKernelGame.udist
        (checkedProgram.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            checkedProgram.frontierSemantics.behavioral.view
            checkedProgram.frontierSemantics.horizon (fun _ => 0)
            ((checkedProgram.frontierSemantics.behavioral.view).legalPureToBehavioral
              checkedProgram.frontierSemantics.horizon pureProfile)).extend) =
      checkedProgram.pureFrontierGame.udist pureProfile :=
  checkedProgram
    |>.frontierPlainEFGMachinePayoffKernelGame_udist_pureGame pureProfile

theorem plainEFGMachinePayoffKernel_support_nativeHistory
    (behavioralProfile : semantics.behavioralGame.Profile)
    {history : checkedProgram.frontierPlainEFGMachinePayoffKernelGame.Outcome}
    (hsupport :
      history ∈
        (checkedProgram.frontierPlainEFGMachinePayoffKernelGame.outcomeKernel
          (checkedProgram.frontierPlainEFGTranslateProfile
            (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
              checkedProgram.frontierSemantics.behavioral.view
              checkedProgram.frontierSemantics.horizon (fun _ => 0)
              behavioralProfile).extend)).support) :
    ∃ nativeHistory : checkedProgram.BehavioralFrontierHistory,
      nativeHistory ∈
        ((checkedProgram.frontierSemantics.behavioral.view).runDist
          checkedProgram.frontierSemantics.horizon
          checkedProgram.frontierSemantics.horizon behavioralProfile).support ∧
      Machine.RoundView.ToFOSG.historyOfBoundedHistory
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0)
          nativeHistory = history ∧
      EventGraph.Terminal (compile checkedProgram.core).graph
        nativeHistory.lastState.state.1 ∧
      (PrimitiveMachine (compile checkedProgram.core)).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine (compile checkedProgram.core))
          checkedProgram.frontierSemantics.horizon).state)
        (Machine.RoundView.boundedHistoryEventBatches
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon nativeHistory)
        nativeHistory.lastState.state :=
  checkedProgram
    |>.frontierPlainEFGMachinePayoffKernelGame_support_nativeHistory
      behavioralProfile hsupport

theorem fosgMachinePayoffHistoryKernel_support_nativeHistory
    (behavioralProfile : semantics.behavioralGame.Profile)
    {history : checkedProgram.frontierFOSGMachinePayoffHistoryKernelGame.Outcome}
    (hsupport :
      history ∈
        (checkedProgram.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            checkedProgram.frontierSemantics.behavioral.view
            checkedProgram.frontierSemantics.horizon (fun _ => 0)
            behavioralProfile).extend).support) :
    ∃ nativeHistory : checkedProgram.BehavioralFrontierHistory,
      nativeHistory ∈
        ((checkedProgram.frontierSemantics.behavioral.view).runDist
          checkedProgram.frontierSemantics.horizon
          checkedProgram.frontierSemantics.horizon behavioralProfile).support ∧
      Machine.RoundView.ToFOSG.historyOfBoundedHistory
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon (fun _ => 0)
          nativeHistory = history ∧
      EventGraph.Terminal (compile checkedProgram.core).graph
        nativeHistory.lastState.state.1 ∧
      (PrimitiveMachine (compile checkedProgram.core)).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine (compile checkedProgram.core))
          checkedProgram.frontierSemantics.horizon).state)
        (Machine.RoundView.boundedHistoryEventBatches
          checkedProgram.frontierSemantics.behavioral.view
          checkedProgram.frontierSemantics.horizon nativeHistory)
        nativeHistory.lastState.state :=
  checkedProgram
    |>.frontierFOSGMachinePayoffHistoryKernelGame_support_nativeHistory
      behavioralProfile hsupport

theorem behavioralToCorrelatedPure
    (behavioralProfile : kuhnGames.behavioral.game.Profile) :
    ∃ correlated : PMF kuhnGames.pure.game.Profile,
      kuhnGames.behavioral.game.outcomeKernel behavioralProfile =
        correlated.bind fun pureProfile =>
          kuhnGames.pure.game.outcomeKernel pureProfile :=
  kuhnGames.behavioralToCorrelatedPureOutcomeKernel kuhnMenus behavioralProfile

theorem semantics_behavioralToCorrelatedPure
    (behavioralProfile : semantics.behavioralGame.Profile) :
    ∃ correlated : PMF semantics.pureGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        correlated.bind fun pureProfile =>
          semantics.pureGame.outcomeKernel pureProfile :=
  semantics.behavioralToCorrelatedPure behavioralProfile

theorem behavioralToMixedPure_outcomeKernel
    (behavioralProfile : semantics.behavioralGame.Profile) :
    semantics.behavioralGame.outcomeKernel behavioralProfile =
      semantics.mixedPureGame.outcomeKernel
        (semantics.behavioralToMixedPure behavioralProfile) :=
  semantics.behavioralToMixedPureOutcomeKernel behavioralProfile

example
    (mixed : semantics.mixedPureGame.Profile) :
    ∃ behavioralProfile : semantics.behavioralGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        semantics.mixedPureGame.outcomeKernel mixed ∧
      ∀ player,
        semantics.behavioralGame.eu behavioralProfile player =
          semantics.mixedPureGame.eu mixed player :=
  semantics.mixedToBehavioralEU mixed

example
    (behavioralProfile : semantics.behavioralGame.Profile) :
    semantics.behavioral.optionOutcomeKernel behavioralProfile =
      PMF.map
        (sourceOutcomeOptionAtHistory checkedProgram.core)
        ((semantics.behavioral.view).runDist
          (completionBound (compile checkedProgram.core))
          (completionBound (compile checkedProgram.core))
          behavioralProfile) :=
  semantics.behavioralOptionOutcomeKernel_eq_sourceMap behavioralProfile

example :
    completionBound compiled = compiled.graph.nodeCount := by
  rfl

example
    (history :
      frontierGame.view.BoundedHistory (completionBound compiled))
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 := by
  exact
    frontierGame
      |>.boundedHistory_terminal_of_length_completionBound history hlen

example
    (σ : frontierGame.game.Profile)
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈
        (frontierGame.optionOutcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  exact frontierGame.optionOutcomeKernel_support_some σ hsupport

example
    (σ : frontierGame.game.Profile) :
    none ∉ (frontierGame.optionOutcomeKernel σ).support := by
  exact
    frontierGame
      |>.none_not_mem_outcomeKernel_support σ

example
    (σ : frontierGame.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    outcome ∈ (frontierGame.game.outcomeKernel σ).support ↔
      some outcome ∈ (frontierGame.optionOutcomeKernel σ).support :=
  frontierGame.outcomeKernel_support_iff σ outcome

example
    (σ : frontierGame.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    frontierGame.game.outcomeKernel σ outcome =
      frontierGame.optionOutcomeKernel σ (some outcome) :=
  frontierGame.outcomeKernel_apply σ outcome

example
    (σ : frontierGame.game.Profile)
    (who : Player) (cutoff : Payoff Player) :
    PMF.map
        (fun outcome => (PrimitiveMachine compiled).utility outcome who)
        (frontierGame.game.outcomeKernel σ) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (frontierGame.optionOutcomeKernel σ) :=
  frontierGame
    |>.utilityDistribution_eq_optionUtilityDistribution σ who cutoff

example
    (σ : frontierGame.game.Profile)
    (who : Player) (cutoff : Payoff Player) {C : ℝ}
    (hbd :
      ∀ outcome, |(PrimitiveMachine compiled).utility outcome who| ≤ C) :
    frontierGame.game.eu σ who =
      Math.Probability.expect
        (frontierGame.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who) :=
  frontierGame
    |>.eu_eq_optionKernel_expect σ who cutoff hbd

example
    (σ : frontierGame.game.Profile)
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport :
      outcome ∈ (frontierGame.game.outcomeKernel σ).support) :
    ∃ history :
        frontierGame.view.BoundedHistory
          (completionBound compiled),
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome := by
  rcases frontierGame.outcomeKernel_support_history σ hsupport with
    ⟨history, _hhistory, hterminal, houtcome, _hrun⟩
  exact ⟨history, hterminal, houtcome⟩

theorem compiled_nodeCount :
    compiled.graph.nodeCount = 8 := by
  simp [compiled, compile, graphProgram, core, hostOpenGuard, compileCore,
    EventGraph.Graph.nodeCount]

noncomputable def node (n : Nat) (h : n < 8) :
    Fin compiled.graph.nodeCount :=
  ⟨n, by
    rw [compiled_nodeCount]
    exact h⟩

noncomputable def node0 : Fin compiled.graph.nodeCount := node 0 (by decide)
noncomputable def node1 : Fin compiled.graph.nodeCount := node 1 (by decide)
noncomputable def node2 : Fin compiled.graph.nodeCount := node 2 (by decide)
noncomputable def node3 : Fin compiled.graph.nodeCount := node 3 (by decide)
noncomputable def node4 : Fin compiled.graph.nodeCount := node 4 (by decide)
noncomputable def node5 : Fin compiled.graph.nodeCount := node 5 (by decide)
noncomputable def node6 : Fin compiled.graph.nodeCount := node 6 (by decide)
noncomputable def node7 : Fin compiled.graph.nodeCount := node 7 (by decide)

/-- The guest's first hidden commitment does not depend on the host's hidden
car commitment. -/
example :
    compiled.graph.prereqs node1 = ∅ := by
  decide

/-- The host's door-opening commitment can use the hidden car and the public
first choice, but it does not directly depend on unrelated reveal order. -/
example :
    compiled.graph.prereqs node3 = {node0, node2} := by
  decide

/-- After Monty opens a door, the guest's switching commitment may condition
on their own first choice, its public reveal, and the opened door. -/
example :
    compiled.graph.prereqs node5 = {node1, node2, node4} := by
  decide

/-- Revealing the car waits for all prior commitments but not for the
independent switch reveal. -/
example :
    compiled.graph.prereqs node7 = {node0, node1, node3, node5} := by
  decide

example :
    compiled.payoffs.length = 2 := by
  simp [compiled, compile, graphProgram, core, hostOpenGuard, compileCore]

end MontyHall

end Examples
end Vegas
