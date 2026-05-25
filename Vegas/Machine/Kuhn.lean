import GameTheory.Theorems.Kuhn
import Vegas.Machine.KernelGame

namespace ObsModelCore

open Math.PMFProduct Math.ProbabilityMassFunction Math.ParameterizedChain

variable {ι σ : Type} {Obs : ι → Type}
variable {Act : (i : ι) → Obs i → Type}
variable {O : ObsModelCore ι σ Obs Act}

section MixedToBehavioralUpdate

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

/-- A player update to the mixed profile does not change any other player's
posterior action factor in the mixed-to-behavioral construction. -/
theorem mixedToBehavioralFactorAt_update_ne
    (μ : ∀ i, PMF (O.LocalStrategy i))
    {who i : ι} (hne : i ≠ who)
    (τ : PMF (O.LocalStrategy who))
    (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O) :
    mixedToBehavioralFactorAt (O := O)
        (Function.update μ who τ) i n ss π₀ =
      mixedToBehavioralFactorAt (O := O) μ i n ss π₀ := by
  simp [mixedToBehavioralFactorAt, Function.update_of_ne hne]

/-- A player update to the mixed profile does not change another player's
behavioral strategy produced by the mixed-to-behavioral construction, provided
the fallback profile is unchanged. -/
theorem mixedToBehavioralProfileWithFallback_update_ne
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (fallback : ObsModelCore.BehavioralProfile O)
    {who i : ι} (hne : i ≠ who)
    (τ : PMF (O.LocalStrategy who))
    (v : O.InfoState i) :
    mixedToBehavioralProfileWithFallback (O := O)
        (Function.update μ who τ) fallback i v =
      mixedToBehavioralProfileWithFallback (O := O) μ fallback i v := by
  classical
  unfold mixedToBehavioralProfileWithFallback
  by_cases h :
      ∃ (n : Nat) (ss : List σ) (π₀ : ObsModelCore.PureProfile O),
        O.projectStates i ss = v ∧
        pureRun (O.pureStep) O.init n π₀ ss ≠ 0
  · rw [dif_pos h, dif_pos h]
    simp [mixedToBehavioralFactorAt_update_ne (O := O) μ hne τ]
  · rw [dif_neg h, dif_neg h]

end MixedToBehavioralUpdate

end ObsModelCore

/-!
# Kuhn adapter for native round views

This module connects the native `Machine.RoundView` strategic presentation to
the generic `ObsModelCore` Kuhn theorem.  The adapter is proof-facing: public
game semantics remain the `RoundView` bounded pure/behavioral kernel games.

The adapter state is a bounded round history, not a raw machine state.  This
matters because a history records the realized player actions and observations,
so the generic perfect-recall hypotheses can be stated over exactly the same
information states used by native strategies.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} {M : Machine Player}

namespace RoundView

/-- A Kuhn-adapter action at a reachable native information state is an
optional native move that is legal at every bounded history realizing that
information state. -/
def KuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (player : Player)
    (info : view.ReachableInfoState horizon player) : Type :=
  { move : Option (view.Act player) //
    ∀ h : view.BoundedHistory horizon,
      view.reachableInfoStateOfHistory horizon player h = info →
        move ∈ view.boundedAvailableMoves horizon h player }

namespace KuhnActionAtInfo

variable {view : M.RoundView} {horizon : Nat}
variable {player : Player} {info : view.ReachableInfoState horizon player}

@[simp] theorem val_mk
    (move : Option (view.Act player))
    (hlegal :
      ∀ h : view.BoundedHistory horizon,
        view.reachableInfoStateOfHistory horizon player h = info →
          move ∈ view.boundedAvailableMoves horizon h player) :
    (Subtype.mk move hlegal :
      view.KuhnActionAtInfo horizon player info).1 = move := rfl

end KuhnActionAtInfo

open Classical in
noncomputable instance instFintypeKuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (player : Player) (info : view.ReachableInfoState horizon player)
    [Fintype (Option (view.Act player))] :
    Fintype (view.KuhnActionAtInfo horizon player info) := by
  unfold KuhnActionAtInfo
  infer_instance

/-- Menu observability gives a default adapter action at every reachable native
information state. -/
noncomputable def defaultKuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) (info : view.ReachableInfoState horizon player) :
    view.KuhnActionAtInfo horizon player info := by
  classical
  let h₀ : view.BoundedHistory horizon := Classical.choose info.2
  have hinfo₀ : h₀.playerView player = info.1 :=
    Classical.choose_spec info.2
  let move : Option (view.Act player) :=
    Classical.choose (view.boundedAvailableMoves_nonempty horizon h₀ player)
  have hmove : move ∈ view.boundedAvailableMoves horizon h₀ player :=
    Classical.choose_spec (view.boundedAvailableMoves_nonempty horizon h₀ player)
  refine ⟨move, ?_⟩
  intro h hinfo
  have hview :
      h₀.playerView player = h.playerView player := by
    have hinfo' := congrArg Subtype.val hinfo
    simpa [reachableInfoStateOfHistory, hinfo₀] using hinfo'.symm
  have hmenus := hMenus player h₀ h hview
  simpa [hmenus] using hmove

/-- Menu observability makes every adapter action type nonempty. -/
@[reducible]
noncomputable def instNonemptyKuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    ∀ player info,
      Nonempty (view.KuhnActionAtInfo horizon player info) :=
  fun player info =>
    ⟨view.defaultKuhnActionAtInfo horizon hMenus player info⟩

/-- Menu observability gives a canonical legal pure strategy: at each
reachable information state, choose an arbitrary move from the common legal
menu for that information state. -/
noncomputable def defaultBoundedPureStrategy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) :
    view.BoundedPureStrategy horizon player :=
  ⟨fun info =>
      (view.defaultKuhnActionAtInfo horizon hMenus player info).1,
    by
      intro history
      exact
        (view.defaultKuhnActionAtInfo horizon hMenus player
          (view.reachableInfoStateOfHistory horizon player history)).2
          history rfl⟩

/-- Menu observability makes every native bounded pure strategy space
nonempty. -/
@[reducible]
noncomputable def instNonemptyBoundedPureStrategyOfMenus
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    ∀ player, Nonempty (view.BoundedPureStrategy horizon player) :=
  fun player =>
    ⟨view.defaultBoundedPureStrategy horizon hMenus player⟩

/-- Joint Kuhn-adapter action at a concrete bounded history. -/
abbrev KuhnActionAtHistory
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) : Type :=
  ∀ player,
    view.KuhnActionAtInfo horizon player
      (view.reachableInfoStateOfHistory horizon player h)

/-- Forget the per-player legality proof carried by an adapter action. -/
def kuhnJointAction
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h) :
    JointAction view.Act :=
  fun player => (action player).1

/-- A nonterminal adapter action is a legal native bounded joint action. -/
theorem kuhnJointAction_legal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (action : view.KuhnActionAtHistory horizon h) :
    JointActionLegal view.Act
      (view.boundedActive horizon)
      (view.boundedTerminal horizon)
      (view.boundedAvailableActions horizon)
      h.lastState
      (view.kuhnJointAction horizon h action) :=
  (view.boundedLegal_iff_forall horizon).2
    ⟨hterm, fun player => (action player).2 h rfl⟩

/-- Repackage a nonterminal adapter action as the native legal-action subtype. -/
def kuhnLegalAction
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (action : view.KuhnActionAtHistory horizon h) :
    view.BoundedLegalAction horizon h.lastState :=
  ⟨view.kuhnJointAction horizon h action,
    view.kuhnJointAction_legal horizon h hterm action⟩

/-- Convert a native legal bounded joint action at a history into the
corresponding Kuhn-adapter action. `MenusObservable` upgrades legality at this
history to legality at every history with the same player information state. -/
def kuhnActionOfLegalAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    view.KuhnActionAtHistory horizon h :=
  fun player =>
    ⟨action.1 player,
      fun h' hinfo => by
        have hview :
            h.playerView player = h'.playerView player := by
          have hinfo' := congrArg Subtype.val hinfo
          simpa [reachableInfoStateOfHistory] using hinfo'.symm
        have hmenus := hMenus player h h' hview
        have hlocal :
            action.1 player ∈
              view.boundedAvailableMoves horizon h player := by
          rw [mem_boundedAvailableMoves_iff]
          exact (view.boundedLegal_iff_forall horizon).1 action.2 |>.2 player
        simpa [hmenus] using hlocal⟩

@[simp] theorem kuhnJointAction_of_legalAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    view.kuhnJointAction horizon h
        (view.kuhnActionOfLegalAction horizon hMenus h action) =
      action.1 := rfl

@[simp] theorem kuhnLegalAction_of_legalAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (action : view.BoundedLegalAction horizon h.lastState) :
    view.kuhnLegalAction horizon h hterm
        (view.kuhnActionOfLegalAction horizon hMenus h action) =
      action := by
  apply Subtype.ext
  rfl

/-- One adapter-machine step. Terminal histories absorb; otherwise the native
bounded transition is lifted to histories by appending the realized round. -/
noncomputable def kuhnStep
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h) :
    PMF (view.BoundedHistory horizon) := by
  classical
  if hterm : view.boundedTerminal horizon h.lastState then
    exact PMF.pure h
  else
    let legalAction := view.kuhnLegalAction horizon h hterm action
    exact
      (view.boundedTransition horizon h.lastState legalAction).map
        (fun dst => h.extendByOutcome legalAction dst)

@[simp] theorem kuhnStep_terminal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h)
    (hterm : view.boundedTerminal horizon h.lastState) :
    view.kuhnStep horizon h action = PMF.pure h := by
  simp [kuhnStep, hterm]

@[simp] theorem kuhnStep_nonterminal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h)
    (hterm : ¬ view.boundedTerminal horizon h.lastState) :
    view.kuhnStep horizon h action =
      (view.boundedTransition horizon h.lastState
          (view.kuhnLegalAction horizon h hterm action)).map
        (fun dst =>
          h.extendByOutcome
            (view.kuhnLegalAction horizon h hterm action) dst) := by
  simp [kuhnStep, hterm]

/-- The `ObsModelCore` proof adapter associated with a native bounded round
view.  Its states are native bounded histories and its observations are the
reachable native information states already used by `BoundedPureStrategy` and
`BoundedBehavioralStrategy`. -/
noncomputable def kuhnModel
    (view : M.RoundView) (horizon : Nat)
    (_hMenus : view.MenusObservable horizon) :
    ObsModelCore Player
      (view.BoundedHistory horizon)
      (fun player => view.ReachableInfoState horizon player)
      (fun player info => view.KuhnActionAtInfo horizon player info) where
  infoState := fun _ => InfoStateCore.identity _
  observe := fun player h =>
    view.reachableInfoStateOfHistory horizon player h
  machine :=
    { init := BoundedHistory.nil view horizon
      step := view.kuhnStep horizon }

@[simp] theorem kuhnModel_init
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    (view.kuhnModel horizon hMenus).init =
      BoundedHistory.nil view horizon := rfl

@[simp] theorem kuhnModel_observe
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) (h : view.BoundedHistory horizon) :
    (view.kuhnModel horizon hMenus).observe player h =
      view.reachableInfoStateOfHistory horizon player h := rfl

@[simp] theorem kuhnModel_projectStates
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) (trace : List (view.BoundedHistory horizon)) :
    (view.kuhnModel horizon hMenus).projectStates player trace =
      view.reachableInfoStateOfHistory horizon player
        ((view.kuhnModel horizon hMenus).lastState trace) := by
  have hcurrent :=
    ObsModelCore.currentObs_projectStates
      (view.kuhnModel horizon hMenus) player trace
  simpa [kuhnModel, ObsModelCore.currentObs] using hcurrent

@[simp]
theorem kuhnActionAtInfo_cast_val
    (view : M.RoundView) (horizon : Nat)
    {player : Player}
    {info info' : view.ReachableInfoState horizon player}
    (hinfo : info = info')
    (action : view.KuhnActionAtInfo horizon player info) :
    ((hinfo ▸ action : view.KuhnActionAtInfo horizon player info').1) =
      action.1 := by
  cases hinfo
  rfl

theorem kuhnJointAction_castJointAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (trace : List (view.BoundedHistory horizon))
    (action :
      ∀ player,
        view.KuhnActionAtInfo horizon player
          ((view.kuhnModel horizon hMenus).currentObs player
            ((view.kuhnModel horizon hMenus).projectStates player trace))) :
    view.kuhnJointAction horizon
        ((view.kuhnModel horizon hMenus).lastState trace)
        ((view.kuhnModel horizon hMenus).castJointAction trace action) =
      fun player => (action player).1 := by
  funext player
  simp [kuhnJointAction, ObsModelCore.castJointAction]

private theorem kuhnActionAtHistory_eq_of_terminal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (hterm : view.boundedTerminal horizon h.lastState)
    (left right : view.KuhnActionAtHistory horizon h) :
    left = right := by
  funext player
  apply Subtype.ext
  have hleft :
      (left player).1 ∈ view.boundedAvailableMoves horizon h player :=
    (left player).2 h rfl
  have hright :
      (right player).1 ∈ view.boundedAvailableMoves horizon h player :=
    (right player).2 h rfl
  rw [mem_boundedAvailableMoves_iff] at hleft hright
  have leftNone : (left player).1 = none := by
    cases hmove : (left player).1 with
    | none => rfl
    | some action =>
        cases hterm with
        | inl hmachine =>
            have hactive := view.terminal_active_eq_empty hmachine
            simp [boundedLocallyLegalAtState, boundedActive, hmove,
              hactive] at hleft
        | inr hcut =>
            simp [boundedLocallyLegalAtState, boundedActive,
              boundedAvailableActions, hmove, hcut] at hleft
  have rightNone : (right player).1 = none := by
    cases hmove : (right player).1 with
    | none => rfl
    | some action =>
        cases hterm with
        | inl hmachine =>
            have hactive := view.terminal_active_eq_empty hmachine
            simp [boundedLocallyLegalAtState, boundedActive, hmove,
              hactive] at hright
        | inr hcut =>
            simp [boundedLocallyLegalAtState, boundedActive,
              boundedAvailableActions, hmove, hcut] at hright
  rw [leftNone, rightNone]

/-- The Kuhn adapter step is action-deterministic: if two adapter joint actions
can reach the same next adapter history from the same source history, then the
joint actions are equal. The reason is structural: nonterminal successor
histories record the legal joint action that produced them, while terminal
histories allow only the no-op optional move. -/
theorem kuhnModel_stepActionDeterminism
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    ObsModelCore.StepActionDeterminism
      (view.kuhnModel horizon hMenus) := by
  classical
  intro h next left right hleft hright
  change view.kuhnStep horizon h left next ≠ 0 at hleft
  change view.kuhnStep horizon h right next ≠ 0 at hright
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · exact view.kuhnActionAtHistory_eq_of_terminal horizon h hterm left right
  · unfold kuhnStep at hleft hright
    rw [dif_neg hterm] at hleft hright
    let leftLegal := view.kuhnLegalAction horizon h hterm left
    let rightLegal := view.kuhnLegalAction horizon h hterm right
    change
      (PMF.map (fun dst => h.extendByOutcome leftLegal dst)
        (view.boundedTransition horizon h.lastState leftLegal)) next ≠ 0
        at hleft
    change
      (PMF.map (fun dst => h.extendByOutcome rightLegal dst)
        (view.boundedTransition horizon h.lastState rightLegal)) next ≠ 0
        at hright
    have hleftMem :
        next ∈
          (PMF.map (fun dst => h.extendByOutcome leftLegal dst)
            (view.boundedTransition horizon h.lastState leftLegal)).support :=
      (PMF.mem_support_iff _ _).2 hleft
    have hrightMem :
        next ∈
          (PMF.map (fun dst => h.extendByOutcome rightLegal dst)
            (view.boundedTransition horizon h.lastState rightLegal)).support :=
      (PMF.mem_support_iff _ _).2 hright
    rcases (PMF.mem_support_map_iff _ _ _).mp hleftMem with
      ⟨leftDst, hleftDstMem, hleftNext⟩
    rcases (PMF.mem_support_map_iff _ _ _).mp hrightMem with
      ⟨rightDst, hrightDstMem, hrightNext⟩
    have hleftDst :
        view.boundedTransition horizon h.lastState leftLegal leftDst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hleftDstMem
    have hrightDst :
        view.boundedTransition horizon h.lastState rightLegal rightDst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hrightDstMem
    rw [BoundedHistory.extendByOutcome_of_support h leftLegal leftDst hleftDst]
      at hleftNext
    rw [BoundedHistory.extendByOutcome_of_support h rightLegal rightDst hrightDst]
      at hrightNext
    have hhist :
        h.snoc leftLegal leftDst hleftDst =
          h.snoc rightLegal rightDst hrightDst := by
      rw [hleftNext, hrightNext]
    have hsteps := congrArg
      (fun history : view.BoundedHistory horizon => history.steps) hhist
    simp only [BoundedHistory.steps_snoc] at hsteps
    have hstepEq :=
      (Math.TraceRun.append_singleton_inj hsteps).2
    have hlegalEq : leftLegal = rightLegal := by
      injection hstepEq
    have hjointEq :
        view.kuhnJointAction horizon h left =
          view.kuhnJointAction horizon h right :=
      congrArg Subtype.val hlegalEq
    funext player
    apply Subtype.ext
    exact congrFun hjointEq player

private theorem kuhnPureStep_update_player_nonzero_iff
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    {profile : (view.kuhnModel horizon hMenus).PureProfile}
    {trace : List (view.BoundedHistory horizon)}
    {next : view.BoundedHistory horizon}
    (hsupport :
      (view.kuhnModel horizon hMenus).pureStep profile trace next ≠ 0)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    (view.kuhnModel horizon hMenus).pureStep
        (Function.update profile player strategy) trace next ≠ 0 ↔
      strategy ((view.kuhnModel horizon hMenus).projectStates player trace) =
        profile player
          ((view.kuhnModel horizon hMenus).projectStates player trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  have hDet : ObsModelCore.StepActionDeterminism O :=
    view.kuhnModel_stepActionDeterminism horizon hMenus
  rw [ObsModelCore.pureStep_nonzero_iff_forall_player
    (O := O) hDet hsupport (Function.update profile player strategy)]
  constructor
  · intro hall
    simpa [O] using hall player
  · intro hstrategy other
    by_cases hother : other = player
    · subst hother
      simpa [O] using hstrategy
    · simp [Function.update_of_ne hother]

private theorem lastState_take_succ
    {ι σ : Type} {Obs : ι → Type}
    {Act : (i : ι) → Obs i → Type}
    (O : ObsModelCore ι σ Obs Act) {states : List σ} {index : Nat}
    (hindex : index < states.length) :
    O.lastState (states.take (index + 1)) = states[index] := by
  unfold ObsModelCore.lastState
  rw [List.getLast?_take]
  have hget : states[index]? = some states[index] :=
    List.getElem?_eq_getElem hindex
  simp [hget]

/-- At a terminal native history, every Kuhn-adapter action for that exact
reachable information state is the no-op move. -/
private theorem kuhnActionAtInfo_eq_none_of_terminal
    (view : M.RoundView) (horizon : Nat)
    {player : Player} {info : view.ReachableInfoState horizon player}
    (h : view.BoundedHistory horizon)
    (hinfo : view.reachableInfoStateOfHistory horizon player h = info)
    (hterm : view.boundedTerminal horizon h.lastState)
    (action : view.KuhnActionAtInfo horizon player info) :
    action.1 = none := by
  have hlegal : action.1 ∈ view.boundedAvailableMoves horizon h player :=
    action.2 h hinfo
  rw [mem_boundedAvailableMoves_iff] at hlegal
  cases hmove : action.1 with
  | none => rfl
  | some choice =>
      cases hterm with
      | inl hmachine =>
          have hactive := view.terminal_active_eq_empty hmachine
          simp [boundedLocallyLegalAtState, boundedActive, hmove, hactive]
            at hlegal
      | inr hcut =>
          simp [boundedLocallyLegalAtState, boundedActive,
            boundedAvailableActions, hmove, hcut] at hlegal

/-- Terminal reachable information states have a singleton adapter action
space. -/
private theorem kuhnActionAtInfo_subsingleton_of_terminal
    (view : M.RoundView) (horizon : Nat)
    {player : Player} {info : view.ReachableInfoState horizon player}
    (h : view.BoundedHistory horizon)
    (hinfo : view.reachableInfoStateOfHistory horizon player h = info)
    (hterm : view.boundedTerminal horizon h.lastState) :
    Subsingleton (view.KuhnActionAtInfo horizon player info) := by
  refine ⟨fun left right => ?_⟩
  apply Subtype.ext
  rw [view.kuhnActionAtInfo_eq_none_of_terminal horizon h hinfo hterm left,
    view.kuhnActionAtInfo_eq_none_of_terminal horizon h hinfo hterm right]

/-- A supported Kuhn-adapter step either stutters at a terminal history or
strictly advances the native history depth by one. -/
private theorem kuhnStep_support_terminal_or_depth_succ
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h)
    {next : view.BoundedHistory horizon}
    (hsupport : view.kuhnStep horizon h action next ≠ 0) :
    (view.boundedTerminal horizon h.lastState ∧ next = h) ∨
      (¬ view.boundedTerminal horizon h.lastState ∧
        next.lastState.depth = h.lastState.depth + 1) := by
  classical
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · left
    have hnext : next = h := by
      have hmem : next ∈ (view.kuhnStep horizon h action).support :=
        (PMF.mem_support_iff _ _).2 hsupport
      rw [view.kuhnStep_terminal horizon h action hterm,
        PMF.support_pure, Set.mem_singleton_iff] at hmem
      exact hmem
    exact ⟨hterm, hnext⟩
  · right
    rw [view.kuhnStep_nonterminal horizon h action hterm] at hsupport
    have hmem :
        next ∈
          (PMF.map
            (fun dst =>
              h.extendByOutcome
                (view.kuhnLegalAction horizon h hterm action) dst)
            (view.boundedTransition horizon h.lastState
              (view.kuhnLegalAction horizon h hterm action))).support :=
      (PMF.mem_support_iff _ _).2 hsupport
    rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
      ⟨dst, hdstMem, hnextEq⟩
    have hdst :
        view.boundedTransition horizon h.lastState
            (view.kuhnLegalAction horizon h hterm action) dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdstMem
    have hdstDepth :
        dst.depth = h.lastState.depth + 1 :=
      view.boundedTransition_support_depth horizon h.lastState
        (view.kuhnLegalAction horizon h hterm action) hdst
    subst next
    refine ⟨hterm, ?_⟩
    rw [BoundedHistory.extendByOutcome_of_support h
      (view.kuhnLegalAction horizon h hterm action) dst hdst]
    simp [hdstDepth]

/-- The same terminal-or-depth-advance property for the pure-step kernel used
by `runDistPure`. -/
private theorem kuhnPureStep_support_terminal_or_depth_succ
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (profile : (view.kuhnModel horizon hMenus).PureProfile)
    (trace : List (view.BoundedHistory horizon))
    {next : view.BoundedHistory horizon}
    (hsupport :
      (view.kuhnModel horizon hMenus).pureStep profile trace next ≠ 0) :
    (view.boundedTerminal horizon
        ((view.kuhnModel horizon hMenus).lastState trace).lastState ∧
      next = (view.kuhnModel horizon hMenus).lastState trace) ∨
      (¬ view.boundedTerminal horizon
          ((view.kuhnModel horizon hMenus).lastState trace).lastState ∧
        next.lastState.depth =
          ((view.kuhnModel horizon hMenus).lastState trace).lastState.depth +
            1) := by
  classical
  let O := view.kuhnModel horizon hMenus
  change
    (O.stepDist (O.pureToBehavioral profile) trace) next ≠ 0
      at hsupport
  change
    ((O.jointActionDist (O.pureToBehavioral profile) trace).bind
      (fun action => O.step (O.lastState trace)
        (O.castJointAction trace action))) next ≠ 0 at hsupport
  have hmem :
      next ∈
        (((O.jointActionDist (O.pureToBehavioral profile) trace).bind
          (fun action => O.step (O.lastState trace)
            (O.castJointAction trace action))).support) :=
    (PMF.mem_support_iff _ _).2 hsupport
  rw [PMF.mem_support_bind_iff] at hmem
  rcases hmem with ⟨action, _haction, hnext⟩
  change
    view.kuhnStep horizon (O.lastState trace)
      (O.castJointAction trace action) next ≠ 0 at hnext
  exact
    view.kuhnStep_support_terminal_or_depth_succ horizon
      (O.lastState trace) (O.castJointAction trace action) hnext

/-- Along a supported pure adapter trace, if a later history is nonterminal
then every strictly earlier trace position has smaller native history depth. -/
private theorem kuhnTrace_depth_lt_of_later_nonterminal
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (profile : (view.kuhnModel horizon hMenus).PureProfile)
    {steps : Nat} {states : List (view.BoundedHistory horizon)}
    (hrun :
      (view.kuhnModel horizon hMenus).runDistPure steps profile states ≠ 0)
    {early late : Nat} (hearlyLate : early < late)
    (hlate : late < states.length)
    (hlateNot :
      ¬ view.boundedTerminal horizon
        (((view.kuhnModel horizon hMenus).lastState
          (states.take (late + 1))).lastState)) :
    (((view.kuhnModel horizon hMenus).lastState
        (states.take (early + 1))).lastState.depth) <
      (((view.kuhnModel horizon hMenus).lastState
        (states.take (late + 1))).lastState.depth) := by
  classical
  let O := view.kuhnModel horizon hMenus
  change O.runDistPure steps profile states ≠ 0 at hrun
  rw [O.runDistPure_eq_pureRun] at hrun
  induction late generalizing early with
  | zero =>
      omega
  | succ m ih =>
      have hmLen : m < states.length := by omega
      have hstep :
          O.pureStep profile (states.take (m + 1)) states[m + 1] ≠ 0 := by
        exact
          Math.ParameterizedChain.pureRun_step_nonzero
            O.pureStep O.init steps profile states hrun m (by omega)
      have hnextLast :
          O.lastState (states.take (m + 1 + 1)) = states[m + 1] :=
        lastState_take_succ O hlate
      have hsourceLast :
          O.lastState (states.take (m + 1)) = states[m] :=
        lastState_take_succ O hmLen
      have hnextLast' :
          (view.kuhnModel horizon hMenus).lastState
              (states.take (m + 1 + 1)) = states[m + 1] := by
        simpa [O] using hnextLast
      have hsourceLast' :
          (view.kuhnModel horizon hMenus).lastState
              (states.take (m + 1)) = states[m] := by
        simpa [O] using hsourceLast
      have hlateNot' :
          ¬ view.boundedTerminal horizon (states[m + 1]).lastState := by
        simpa [hnextLast'] using hlateNot
      have hstruct :=
        view.kuhnPureStep_support_terminal_or_depth_succ
          horizon hMenus profile (states.take (m + 1)) hstep
      rcases hstruct with hterminal | hadvance
      · rcases hterminal with ⟨hsourceTerm, hnextEq⟩
        exact False.elim (hlateNot' (by simpa [hnextEq] using hsourceTerm))
      · rcases hadvance with ⟨hsourceNot, hdepthSucc⟩
        by_cases heq : early = m
        · subst early
          have hdepthSucc' :
              states[m + 1].lastState.depth =
                states[m].lastState.depth + 1 := by
            simpa [hsourceLast'] using hdepthSucc
          rw [hsourceLast', hnextLast']
          omega
        · have hearlyM : early < m := by omega
          have hltPrev :
              (O.lastState (states.take (early + 1))).lastState.depth <
                (O.lastState (states.take (m + 1))).lastState.depth :=
            ih hearlyM hmLen hsourceNot
          have hltPrev' :
              ((view.kuhnModel horizon hMenus).lastState
                  (states.take (early + 1))).lastState.depth <
                states[m].lastState.depth := by
            simpa [O, hsourceLast'] using hltPrev
          have hdepthSucc' :
              states[m + 1].lastState.depth =
                states[m].lastState.depth + 1 := by
            simpa [hsourceLast'] using hdepthSucc
          rw [hnextLast']
          omega

/-- The native round-view Kuhn adapter cannot revisit a nontrivial
information state along a supported pure trace.  If a reachable information
state repeats, all intervening adapter steps are terminal stutters, and the
adapter action space is the singleton no-op move. -/
theorem kuhnModel_noNontrivialInfoStateRepeat
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)] :
    ObsModelCore.NoNontrivialInfoStateRepeat
      (view.kuhnModel horizon hMenus) := by
  classical
  let O := view.kuhnModel horizon hMenus
  intro player profile steps states hrun j₁ j₂ hjlt hjlen hEq
  let h₁ : view.BoundedHistory horizon :=
    O.lastState (states.take (j₁ + 1))
  let h₂ : view.BoundedHistory horizon :=
    O.lastState (states.take (j₂ + 1))
  have hinfoEq :
      view.reachableInfoStateOfHistory horizon player h₁ =
        view.reachableInfoStateOfHistory horizon player h₂ := by
    simpa [O, h₁, h₂] using hEq
  have hviewEq : h₁.playerView player = h₂.playerView player :=
    congrArg Subtype.val hinfoEq
  have hdepthEq : h₁.lastState.depth = h₂.lastState.depth :=
    BoundedHistory.depth_eq_of_playerView_eq
      (view := view) (horizon := horizon) h₁ h₂ player hviewEq
  by_cases hterm : view.boundedTerminal horizon h₂.lastState
  · have hsub :
        Subsingleton (view.KuhnActionAtInfo horizon player
          (view.reachableInfoStateOfHistory horizon player h₂)) :=
      view.kuhnActionAtInfo_subsingleton_of_terminal horizon h₂ rfl hterm
    simpa [O, h₂, ObsModelCore.currentObs] using hsub
  · have hlt :
        h₁.lastState.depth < h₂.lastState.depth := by
      have hraw :=
        view.kuhnTrace_depth_lt_of_later_nonterminal
          horizon hMenus profile hrun hjlt hjlen hterm
      simpa [O, h₁, h₂] using hraw
    omega

/-- Local support/perfect-recall condition needed for mixed-to-behavioral
Kuhn realization on the adapter model. It says that replacing one player's
local strategy preserves reachability of a trace according only to that
player's endpoint information state. -/
def KuhnLocality
    (view : M.RoundView) (horizon : Nat)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (hMenus : view.MenusObservable horizon) : Prop :=
  ∀ player,
    ObsModelCore.ObsLocalFeasibilityFull
      (view.kuhnModel horizon hMenus) player

/-- Information prefix obtained by consuming a visible event suffix. This is
extensionally `pref ++ events`, but its recursive shape matches
`KuhnLocalSupportReqFrom`. -/
def KuhnInfoAfter
    (view : M.RoundView) (player : Player)
    (pref events : view.InfoState player) : view.InfoState player :=
  match events with
  | [] => pref
  | event :: rest =>
      view.KuhnInfoAfter player (pref ++ [event]) rest

theorem KuhnInfoAfter_eq_append
    (view : M.RoundView) (player : Player)
    (pref events : view.InfoState player) :
    view.KuhnInfoAfter player pref events = pref ++ events := by
  induction events generalizing pref with
  | nil =>
      simp [KuhnInfoAfter]
  | cons event rest ih =>
      simp [KuhnInfoAfter, ih, List.append_assoc]

/-- A local strategy chooses `action` at a concrete reachable information
state represented by the raw player-visible event list `info`. -/
def KuhnStrategyChoosesAt
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (info : view.InfoState player)
    (action : view.Act player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) : Prop :=
  ∀ hinfo : ∃ h : view.BoundedHistory horizon,
      h.playerView player = info,
    (strategy ⟨info, hinfo⟩).1 = some action

/-- Support requirements induced by a player-visible event suffix.

The accumulator `pref` is the information state before reading `events`.
Observation events add no strategic support requirement.  An own-action event
requires a replacement local strategy to choose that action at the preceding
reachable prefix. -/
def KuhnLocalSupportReqFrom
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) : Prop :=
  match events with
  | [] => True
  | event :: rest =>
      match event with
      | PlayerEvent.obs _ _ =>
          view.KuhnLocalSupportReqFrom horizon hMenus player
            (pref ++ [event]) rest strategy
      | PlayerEvent.act action =>
          (∀ hprefix : ∃ h : view.BoundedHistory horizon,
              h.playerView player = pref,
            (strategy ⟨pref, hprefix⟩).1 = some action) ∧
          view.KuhnLocalSupportReqFrom horizon hMenus player
            (pref ++ [event]) rest strategy

/-- A replacement local strategy supports an endpoint information state when it
agrees with every own-action event recorded in that state. -/
def KuhnLocalSupportReq
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (info : (view.kuhnModel horizon hMenus).InfoState player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) : Prop :=
  view.KuhnLocalSupportReqFrom horizon hMenus player [] info.1 strategy

theorem KuhnLocalSupportReqFrom_append_obs
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (priv : M.Obs player) (pub : M.Public)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReqFrom horizon hMenus player pref
        (events ++ [PlayerEvent.obs priv pub]) strategy ↔
      view.KuhnLocalSupportReqFrom horizon hMenus player pref
        events strategy := by
  induction events generalizing pref with
  | nil =>
      simp [KuhnLocalSupportReqFrom]
  | cons event rest ih =>
      cases event <;>
        simp [KuhnLocalSupportReqFrom, ih]

theorem KuhnLocalSupportReqFrom_append_act_obs
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (action : view.Act player)
    (priv : M.Obs player) (pub : M.Public)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReqFrom horizon hMenus player pref
        (events ++ [PlayerEvent.act action, PlayerEvent.obs priv pub])
        strategy ↔
      view.KuhnLocalSupportReqFrom horizon hMenus player pref
          events strategy ∧
        view.KuhnStrategyChoosesAt horizon hMenus player
          (view.KuhnInfoAfter player pref events) action strategy := by
  induction events generalizing pref with
  | nil =>
      simp [KuhnLocalSupportReqFrom, KuhnInfoAfter,
        KuhnStrategyChoosesAt]
  | cons event rest ih =>
      cases event <;>
        simp [KuhnLocalSupportReqFrom, KuhnInfoAfter, ih,
          and_assoc]

theorem KuhnLocalSupportReqFrom_append_playerView
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (step : view.BoundedStep horizon)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReqFrom horizon hMenus player pref
        (events ++ step.playerView player) strategy ↔
      view.KuhnLocalSupportReqFrom horizon hMenus player pref
          events strategy ∧
        match step.ownAction? player with
        | none => True
        | some action =>
            view.KuhnStrategyChoosesAt horizon hMenus player
              (view.KuhnInfoAfter player pref events) action strategy := by
  cases hact : step.ownAction? player with
  | none =>
      simp [BoundedStep.playerView, hact,
        KuhnLocalSupportReqFrom_append_obs]
  | some action =>
      simp [BoundedStep.playerView, hact,
        KuhnLocalSupportReqFrom_append_act_obs]

private theorem kuhnActionAtInfo_eq_of_base_none
    (view : M.RoundView) (horizon : Nat)
    {player : Player} {info : view.ReachableInfoState horizon player}
    (h : view.BoundedHistory horizon)
    (hinfo : view.reachableInfoStateOfHistory horizon player h = info)
    (base action : view.KuhnActionAtInfo horizon player info)
    (hbase : base.1 = none) :
    action = base := by
  apply Subtype.ext
  have hbaseLegal : none ∈ view.boundedAvailableMoves horizon h player := by
    simpa [hbase] using base.2 h hinfo
  have hactionLegal : action.1 ∈
      view.boundedAvailableMoves horizon h player :=
    action.2 h hinfo
  rw [mem_boundedAvailableMoves_iff] at hbaseLegal hactionLegal
  cases haction : action.1 with
  | none =>
      simp [hbase]
  | some choice =>
      exfalso
      have hlocal :
          view.boundedLocallyLegalAtState horizon h.lastState player
            (some choice) := by
        simpa [boundedLocallyLegalAtState, haction] using hactionLegal
      have hactive : player ∈ view.boundedActive horizon h.lastState := by
        exact hlocal.1
      exact hbaseLegal hactive

private theorem kuhnPureStep_support_req_iff
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    {profile : (view.kuhnModel horizon hMenus).PureProfile}
    {trace : List (view.BoundedHistory horizon)}
    {next : view.BoundedHistory horizon}
    (hsupport :
      (view.kuhnModel horizon hMenus).pureStep profile trace next ≠ 0)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReq horizon hMenus player
        ((view.kuhnModel horizon hMenus).projectStates player
          (trace ++ [next])) strategy ↔
      view.KuhnLocalSupportReq horizon hMenus player
          ((view.kuhnModel horizon hMenus).projectStates player trace)
          strategy ∧
        strategy
          ((view.kuhnModel horizon hMenus).projectStates player trace) =
          profile player
            ((view.kuhnModel horizon hMenus).projectStates player trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let h := O.lastState trace
  let action : view.KuhnActionAtHistory horizon h :=
    O.castJointAction trace
      (fun player => profile player (O.projectStates player trace))
  have hprefixInfo :
      O.projectStates player trace =
        view.reachableInfoStateOfHistory horizon player h := by
    simp [O, h]
  rw [ObsModelCore.pureStep_eq] at hsupport
  change view.kuhnStep horizon h action next ≠ 0 at hsupport
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · have hnext : next = h := by
      have hmem : next ∈ (view.kuhnStep horizon h action).support :=
        (PMF.mem_support_iff _ _).2 hsupport
      rw [view.kuhnStep_terminal horizon h action hterm,
        PMF.support_pure, Set.mem_singleton_iff] at hmem
      exact hmem
    subst next
    have hstrategy :
        strategy (O.projectStates player trace) =
          profile player (O.projectStates player trace) := by
      rw [hprefixInfo]
      dsimp [O, kuhnModel, ObsModelCore.currentObs]
      haveI :
          Subsingleton
            (view.KuhnActionAtInfo horizon player
              (view.reachableInfoStateOfHistory horizon player h)) :=
        view.kuhnActionAtInfo_subsingleton_of_terminal horizon h rfl hterm
      exact Subsingleton.elim _ _
    have hfinalSame :
        O.projectStates player (trace ++ [h]) =
          O.projectStates player trace := by
      have htmp :=
        view.kuhnModel_projectStates horizon hMenus player (trace ++ [h])
      rw [ObsModelCore.lastState_append_singleton] at htmp
      have htmp' :
          O.projectStates player (trace ++ [h]) =
            view.reachableInfoStateOfHistory horizon player h := by
        simpa [O] using htmp
      exact htmp'.trans hprefixInfo.symm
    rw [hfinalSame]
    constructor
    · intro hreq
      exact ⟨by
        simpa [KuhnLocalSupportReq, O, h] using hreq, hstrategy⟩
    · intro hreq
      simpa [KuhnLocalSupportReq, O, h] using hreq.1
  · rw [view.kuhnStep_nonterminal horizon h action hterm] at hsupport
    let legalAction := view.kuhnLegalAction horizon h hterm action
    have hmem :
        next ∈
          (PMF.map
            (fun dst => h.extendByOutcome legalAction dst)
            (view.boundedTransition horizon h.lastState legalAction)).support :=
      (PMF.mem_support_iff _ _).2 hsupport
    rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
      ⟨dst, hdstMem, hnextEq⟩
    have hdst :
        view.boundedTransition horizon h.lastState legalAction dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdstMem
    have hnextSnoc :
        next = h.snoc legalAction dst hdst := by
      rw [BoundedHistory.extendByOutcome_of_support h legalAction dst hdst]
        at hnextEq
      exact hnextEq.symm
    let step : view.BoundedStep horizon :=
      ⟨h.lastState, legalAction, dst, hdst⟩
    have hnextView :
        next.playerView player =
          h.playerView player ++ step.playerView player := by
      rw [hnextSnoc]
      exact BoundedHistory.playerView_snoc h player legalAction dst hdst
    have hJoint :
        view.kuhnJointAction horizon h action =
          fun player =>
            (profile player (O.projectStates player trace)).1 := by
      dsimp [action]
      exact
        view.kuhnJointAction_castJointAction horizon hMenus trace
          (fun player => profile player (O.projectStates player trace))
    have hstepOwn :
        step.ownAction? player =
          (profile player (O.projectStates player trace)).1 := by
      change legalAction.1 player =
        (profile player (O.projectStates player trace)).1
      simpa [legalAction, kuhnLegalAction] using congrFun hJoint player
    rw [hprefixInfo] at hstepOwn
    have hfinalInfo :
        O.projectStates player (trace ++ [next]) =
          view.reachableInfoStateOfHistory horizon player next := by
      have htmp :=
        view.kuhnModel_projectStates horizon hMenus player (trace ++ [next])
      rw [ObsModelCore.lastState_append_singleton] at htmp
      simpa [O] using htmp
    rw [hfinalInfo, hprefixInfo]
    simp only [KuhnLocalSupportReq,
      reachableInfoStateOfHistory_val]
    rw [hnextView]
    have happend :=
      view.KuhnLocalSupportReqFrom_append_playerView horizon hMenus player
        [] (h.playerView player) step strategy
    rw [happend]
    rw [view.KuhnInfoAfter_eq_append player [] (h.playerView player)]
    simp only [List.nil_append]
    cases hmove : (profile player
        (view.reachableInfoStateOfHistory horizon player h)).1 with
    | none =>
        have hstepNone : step.ownAction? player = none := by
          simpa [hmove] using hstepOwn
        have hstrategy :
            strategy (view.reachableInfoStateOfHistory horizon player h) =
              profile player
                (view.reachableInfoStateOfHistory horizon player h) := by
          exact
            view.kuhnActionAtInfo_eq_of_base_none horizon h rfl
              (profile player
                (view.reachableInfoStateOfHistory horizon player h))
              (strategy
                (view.reachableInfoStateOfHistory horizon player h))
              hmove
        simp only [hstepNone]
        apply and_congr_right_iff.mpr
        intro _hreq
        exact ⟨fun _ => hstrategy, fun _ => trivial⟩
    | some move =>
        have hstepSome : step.ownAction? player = some move := by
          simpa [hmove] using hstepOwn
        simp only [hstepSome]
        constructor
        · intro hreq
          refine ⟨hreq.1, ?_⟩
          apply Subtype.ext
          rw [hmove]
          exact hreq.2 ⟨h, rfl⟩
        · intro hreq
          refine ⟨hreq.1, ?_⟩
          intro hprefix
          have harg :
              (⟨h.playerView player, hprefix⟩ :
                view.ReachableInfoState horizon player) =
                view.reachableInfoStateOfHistory horizon player h := by
            apply Subtype.ext
            rfl
          have hstrategyAtVal :
              (strategy ⟨h.playerView player, hprefix⟩).1 =
                (strategy
                  (view.reachableInfoStateOfHistory horizon player h)).1 := by
            cases harg
            rfl
          rw [hstrategyAtVal]
          have hval := congrArg Subtype.val hreq.2
          rw [hmove] at hval
          exact hval

private theorem kuhnPureRun_update_support_iff_req
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (steps : Nat)
    {profile : (view.kuhnModel horizon hMenus).PureProfile}
    {trace : List (view.BoundedHistory horizon)}
    (hsupport :
      Math.ParameterizedChain.pureRun
          ((view.kuhnModel horizon hMenus).pureStep)
          ((view.kuhnModel horizon hMenus).init)
          steps profile trace ≠ 0)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    Math.ParameterizedChain.pureRun
        ((view.kuhnModel horizon hMenus).pureStep)
        ((view.kuhnModel horizon hMenus).init)
        steps (Function.update profile player strategy) trace ≠ 0 ↔
      view.KuhnLocalSupportReq horizon hMenus player
        ((view.kuhnModel horizon hMenus).projectStates player trace)
        strategy := by
  classical
  let O := view.kuhnModel horizon hMenus
  induction steps generalizing trace profile with
  | zero =>
      simp only [Math.ParameterizedChain.pureRun,
        Math.TraceRun.traceRun_zero, PMF.pure_apply] at hsupport ⊢
      have htraceRaw :
          trace = [(view.kuhnModel horizon hMenus).init] := by
        by_contra hne
        have hne' : ¬ trace = [BoundedHistory.nil view horizon] := by
          simpa [kuhnModel] using hne
        exact hsupport (by simp [hne'])
      have htrace : trace = [O.init] := by
        simpa [O] using htraceRaw
      subst htrace
      have hinfo :
          O.projectStates player [O.init] =
            view.reachableInfoStateOfHistory horizon player
              (BoundedHistory.nil view horizon) := by
        have hproject :=
          view.kuhnModel_projectStates horizon hMenus player [O.init]
        simpa [O, kuhnModel] using hproject
      rw [hinfo]
      constructor
      · intro _
        change True
        trivial
      · intro _
        simp [O, kuhnModel]
  | succ steps ih =>
      rcases List.eq_nil_or_concat trace with rfl | ⟨pref, next, rfl⟩
      · exact absurd
          (Math.ParameterizedChain.pureRun_succ_nil
            (O.pureStep) O.init steps profile) hsupport
      · simp only [List.concat_eq_append,
          Math.ParameterizedChain.pureRun_succ_append] at hsupport ⊢
        have hprefix :
            Math.ParameterizedChain.pureRun (O.pureStep) O.init
              steps profile pref ≠ 0 :=
          left_ne_zero_of_mul hsupport
        have hstep :
            O.pureStep profile pref next ≠ 0 :=
          right_ne_zero_of_mul hsupport
        have ihPrefix :=
          ih (profile := profile) hprefix
        have hstepReq :=
          view.kuhnPureStep_support_req_iff horizon hMenus
            hstep player strategy
        have hstepUpdate :=
          view.kuhnPureStep_update_player_nonzero_iff horizon hMenus
            hstep player strategy
        constructor
        · intro hrun
          have hrunPrefix :
              Math.ParameterizedChain.pureRun (O.pureStep) O.init
                steps (Function.update profile player strategy) pref ≠ 0 :=
            left_ne_zero_of_mul hrun
          have hrunStep :
              O.pureStep (Function.update profile player strategy)
                pref next ≠ 0 :=
            right_ne_zero_of_mul hrun
          exact hstepReq.mpr
            ⟨ihPrefix.mp hrunPrefix, hstepUpdate.mp hrunStep⟩
        · intro hreq
          have hparts := hstepReq.mp hreq
          have hrunPrefix :
              Math.ParameterizedChain.pureRun (O.pureStep) O.init
                steps (Function.update profile player strategy) pref ≠ 0 :=
            ihPrefix.mpr hparts.1
          have hrunStep :
              O.pureStep (Function.update profile player strategy)
                pref next ≠ 0 :=
            hstepUpdate.mpr hparts.2
          exact mul_ne_zero hrunPrefix hrunStep

def kuhnModel_localSupportSignatureFull
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (player : Player) :
    ObsModelCore.LocalSupportSignatureFull
      (view.kuhnModel horizon hMenus) player where
  Req := fun info strategy =>
    view.KuhnLocalSupportReq horizon hMenus player info strategy
  support_iff := by
    intro steps profile trace hsupport strategy
    exact
      view.kuhnPureRun_update_support_iff_req horizon hMenus
        steps hsupport player strategy

theorem kuhnModel_obsLocalFeasibilityFull
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (player : Player) :
    ObsModelCore.ObsLocalFeasibilityFull
      (view.kuhnModel horizon hMenus) player :=
  ObsModelCore.obsLocalFeasibilityFull_of_localSupportSignatureFull
    player
    (view.kuhnModel_localSupportSignatureFull horizon hMenus player)

theorem kuhnLocality
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))] :
    view.KuhnLocality horizon hMenus := by
  intro player
  exact view.kuhnModel_obsLocalFeasibilityFull horizon hMenus player

open Classical in
noncomputable instance instFintypeKuhnModelInfoState
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player] [Fintype M.State]
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player) :
    Fintype ((view.kuhnModel horizon hMenus).InfoState player) := by
  dsimp [kuhnModel, ObsModelCore.InfoState]
  exact view.instFintypeReachableInfoState horizon player

open Classical in
noncomputable instance instFintypeKuhnModelLocalStrategy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player)
    [Finite ((view.kuhnModel horizon hMenus).InfoState player)] :
    Fintype ((view.kuhnModel horizon hMenus).LocalStrategy player) := by
  letI : Fintype ((view.kuhnModel horizon hMenus).InfoState player) :=
    Fintype.ofFinite _
  dsimp [ObsModelCore.LocalStrategy]
  infer_instance

/-- Embed a native legal pure strategy into the Kuhn adapter. -/
noncomputable def pureStrategyToKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (strategy : view.BoundedPureStrategy horizon player) :
    (view.kuhnModel horizon hMenus).LocalStrategy player :=
  fun info =>
    ⟨strategy.1 info,
      fun h hinfo => by
        have hlegal := strategy.2 h
        simpa [hinfo] using hlegal⟩

/-- Embed a native legal pure profile into the Kuhn adapter. -/
noncomputable def pureProfileToKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (profile : view.BoundedPureProfile horizon) :
    (view.kuhnModel horizon hMenus).PureProfile :=
  fun player =>
    view.pureStrategyToKuhn horizon hMenus player (profile player)

/-- Forget a Kuhn-adapter pure strategy back to a native legal pure strategy. -/
noncomputable def pureStrategyOfKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.BoundedPureStrategy horizon player :=
  ⟨fun info => (strategy info).1,
    fun h => (strategy
      (view.reachableInfoStateOfHistory horizon player h)).2 h rfl⟩

/-- Forget a Kuhn-adapter pure profile back to a native legal pure profile. -/
noncomputable def pureProfileOfKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (profile : (view.kuhnModel horizon hMenus).PureProfile) :
    view.BoundedPureProfile horizon :=
  fun player =>
    view.pureStrategyOfKuhn horizon hMenus player (profile player)

@[simp]
theorem pureStrategyOfKuhn_pureStrategyToKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (strategy : view.BoundedPureStrategy horizon player) :
    view.pureStrategyOfKuhn horizon hMenus player
        (view.pureStrategyToKuhn horizon hMenus player strategy) =
      strategy := by
  apply Subtype.ext
  rfl

@[simp]
theorem pureStrategyToKuhn_pureStrategyOfKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.pureStrategyToKuhn horizon hMenus player
        (view.pureStrategyOfKuhn horizon hMenus player strategy) =
      strategy := by
  funext info
  apply Subtype.ext
  rfl

@[simp]
theorem pureProfileOfKuhn_pureProfileToKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (profile : view.BoundedPureProfile horizon) :
    view.pureProfileOfKuhn horizon hMenus
        (view.pureProfileToKuhn horizon hMenus profile) =
      profile := by
  funext player
  exact
    view.pureStrategyOfKuhn_pureStrategyToKuhn horizon hMenus player
      (profile player)

/-- Forget a Kuhn-adapter behavioral profile back to a native legal behavioral
profile by erasing the action-subtype proof in each local distribution. -/
noncomputable def behavioralProfileOfKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (profile :
      (view.kuhnModel horizon hMenus).BehavioralProfile) :
    view.BoundedBehavioralProfile horizon :=
  fun player =>
    ⟨fun info => PMF.map Subtype.val (profile player info),
      fun h {move} hmove => by
        rcases (PMF.mem_support_map_iff _ _ _).mp hmove with
          ⟨action, haction, hvalue⟩
        rw [← hvalue]
        exact action.2 h rfl⟩

private theorem sum_subtype_eq_sum_dite
    {α M₀ : Type} [Fintype α] [AddCommMonoid M₀]
    {p : α → Prop} [DecidablePred p] (F : (a : α) → p a → M₀) :
    (∑ x : {a : α // p a}, F x.1 x.2) =
      ∑ a : α, if h : p a then F a h else 0 := by
  classical
  let f : α → M₀ := fun a => if h : p a then F a h else 0
  have hsub :
      (Finset.subtype p (Finset.univ : Finset α)).sum
          (fun x => f x.1) =
        ∑ x : {a : α // p a}, F x.1 x.2 := by
    have huniv :
        Finset.subtype p (Finset.univ : Finset α) =
          (Finset.univ : Finset {a : α // p a}) := by
      ext x
      simp
    rw [huniv]
    refine Finset.sum_congr rfl ?_
    intro x _
    simp only [f]
    have hp : p x.1 := x.2
    simp [hp]
  calc
    ∑ x : {a : α // p a}, F x.1 x.2 =
      (Finset.subtype p (Finset.univ : Finset α)).sum
        (fun x => f x.1) := hsub.symm
    _ = ∑ a : α, if p a then f a else 0 := by
      simpa [Finset.sum_filter] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset α)) (p := p) (f := f))
    _ = ∑ a : α, f a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases hp : p a <;> simp [f, hp]
    _ = ∑ a : α, if h : p a then F a h else 0 := rfl

theorem behavioralStrategy_mass_zero_of_not_kuhnLegal
    (view : M.RoundView) (horizon : Nat)
    (player : Player)
    (strategy : view.BoundedBehavioralStrategy horizon player)
    (info : view.ReachableInfoState horizon player)
    {move : Option (view.Act player)}
    (hillegal :
      ¬ ∀ h : view.BoundedHistory horizon,
        view.reachableInfoStateOfHistory horizon player h = info →
          move ∈ view.boundedAvailableMoves horizon h player) :
    strategy.1 info move = 0 := by
  classical
  by_contra hnonzero
  have hsupport : move ∈ (strategy.1 info).support :=
    (PMF.mem_support_iff _ _).2 hnonzero
  push Not at hillegal
  rcases hillegal with ⟨h, hinfo, hmove⟩
  have hsupportAtHistory :
      move ∈
        (strategy.1
          (view.reachableInfoStateOfHistory horizon player h)).support := by
    simpa [hinfo] using hsupport
  exact hmove (strategy.2 h hsupportAtHistory)

open Classical in
theorem behavioralStrategy_kuhnActionMass_eq_one
    (view : M.RoundView) (horizon : Nat)
    (player : Player)
    [Fintype (Option (view.Act player))]
    (strategy : view.BoundedBehavioralStrategy horizon player)
    (info : view.ReachableInfoState horizon player) :
    ∑ action : view.KuhnActionAtInfo horizon player info,
      strategy.1 info action.1 = 1 := by
  have hmass : ∑ move : Option (view.Act player),
      strategy.1 info move = 1 := by
    have := PMF.tsum_coe (strategy.1 info)
    rwa [tsum_fintype] at this
  calc
    ∑ action : view.KuhnActionAtInfo horizon player info,
      strategy.1 info action.1
      =
        ∑ move : Option (view.Act player),
          if hlegal :
              ∀ h : view.BoundedHistory horizon,
                view.reachableInfoStateOfHistory horizon player h = info →
                  move ∈ view.boundedAvailableMoves horizon h player then
            strategy.1 info move
          else 0 := by
            let p : Option (view.Act player) → Prop :=
              fun move =>
                ∀ h : view.BoundedHistory horizon,
                  view.reachableInfoStateOfHistory horizon player h = info →
                    move ∈ view.boundedAvailableMoves horizon h player
            simpa [KuhnActionAtInfo, p] using
              (sum_subtype_eq_sum_dite
                (p := p)
                (fun move _ => strategy.1 info move))
    _ = ∑ move : Option (view.Act player),
        strategy.1 info move := by
          refine Finset.sum_congr rfl ?_
          intro move _
          by_cases hlegal :
              ∀ h : view.BoundedHistory horizon,
                view.reachableInfoStateOfHistory horizon player h = info →
                  move ∈ view.boundedAvailableMoves horizon h player
          · rw [dif_pos hlegal]
          · rw [dif_neg hlegal]
            exact
              (view.behavioralStrategy_mass_zero_of_not_kuhnLegal
                horizon player strategy info hlegal).symm
    _ = 1 := hmass

open Classical in
/-- Restrict a native legal behavioral strategy to the Kuhn adapter's legal
local action subtype. -/
noncomputable def behavioralStrategyToKuhn
    (view : M.RoundView) (horizon : Nat)
    (player : Player)
    [Fintype (Option (view.Act player))]
    (strategy : view.BoundedBehavioralStrategy horizon player)
    (info : view.ReachableInfoState horizon player) :
    PMF (view.KuhnActionAtInfo horizon player info) :=
  PMF.ofFintype
    (fun action => strategy.1 info action.1)
    (view.behavioralStrategy_kuhnActionMass_eq_one
      horizon player strategy info)

/-- Lift a native legal behavioral profile into the Kuhn adapter. -/
noncomputable def behavioralProfileToKuhn
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (hMenus : view.MenusObservable horizon)
    (profile : view.BoundedBehavioralProfile horizon) :
    (view.kuhnModel horizon hMenus).BehavioralProfile :=
  fun player info =>
    view.behavioralStrategyToKuhn horizon player
      (profile player) info

open Classical in
/-- Adapter mixed pure strategy induced by one native legal behavioral
strategy. This is the one-player B→M construction used for unilateral
deviations. -/
noncomputable def behavioralStrategyToKuhnMixed
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player)
    [Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (strategy : view.BoundedBehavioralStrategy horizon player) :
    PMF ((view.kuhnModel horizon hMenus).LocalStrategy player) := by
  classical
  letI : Fintype ((view.kuhnModel horizon hMenus).InfoState player) :=
    Fintype.ofFinite _
  exact
    Math.PMFProduct.pmfPi
      (view.behavioralStrategyToKuhn horizon player strategy)

open Classical in
/-- Native mixed pure strategy induced by one legal behavioral strategy. -/
noncomputable def behavioralStrategyToMixedPure
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player)
    [Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (strategy : view.BoundedBehavioralStrategy horizon player) :
    PMF (view.BoundedPureStrategy horizon player) :=
  PMF.map
    (view.pureStrategyOfKuhn horizon hMenus player)
    (view.behavioralStrategyToKuhnMixed horizon hMenus player strategy)

@[simp]
theorem behavioralStrategyToMixedPure_toKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player)
    [Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (strategy : view.BoundedBehavioralStrategy horizon player) :
    PMF.map
        (view.pureStrategyToKuhn horizon hMenus player)
        (view.behavioralStrategyToMixedPure horizon hMenus player strategy) =
      view.behavioralStrategyToKuhnMixed horizon hMenus player strategy := by
  rw [behavioralStrategyToMixedPure, PMF.map_comp]
  change PMF.map
      ((view.pureStrategyToKuhn horizon hMenus player) ∘
        (view.pureStrategyOfKuhn horizon hMenus player))
      (view.behavioralStrategyToKuhnMixed horizon hMenus player strategy) =
    view.behavioralStrategyToKuhnMixed horizon hMenus player strategy
  have hfun :
      ((view.pureStrategyToKuhn horizon hMenus player) ∘
        (view.pureStrategyOfKuhn horizon hMenus player)) = id := by
    funext localStrategy info
    change
      (view.pureStrategyToKuhn horizon hMenus player
        (view.pureStrategyOfKuhn horizon hMenus player localStrategy)) info =
        localStrategy info
    rw [view.pureStrategyToKuhn_pureStrategyOfKuhn
      horizon hMenus player localStrategy]
  rw [hfun, PMF.map_id]

theorem behavioralStrategyToKuhn_map_val
    (view : M.RoundView) (horizon : Nat)
    (player : Player)
    [Fintype (Option (view.Act player))]
    (strategy : view.BoundedBehavioralStrategy horizon player)
    (info : view.ReachableInfoState horizon player) :
    PMF.map Subtype.val
        (view.behavioralStrategyToKuhn horizon player strategy info) =
      strategy.1 info := by
  classical
  apply PMF.ext
  intro move
  rw [PMF.map_apply, tsum_fintype]
  let legal : Option (view.Act player) → Prop :=
    fun move =>
      ∀ h : view.BoundedHistory horizon,
        view.reachableInfoStateOfHistory horizon player h = info →
          move ∈ view.boundedAvailableMoves horizon h player
  calc
    _ =
      ∑ action : view.KuhnActionAtInfo horizon player info,
        if move = action.1 then strategy.1 info action.1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro action _
          by_cases hmove : move = action.1
          · rw [if_pos hmove, if_pos hmove]
            rfl
          · rw [if_neg hmove, if_neg hmove]
    _ =
      ∑ candidate : Option (view.Act player),
        if h : legal candidate then
          if move = candidate then strategy.1 info candidate else 0
        else 0 := by
          simpa [behavioralStrategyToKuhn, KuhnActionAtInfo, legal] using
            (sum_subtype_eq_sum_dite
              (p := legal)
              (fun candidate h =>
                if move = candidate then strategy.1 info candidate else 0))
    _ = strategy.1 info move := by
      by_cases hlegal : legal move
      · calc
          ∑ candidate : Option (view.Act player),
              (if h : legal candidate then
                if move = candidate then strategy.1 info candidate else 0
              else 0)
              =
            ∑ candidate : Option (view.Act player),
              if move = candidate then strategy.1 info candidate else 0 := by
                refine Finset.sum_congr rfl ?_
                intro candidate _
                by_cases hmove : move = candidate
                · subst candidate
                  simp [hlegal]
                · by_cases hcandidate : legal candidate <;>
                    simp [hcandidate, hmove]
          _ = strategy.1 info move := by
            rw [Finset.sum_ite_eq]
            simp
      · have hzero :=
          view.behavioralStrategy_mass_zero_of_not_kuhnLegal
            horizon player strategy info hlegal
        calc
          ∑ candidate : Option (view.Act player),
              (if h : legal candidate then
                if move = candidate then strategy.1 info candidate else 0
              else 0)
              =
            ∑ candidate : Option (view.Act player),
              if move = candidate then strategy.1 info candidate else 0 := by
                refine Finset.sum_congr rfl ?_
                intro candidate _
                by_cases hmove : move = candidate
                · subst candidate
                  simp [hlegal, hzero]
                · by_cases hcandidate : legal candidate <;>
                    simp [hcandidate, hmove]
          _ = strategy.1 info move := by
            rw [Finset.sum_ite_eq]
            simp

@[simp]
theorem behavioralProfileOfKuhn_behavioralProfileToKuhn
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (hMenus : view.MenusObservable horizon)
    (profile : view.BoundedBehavioralProfile horizon) :
    view.behavioralProfileOfKuhn horizon hMenus
        (view.behavioralProfileToKuhn horizon hMenus profile) =
      profile := by
  funext player
  apply Subtype.ext
  funext info
  exact
    view.behavioralStrategyToKuhn_map_val horizon player
      (profile player) info

open Classical in
private theorem kuhnModel_current_coord_ignores_of_reachable
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    {steps : Nat}
    {profile : (view.kuhnModel horizon hMenus).PureProfile}
    {trace : List (view.BoundedHistory horizon)}
    (hreach :
      Math.ParameterizedChain.pureRun
        ((view.kuhnModel horizon hMenus).pureStep)
        (view.kuhnModel horizon hMenus).init steps profile trace ≠ 0)
    (player : Player) :
    Math.PMFProduct.Ignores
      (A := fun info =>
        view.KuhnActionAtInfo horizon player info)
      ((view.kuhnModel horizon hMenus).projectStates player trace)
      (fun strategy :
          (view.kuhnModel horizon hMenus).LocalStrategy player =>
        Math.ParameterizedChain.pureRun
          ((view.kuhnModel horizon hMenus).pureStep)
          (view.kuhnModel horizon hMenus).init steps
          (Function.update profile player strategy) trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  intro strategy action
  let info := O.projectStates player trace
  let strategy' : O.LocalStrategy player :=
    Function.update strategy info action
  let profile₁ : O.PureProfile :=
    Function.update profile player strategy'
  let profile₂ : O.PureProfile :=
    Function.update profile player strategy
  have hlen : trace.length = steps + 1 :=
    Math.ParameterizedChain.pureRun_length O.pureStep O.init
      steps profile trace hreach
  have hagree :
      ∀ (index : Nat), index < steps → ∀ other : Player,
        profile₁ other (O.projectStates other (trace.take (index + 1))) =
          profile₂ other
            (O.projectStates other (trace.take (index + 1))) := by
    intro index hindex other
    by_cases hother : other = player
    · subst other
      dsimp [profile₁, profile₂]
      rw [Function.update_self, Function.update_self]
      by_cases hsame :
          O.projectStates player (trace.take (index + 1)) = info
      · have htakeAll : trace.take (steps + 1) = trace := by
          rw [List.take_eq_self_iff]
          exact le_of_eq hlen
        have hrepeat :
            O.projectStates player (trace.take (index + 1)) =
              O.projectStates player (trace.take (steps + 1)) := by
          rw [htakeAll]
          exact hsame
        have hsub :
            Subsingleton
              (view.KuhnActionAtInfo horizon player
                (O.projectStates player (trace.take (steps + 1)))) := by
          have hnr :=
            view.kuhnModel_noNontrivialInfoStateRepeat
              horizon hMenus
          have hrun :
              O.runDistPure steps profile trace ≠ 0 := by
            simpa [O.runDistPure_eq_pureRun] using hreach
          simpa [O, ObsModelCore.currentObs] using
            hnr player profile steps trace hrun index steps
              hindex (by omega) hrepeat
        have hsubEarlier :
            Subsingleton
              (view.KuhnActionAtInfo horizon player
                (O.projectStates player (trace.take (index + 1)))) := by
          simpa [hsame, htakeAll] using hsub
        exact @Subsingleton.elim _ hsubEarlier _ _
      · exact Function.update_of_ne hsame action strategy
    · dsimp [profile₁, profile₂]
      rw [Function.update_of_ne hother, Function.update_of_ne hother]
  have hrun :=
    ObsModelCore.runDistPure_congr_on_trace
      (O := O) (π₁ := profile₁) (π₂ := profile₂)
      (n := steps) (ss := trace) hlen hagree
  simpa [profile₁, profile₂, strategy', info,
    ObsModelCore.runDistPure_eq_pureRun] using hrun

open Classical in
theorem behavioralStrategyToKuhnMixed_factorAt_of_ignores
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player)
    [Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (strategy : view.BoundedBehavioralStrategy horizon player)
    (steps : Nat) (trace : List (view.BoundedHistory horizon))
    (profile : (view.kuhnModel horizon hMenus).PureProfile)
    (hign :
      Math.PMFProduct.Ignores
        (A := fun info =>
          view.KuhnActionAtInfo horizon player info)
        ((view.kuhnModel horizon hMenus).projectStates player trace)
        (fun localStrategy :
            (view.kuhnModel horizon hMenus).LocalStrategy player =>
          Math.ParameterizedChain.pureRun
            ((view.kuhnModel horizon hMenus).pureStep)
            (view.kuhnModel horizon hMenus).init steps
            (Function.update profile player localStrategy) trace)) :
    Math.ProbabilityMassFunction.pushforward
        (Math.ParameterizedChain.reweightPMF
          (view.behavioralStrategyToKuhnMixed
            horizon hMenus player strategy)
          (fun localStrategy :
              (view.kuhnModel horizon hMenus).LocalStrategy player =>
            Math.ParameterizedChain.pureRun
              ((view.kuhnModel horizon hMenus).pureStep)
              (view.kuhnModel horizon hMenus).init steps
              (Function.update profile player localStrategy) trace))
        (fun localStrategy =>
          localStrategy
            ((view.kuhnModel horizon hMenus).projectStates player trace)) =
      view.behavioralStrategyToKuhn horizon player strategy
        ((view.kuhnModel horizon hMenus).projectStates player trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI : Fintype (O.InfoState player) := Fintype.ofFinite _
  letI : Fintype (view.ReachableInfoState horizon player) := by
    simpa [O, kuhnModel, ObsModelCore.InfoState] using
      (inferInstance : Fintype (O.InfoState player))
  have hCtop :
      (∑ localStrategy : O.LocalStrategy player,
        view.behavioralStrategyToKuhnMixed
            horizon hMenus player strategy localStrategy *
          Math.ParameterizedChain.pureRun O.pureStep O.init steps
            (Function.update profile player localStrategy) trace) ≠ ⊤ := by
    exact ObsModelCore.sum_mul_pmf_ne_top
      (view.behavioralStrategyToKuhnMixed
        horizon hMenus player strategy)
      (fun localStrategy : O.LocalStrategy player =>
        Math.ParameterizedChain.pureRun O.pureStep O.init steps
          (Function.update profile player localStrategy) trace)
      (fun _ => PMF.coe_le_one _ trace)
  simpa [behavioralStrategyToKuhnMixed, O] using
    Math.ParameterizedChain.reweightPMF_pmfPi_push_coord_of_ignores'
      (A := fun info =>
        view.KuhnActionAtInfo horizon player info)
      (σ := view.behavioralStrategyToKuhn horizon player strategy)
      (j := (O.projectStates player trace))
      (w := fun localStrategy : O.LocalStrategy player =>
        Math.ParameterizedChain.pureRun O.pureStep O.init steps
          (Function.update profile player localStrategy) trace)
      hign hCtop

open Classical in
theorem behavioralStrategyToKuhnMixed_factorAt
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player)
    [Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (strategy : view.BoundedBehavioralStrategy horizon player)
    (steps : Nat) (trace : List (view.BoundedHistory horizon))
    (profile : (view.kuhnModel horizon hMenus).PureProfile)
    (hreach :
      Math.ParameterizedChain.pureRun
        ((view.kuhnModel horizon hMenus).pureStep)
        (view.kuhnModel horizon hMenus).init steps profile trace ≠ 0) :
    Math.ProbabilityMassFunction.pushforward
        (Math.ParameterizedChain.reweightPMF
          (view.behavioralStrategyToKuhnMixed
            horizon hMenus player strategy)
          (fun localStrategy :
              (view.kuhnModel horizon hMenus).LocalStrategy player =>
            Math.ParameterizedChain.pureRun
              ((view.kuhnModel horizon hMenus).pureStep)
              (view.kuhnModel horizon hMenus).init steps
              (Function.update profile player localStrategy) trace))
        (fun localStrategy =>
          localStrategy
            ((view.kuhnModel horizon hMenus).projectStates player trace)) =
      view.behavioralStrategyToKuhn horizon player strategy
        ((view.kuhnModel horizon hMenus).projectStates player trace) :=
  view.behavioralStrategyToKuhnMixed_factorAt_of_ignores
    horizon hMenus player strategy steps trace profile
    (view.kuhnModel_current_coord_ignores_of_reachable
      horizon hMenus hreach player)

@[simp]
theorem behavioralProfileOfKuhn_pureToBehavioral
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (profile : (view.kuhnModel horizon hMenus).PureProfile) :
    view.behavioralProfileOfKuhn horizon hMenus
        ((view.kuhnModel horizon hMenus).pureToBehavioral profile) =
      view.legalPureToBehavioral horizon
        (view.pureProfileOfKuhn horizon hMenus profile) := by
  funext player
  apply Subtype.ext
  funext info
  change PMF.map Subtype.val (PMF.pure (profile player info)) =
    PMF.pure (profile player info).1
  rw [PMF.pure_map]

theorem kuhnJointActionDist_bind_eq_native
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player]
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (behavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile)
    (trace : List (view.BoundedHistory horizon))
    {β : Type} (K : JointAction view.Act → PMF β) :
    ((view.kuhnModel horizon hMenus).jointActionDist behavioral trace).bind
        (fun action => K (fun player => (action player).1)) =
      (view.jointActionDist horizon
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)
        ((view.kuhnModel horizon hMenus).lastState trace)).bind K := by
  classical
  let O := view.kuhnModel horizon hMenus
  have hnative :
      view.jointActionDist horizon
          (view.behavioralProfileOfKuhn horizon hMenus behavioral)
          (O.lastState trace) =
        Math.PMFProduct.pmfPi
          (fun player =>
            PMF.map Subtype.val
              (behavioral player (O.projectStates player trace))) := by
    change
      Math.PMFProduct.pmfPi
          (fun player =>
            PMF.map Subtype.val
              (behavioral player
                (view.reachableInfoStateOfHistory horizon player
                  (O.lastState trace)))) =
        Math.PMFProduct.pmfPi
          (fun player =>
            PMF.map Subtype.val
              (behavioral player (O.projectStates player trace)))
    congr
    funext player
    rw [kuhnModel_projectStates]
  rw [hnative]
  change
    (Math.PMFProduct.pmfPi
        (fun player => behavioral player (O.projectStates player trace))).bind
        (fun action => K (fun player => (action player).1)) =
      (Math.PMFProduct.pmfPi
        (fun player =>
          PMF.map Subtype.val
            (behavioral player (O.projectStates player trace)))).bind K
  rw [Math.PMFProduct.pmfPi_map_bind]
  rfl

theorem kuhnStepDist_eq_runDistFrom_one
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (behavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile)
    (trace : List (view.BoundedHistory horizon)) :
    (view.kuhnModel horizon hMenus).stepDist behavioral trace =
      BoundedHistory.runDistFrom view horizon
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)
        1 ((view.kuhnModel horizon hMenus).lastState trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let h := O.lastState trace
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · change
      (O.jointActionDist behavioral trace).bind
          (fun action =>
            view.kuhnStep horizon h (O.castJointAction trace action)) =
        BoundedHistory.runDistFrom view horizon
          (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1 h
    rw [BoundedHistory.runDistFrom_succ_terminal view horizon
      (view.behavioralProfileOfKuhn horizon hMenus behavioral) 0 h hterm]
    apply PMF.ext
    intro dst
    rw [PMF.bind_apply]
    by_cases hdst : dst = h
    · simp [kuhnStep_terminal, hterm, hdst]
      have hmass := PMF.tsum_coe (O.jointActionDist behavioral trace)
      rwa [tsum_fintype] at hmass
    · simp [kuhnStep_terminal, hterm, hdst]
  · change
      (O.jointActionDist behavioral trace).bind
          (fun action =>
            view.kuhnStep horizon h (O.castJointAction trace action)) =
        BoundedHistory.runDistFrom view horizon
          (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1 h
    rw [BoundedHistory.runDistFrom_succ_nonterminal view horizon
      (view.behavioralProfileOfKuhn horizon hMenus behavioral) 0 h hterm]
    rw [view.legalActionLaw_bind_eq_jointActionDist_bind horizon
      (view.behavioralProfileOfKuhn horizon hMenus behavioral) h hterm h
      (fun action =>
        (view.boundedTransition horizon h.lastState action).bind fun dst =>
          BoundedHistory.runDistFrom view horizon
            (view.behavioralProfileOfKuhn horizon hMenus behavioral) 0
            (h.extendByOutcome action dst))]
    rw [← view.kuhnJointActionDist_bind_eq_native horizon hMenus behavioral
      trace]
    apply congrArg
      (fun f =>
        (O.jointActionDist behavioral trace).bind f)
    funext action
    let joint : JointAction view.Act := fun player => (action player).1
    have hlegal :
        JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) h.lastState joint := by
      have hlegalCast :=
        view.kuhnJointAction_legal horizon h hterm
          (O.castJointAction trace action)
      rw [view.kuhnJointAction_castJointAction horizon hMenus trace action]
        at hlegalCast
      exact hlegalCast
    have hlegalAction :
        view.kuhnLegalAction horizon h hterm
            (O.castJointAction trace action) =
          (⟨joint, hlegal⟩ :
            view.BoundedLegalAction horizon h.lastState) := by
      apply Subtype.ext
      simpa [joint] using
        view.kuhnJointAction_castJointAction horizon hMenus trace action
    rw [dif_pos hlegal]
    rw [view.kuhnStep_nonterminal horizon h (O.castJointAction trace action)
      hterm, hlegalAction]
    rfl

/-- Default behavioral profile used only on Kuhn-adapter information states
that are unreachable under every pure profile. Reachable behavior in the
mixed-to-behavioral construction is determined by the mixed profile itself. -/
noncomputable def defaultKuhnBehavioralProfile
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    (view.kuhnModel horizon hMenus).BehavioralProfile :=
  fun player info =>
    PMF.pure (view.defaultKuhnActionAtInfo horizon hMenus player info)

/-- Push a native product-mixed pure profile into the Kuhn adapter's pure
strategy carrier. -/
noncomputable def mixedPureProfileToKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    ∀ player, PMF ((view.kuhnModel horizon hMenus).LocalStrategy player) :=
  fun player =>
    PMF.map
      (view.pureStrategyToKuhn horizon hMenus player)
      (mixed player)

/-- Canonical mixed-to-behavioral realization used by the native Kuhn bridge.

This is the explicit `ObsModelCore.mixedToBehavioralProfileWithFallback`
witness. The fallback is irrelevant on reachable adapter information states
but makes the profile total. -/
noncomputable def mixedPureToKuhnBehavioralProfile
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    (view.kuhnModel horizon hMenus).BehavioralProfile := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  letI :
      ∀ player info,
        Nonempty (view.KuhnActionAtInfo horizon player info) :=
    view.instNonemptyKuhnActionAtInfo horizon hMenus
  exact
    ObsModelCore.mixedToBehavioralProfileWithFallback
      (O := O)
      (view.mixedPureProfileToKuhn horizon hMenus mixed)
      (view.defaultKuhnBehavioralProfile horizon hMenus)

/-- Canonical mixed-to-behavioral realization used by the native Kuhn bridge,
erased from the proof adapter back to the native bounded behavioral-strategy
carrier. -/
noncomputable def mixedPureToBehavioralProfile
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    view.BoundedBehavioralProfile horizon :=
  view.behavioralProfileOfKuhn horizon hMenus
    (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed)

/-- Updating one player's mixed-pure marginal leaves every other player's
Kuhn-adapter behavioral realization unchanged. -/
theorem mixedPureToKuhnBehavioralProfile_update_ne
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player))
    {who player : Player} (hne : player ≠ who)
    (τ : PMF (view.BoundedPureStrategy horizon who)) :
    view.mixedPureToKuhnBehavioralProfile horizon hMenus
        (Function.update mixed who τ) player =
      view.mixedPureToKuhnBehavioralProfile horizon hMenus
        mixed player := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  funext info
  let μ := view.mixedPureProfileToKuhn horizon hMenus mixed
  let τK : PMF (O.LocalStrategy who) :=
    PMF.map (view.pureStrategyToKuhn horizon hMenus who) τ
  have hμ :
      view.mixedPureProfileToKuhn horizon hMenus
          (Function.update mixed who τ) =
        Function.update μ who τK := by
    funext other
    by_cases hother : other = who
    · subst other
      simp [mixedPureProfileToKuhn, μ, τK]
    · simp [mixedPureProfileToKuhn, μ, τK, Function.update_of_ne hother]
  calc
    view.mixedPureToKuhnBehavioralProfile horizon hMenus
        (Function.update mixed who τ) player info
        =
      ObsModelCore.mixedToBehavioralProfileWithFallback (O := O)
        (Function.update μ who τK)
        (view.defaultKuhnBehavioralProfile horizon hMenus) player info := by
          simp [mixedPureToKuhnBehavioralProfile, hμ, μ, τK, O]
    _ =
      ObsModelCore.mixedToBehavioralProfileWithFallback (O := O)
        μ (view.defaultKuhnBehavioralProfile horizon hMenus) player info :=
          ObsModelCore.mixedToBehavioralProfileWithFallback_update_ne
            (O := O) μ (view.defaultKuhnBehavioralProfile horizon hMenus)
            hne τK info
    _ =
      view.mixedPureToKuhnBehavioralProfile horizon hMenus
        mixed player info := by
          simp [mixedPureToKuhnBehavioralProfile, μ, O]

/-- Updating one player's mixed-pure marginal leaves every other player's
native behavioral realization unchanged. -/
theorem mixedPureToBehavioralProfile_update_ne
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player))
    {who player : Player} (hne : player ≠ who)
    (τ : PMF (view.BoundedPureStrategy horizon who)) :
    view.mixedPureToBehavioralProfile horizon hMenus
        (Function.update mixed who τ) player =
      view.mixedPureToBehavioralProfile horizon hMenus
        mixed player := by
  apply Subtype.ext
  funext info
  have hprofile :=
    view.mixedPureToKuhnBehavioralProfile_update_ne
      horizon hMenus mixed hne τ
  exact congrArg (fun strategy => PMF.map Subtype.val (strategy info))
    hprofile

/-- The canonical mixed-to-behavioral witness has the adapter trace law
specified by Kuhn's theorem. -/
theorem mixedPureToBehavioralProfile_runDist
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    let O := view.kuhnModel horizon hMenus
    O.runDist steps
        (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed) =
      (Math.PMFProduct.pmfPi
        (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
        (O.runDistPure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  have hDet :
      ObsModelCore.StepActionDeterminism O :=
    view.kuhnModel_stepActionDeterminism horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  letI :
      ∀ player info,
        Nonempty (view.KuhnActionAtInfo horizon player info) :=
    view.instNonemptyKuhnActionAtInfo horizon hMenus
  have hLocalO :
      ∀ player, ObsModelCore.ObsLocalFeasibilityFull O player := by
    simpa [KuhnLocality, O] using
      view.kuhnLocality horizon hMenus
  have hAPL :
      ∀ player, ObsModelCore.ActionPosteriorLocal O player :=
    fun player =>
      ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
        hDet.toMassInvariant player
        (by
          intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _hsub πᵢ
          exact hLocalO player n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ πᵢ)
  simpa [O, mixedPureProfileToKuhn, mixedPureToKuhnBehavioralProfile] using
    (ObsModelCore.mixedToBehavioralProfileWithFallback_runDist
      (O := O)
      hDet.toMassInvariant
      hDet.toSupportFactorization
      hAPL
      (view.mixedPureProfileToKuhn horizon hMenus mixed)
      (view.defaultKuhnBehavioralProfile horizon hMenus)
      steps)

open Classical in
/-- Unilateral-deviation law for the canonical mixed-to-behavioral Kuhn
realizer at the adapter trace level.

Replacing one player's mixed pure component by the product mixed strategy
induced from a behavioral deviation has the same trace law as keeping the
canonical behavioral realization for the opponents and plugging in that
behavioral deviation for the deviating player. -/
theorem mixedPureToKuhnBehavioralProfile_unilateral_deviation_runDist
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player))
    (who : Player)
    (deviation : view.BoundedBehavioralStrategy horizon who) :
    let mixedDeviation :=
      view.behavioralStrategyToMixedPure horizon hMenus who deviation
    let mixed' := Function.update mixed who mixedDeviation
    let behavioralTarget :
        (view.kuhnModel horizon hMenus).BehavioralProfile :=
      Function.update
        (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed)
        who
        (view.behavioralStrategyToKuhn horizon who deviation)
    (view.kuhnModel horizon hMenus).runDist steps
        (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed') =
      (view.kuhnModel horizon hMenus).runDist steps behavioralTarget := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI : ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  let mixedDeviation :=
    view.behavioralStrategyToMixedPure horizon hMenus who deviation
  let mixed' := Function.update mixed who mixedDeviation
  let μ := view.mixedPureProfileToKuhn horizon hMenus mixed
  let μ' := view.mixedPureProfileToKuhn horizon hMenus mixed'
  let fallback := view.defaultKuhnBehavioralProfile horizon hMenus
  let βsrc := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed'
  let βorig := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  let βtgt : O.BehavioralProfile :=
    Function.update βorig who
      (view.behavioralStrategyToKuhn horizon who deviation)
  have hDet : ObsModelCore.StepActionDeterminism O :=
    view.kuhnModel_stepActionDeterminism horizon hMenus
  have hLocalO :
      ∀ player, ObsModelCore.ObsLocalFeasibilityFull O player := by
    simpa [KuhnLocality, O] using
      view.kuhnLocality horizon hMenus
  have hAPL :
      ∀ player, ObsModelCore.ActionPosteriorLocal O player :=
    fun player =>
      ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
        hDet.toMassInvariant player
        (by
          intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _hsub πᵢ
          exact hLocalO player n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ πᵢ)
  have hμWho :
      μ' who =
        view.behavioralStrategyToKuhnMixed horizon hMenus who deviation := by
    simp [μ', mixedPureProfileToKuhn, mixed', mixedDeviation]
  have hμOther :
      ∀ player, player ≠ who → μ' player = μ player := by
    intro player hne
    simp [μ', μ, mixedPureProfileToKuhn, mixed', Function.update_of_ne hne]
  have hrunSrc :
      ∀ m,
        O.runDist m βsrc =
          (Math.PMFProduct.pmfPi μ').bind (O.runDistPure m) := by
    intro m
    simpa [O, βsrc, μ'] using
      view.mixedPureToBehavioralProfile_runDist
        horizon m hMenus mixed'
  apply ObsModelCore.runDist_congr
    (O := O) (β₁ := βsrc) (β₂ := βtgt)
  intro m player trace htrace
  have hmix :
      ((Math.PMFProduct.pmfPi μ').bind (O.runDistPure m)) trace ≠ 0 := by
    rw [← hrunSrc m]
    exact htrace
  have hmixSum :
      ∑ pure : O.PureProfile,
        Math.PMFProduct.pmfPi μ' pure * O.runDistPure m pure trace ≠ 0 := by
    simpa only [PMF.bind_apply, tsum_fintype] using hmix
  obtain ⟨witness, _hwitnessMem, hwitnessProd⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hmixSum
  have hwitnessRun :
      O.runDistPure m witness trace ≠ 0 :=
    right_ne_zero_of_mul hwitnessProd
  have hwitnessPureRun :
      Math.ParameterizedChain.pureRun O.pureStep O.init m
          witness trace ≠ 0 := by
    simpa [O.runDistPure_eq_pureRun] using hwitnessRun
  have hsrcFactor :
      βsrc player (O.projectStates player trace) =
        ObsModelCore.mixedToBehavioralFactorAt
          (O := O) μ' player m trace witness := by
    have h :=
      ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
        (O := O) hAPL μ' fallback player m trace witness
        hwitnessPureRun
    simpa [βsrc, mixedPureToKuhnBehavioralProfile, μ',
      fallback, O] using h
  by_cases hplayer : player = who
  · subst player
    have hwhoFactor :
        ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ' who m trace witness =
          view.behavioralStrategyToKuhn horizon who deviation
            (O.projectStates who trace) := by
      simpa [ObsModelCore.mixedToBehavioralFactorAt, hμWho, O] using
        view.behavioralStrategyToKuhnMixed_factorAt
          horizon hMenus who deviation m trace witness
          hwitnessPureRun
    have htgt :
        βtgt who (O.projectStates who trace) =
          view.behavioralStrategyToKuhn horizon who deviation
            (O.projectStates who trace) := by
      simp [βtgt]
    exact hsrcFactor.trans (hwhoFactor.trans htgt.symm)
  · have horigFactor :
        βorig player (O.projectStates player trace) =
          ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ player m trace witness := by
      have h :=
        ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
          (O := O) hAPL μ fallback player m trace witness
          hwitnessPureRun
      simpa [βorig, mixedPureToKuhnBehavioralProfile, μ,
        fallback, O] using h
    have hfactorEq :
        ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ' player m trace witness =
          ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ player m trace witness := by
      simp [ObsModelCore.mixedToBehavioralFactorAt, hμOther player hplayer]
    calc
      βsrc player (O.projectStates player trace)
          =
        ObsModelCore.mixedToBehavioralFactorAt
          (O := O) μ' player m trace witness := hsrcFactor
      _ =
        ObsModelCore.mixedToBehavioralFactorAt
          (O := O) μ player m trace witness := hfactorEq
      _ =
        βorig player (O.projectStates player trace) := horigFactor.symm
      _ =
        βtgt player (O.projectStates player trace) := by
          simp [βtgt, hplayer]

/-- Core mixed-to-behavioral Kuhn realization for a native round view, stated
at the proof-adapter trace level.

The public game-facing theorem should compose this result with a run/outcome
adequacy theorem for the concrete `RoundView`.  The hypotheses are exactly the
generic Kuhn semantic hypotheses on the adapter model; the adapter itself does
not add another public game IR. -/
theorem kuhn_mixed_to_behavioral_core
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    ∃ behavioral : view.BoundedBehavioralProfile horizon,
      ∃ adapterBehavioral :
        (view.kuhnModel horizon hMenus).BehavioralProfile,
        behavioral = view.behavioralProfileOfKuhn horizon hMenus
          adapterBehavioral ∧
        (view.kuhnModel horizon hMenus).runDist steps
          adapterBehavioral =
          (Math.PMFProduct.pmfPi
            (fun player =>
              PMF.map
                (view.pureStrategyToKuhn horizon hMenus player)
                (mixed player))).bind
            ((view.kuhnModel horizon hMenus).runDistPure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  let adapterBehavioral :=
    view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  exact
    ⟨view.mixedPureToBehavioralProfile horizon hMenus mixed,
      adapterBehavioral, by
        simp [mixedPureToBehavioralProfile, adapterBehavioral],
      by
        simpa [mixedPureProfileToKuhn, O, adapterBehavioral] using
          view.mixedPureToBehavioralProfile_runDist
            horizon steps hMenus mixed⟩

/-- Core behavioral-to-correlated-pure Kuhn theorem for the native round-view
adapter. This is useful when analyzing behavioral strategies directly at the
adapter trace level. The produced distribution is over pure profiles jointly,
not a product mixed strategy profile. -/
theorem kuhn_behavioral_to_correlated_pure_core
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (behavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile) :
    (view.kuhnModel horizon hMenus).runDist steps behavioral =
      ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
        behavioral).bind
        ((view.kuhnModel horizon hMenus).runDistPure steps) :=
  ObsModelCore.kuhn_behavioral_to_mixed
    (view.kuhnModel_noNontrivialInfoStateRepeat horizon hMenus)
    behavioral steps

/-- Run adequacy needed to move Kuhn results from the proof adapter back to
native bounded histories.  The adapter is proof-facing; this predicate is the
claim that its final-history marginal is exactly the native `RoundView` run for
the corresponding legal behavioral or pure strategy. -/
def KuhnRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) : Prop :=
  let O := view.kuhnModel horizon hMenus
  (∀ behavioral : O.BehavioralProfile,
    PMF.map O.lastState (O.runDist steps behavioral) =
      view.runDist horizon steps
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)) ∧
  (∀ pure : view.BoundedPureProfile horizon,
    PMF.map O.lastState
        (O.runDistPure steps
        (view.pureProfileToKuhn horizon hMenus pure)) =
      view.runDist horizon steps
        (view.legalPureToBehavioral horizon pure))

/-- The single semantic bridge behind `KuhnRunAdequacy`: projecting the
adapter trace run to its final native history agrees with the native
history-run semantics for every adapter behavioral profile. -/
def KuhnBehavioralRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) : Prop :=
  let O := view.kuhnModel horizon hMenus
  ∀ behavioral : O.BehavioralProfile,
    PMF.map O.lastState (O.runDist steps behavioral) =
      view.runDist horizon steps
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)

theorem kuhnBehavioralRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) :
    view.KuhnBehavioralRunAdequacy horizon hMenus steps := by
  classical
  intro behavioral
  let O := view.kuhnModel horizon hMenus
  induction steps with
  | zero =>
      change PMF.map O.lastState (PMF.pure [O.init]) =
        PMF.pure (BoundedHistory.nil view horizon)
      rw [PMF.pure_map]
      change PMF.pure O.init = PMF.pure (BoundedHistory.nil view horizon)
      simp [O, kuhnModel]
  | succ steps ih =>
      change
        PMF.map O.lastState
            (Math.TraceRun.traceRun (O.stepDist behavioral) O.init
              (steps + 1)) =
          Machine.RoundView.runDist view horizon (steps + 1)
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
      rw [Math.TraceRun.traceRun_succ]
      rw [PMF.map_bind]
      conv_lhs =>
        arg 2
        ext trace
        rw [PMF.map_bind]
        arg 2
        ext next
        rw [PMF.pure_map]
        rw [ObsModelCore.lastState_append_singleton]
      conv_lhs =>
        arg 2
        ext trace
        rw [view.kuhnStepDist_eq_runDistFrom_one horizon hMenus behavioral
          trace]
        rw [PMF.bind_pure]
      change
        (Math.TraceRun.traceRun (O.stepDist behavioral) O.init steps).bind
            ((fun history =>
              BoundedHistory.runDistFrom view horizon
                (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1
                history) ∘ O.lastState) =
          Machine.RoundView.runDist view horizon (steps + 1)
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
      rw [← PMF.bind_map]
      change
        (PMF.map O.lastState (O.runDist steps behavioral)).bind
            (fun history =>
              BoundedHistory.runDistFrom view horizon
                (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1
                history) =
          Machine.RoundView.runDist view horizon (steps + 1)
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
      rw [ih]
      change
        (BoundedHistory.runDistFrom view horizon
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
            steps (BoundedHistory.nil view horizon)).bind
            (fun history =>
              BoundedHistory.runDistFrom view horizon
                (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1
                history) =
          BoundedHistory.runDistFrom view horizon
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
            (steps + 1) (BoundedHistory.nil view horizon)
      rw [← BoundedHistory.runDistFrom_bind_runDistFrom
        view horizon
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)
        steps 1 (BoundedHistory.nil view horizon)]

/-- Pure-profile run adequacy for arbitrary adapter pure profiles.  This is
the behavioral-to-correlated-pure counterpart of the native-pure clause in
`KuhnRunAdequacy`: an adapter pure profile may be produced by the generic Kuhn
behavioral-to-correlated-pure theorem, so it must be compared with its native
erased pure profile. -/
def KuhnAdapterPureRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) : Prop :=
  let O := view.kuhnModel horizon hMenus
  ∀ pure : O.PureProfile,
    PMF.map O.lastState (O.runDistPure steps pure) =
      view.runDist horizon steps
        (view.legalPureToBehavioral horizon
          (view.pureProfileOfKuhn horizon hMenus pure))

theorem KuhnRunAdequacy.of_behavioral
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat)
    (hAdequacy :
      view.KuhnBehavioralRunAdequacy horizon hMenus steps) :
    view.KuhnRunAdequacy horizon hMenus steps := by
  constructor
  · exact hAdequacy
  · intro pure
    let O := view.kuhnModel horizon hMenus
    have hrun := hAdequacy (O.pureToBehavioral
      (view.pureProfileToKuhn horizon hMenus pure))
    simpa [KuhnBehavioralRunAdequacy, O, ObsModelCore.runDistPure] using hrun

theorem kuhnRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) :
    view.KuhnRunAdequacy horizon hMenus steps :=
  KuhnRunAdequacy.of_behavioral view horizon hMenus steps
    (view.kuhnBehavioralRunAdequacy horizon hMenus steps)

theorem KuhnAdapterPureRunAdequacy.of_behavioral
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat)
    (hAdequacy :
      view.KuhnBehavioralRunAdequacy horizon hMenus steps) :
    view.KuhnAdapterPureRunAdequacy horizon hMenus steps := by
  intro pure
  let O := view.kuhnModel horizon hMenus
  have hrun := hAdequacy (O.pureToBehavioral pure)
  simpa [KuhnBehavioralRunAdequacy, O, ObsModelCore.runDistPure] using hrun

theorem kuhnAdapterPureRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) :
    view.KuhnAdapterPureRunAdequacy horizon hMenus steps :=
  KuhnAdapterPureRunAdequacy.of_behavioral view horizon hMenus steps
    (view.kuhnBehavioralRunAdequacy horizon hMenus steps)

theorem pureProfileToKuhn_pmfPi
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    Math.PMFProduct.pmfPi
        (fun player =>
          PMF.map
            (view.pureStrategyToKuhn horizon hMenus player)
            (mixed player)) =
      PMF.map
        (view.pureProfileToKuhn horizon hMenus)
        (Math.PMFProduct.pmfPi mixed) := by
  simpa [pureProfileToKuhn] using
    (Math.PMFProduct.pmfPi_push_coordwise
      (A := fun player => view.BoundedPureStrategy horizon player)
      (B := fun player =>
        (view.kuhnModel horizon hMenus).LocalStrategy player)
      mixed
      (fun player =>
        view.pureStrategyToKuhn horizon hMenus player)).symm

theorem boundedOutcomeFromBehavioral_eq_map_history
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    view.boundedOutcomeFromBehavioral horizon behavioral steps =
      PMF.map (fun history : view.BoundedHistory horizon =>
        M.outcome history.lastState.state)
        (view.runDist horizon steps behavioral) := by
  rw [boundedOutcomeFromBehavioral, boundedEventBatchTraceFromBehavioral]
  rw [PMF.map_comp]
  rfl

theorem boundedOutcomeFromPure_eq_map_history
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (pure : view.BoundedPureProfile horizon) :
    view.boundedOutcomeFromPure horizon pure steps =
      PMF.map (fun history : view.BoundedHistory horizon =>
        M.outcome history.lastState.state)
        (view.runDist horizon steps
          (view.legalPureToBehavioral horizon pure)) := by
  rw [boundedOutcomeFromPure, boundedEventBatchTraceFromPure,
    boundedEventBatchTraceFromBehavioral]
  rw [PMF.map_comp]
  rfl

/-- Native option-outcome law for the canonical mixed-to-behavioral Kuhn
realizer. -/
theorem mixedPureToBehavioralProfile_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    view.boundedOutcomeFromBehavioral horizon
        (view.mixedPureToBehavioralProfile horizon hMenus mixed) steps =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let historyOutcome : view.BoundedHistory horizon → Option M.Outcome :=
    fun history => M.outcome history.lastState.state
  let traceOutcome : List (view.BoundedHistory horizon) → Option M.Outcome :=
    fun trace => historyOutcome (O.lastState trace)
  let adapterBehavioral :=
    view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  have hrun :
      O.runDist steps adapterBehavioral =
        (Math.PMFProduct.pmfPi
          (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
          (O.runDistPure steps) := by
    simpa [O, adapterBehavioral] using
      view.mixedPureToBehavioralProfile_runDist
        horizon steps hMenus mixed
  have hAdequacy := view.kuhnRunAdequacy horizon hMenus steps
  have hAdeqBehavioral := hAdequacy.1 adapterBehavioral
  have hAdeqPure := hAdequacy.2
  calc
    view.boundedOutcomeFromBehavioral horizon
        (view.mixedPureToBehavioralProfile horizon hMenus mixed) steps
        =
      PMF.map historyOutcome
        (view.runDist horizon steps
          (view.mixedPureToBehavioralProfile horizon hMenus mixed)) := by
          simp [historyOutcome,
            boundedOutcomeFromBehavioral_eq_map_history]
    _ =
      PMF.map historyOutcome
        (view.runDist horizon steps
          (view.behavioralProfileOfKuhn horizon hMenus
            adapterBehavioral)) := by
          rfl
    _ =
      PMF.map historyOutcome
        (PMF.map O.lastState
          (O.runDist steps adapterBehavioral)) := by
          rw [hAdeqBehavioral]
    _ =
      PMF.map traceOutcome
        (O.runDist steps adapterBehavioral) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map traceOutcome
        ((Math.PMFProduct.pmfPi
          (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
          (O.runDistPure steps)) := by
          rw [hrun]
    _ =
      (Math.PMFProduct.pmfPi
        (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
        (fun pure =>
          PMF.map traceOutcome (O.runDistPure steps pure)) := by
          rw [PMF.map_bind]
    _ =
      (PMF.map
        (view.pureProfileToKuhn horizon hMenus)
        (Math.PMFProduct.pmfPi mixed)).bind
        (fun pure =>
          PMF.map traceOutcome (O.runDistPure steps pure)) := by
          rw [show
            Math.PMFProduct.pmfPi
                (view.mixedPureProfileToKuhn horizon hMenus mixed) =
              PMF.map
                (view.pureProfileToKuhn horizon hMenus)
                (Math.PMFProduct.pmfPi mixed) from by
                  simpa [mixedPureProfileToKuhn] using
                    view.pureProfileToKuhn_pmfPi horizon hMenus mixed]
    _ =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pure =>
          PMF.map traceOutcome
            (O.runDistPure steps
              (view.pureProfileToKuhn horizon hMenus pure))) := by
          rw [PMF.bind_map]
          rfl
    _ =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pure =>
          PMF.map historyOutcome
            (view.runDist horizon steps
              (view.legalPureToBehavioral horizon pure))) := by
          apply congrArg
            (fun f =>
              (Math.PMFProduct.pmfPi mixed).bind f)
          funext pure
          rw [← hAdeqPure pure]
          rw [PMF.map_comp]
          rfl
    _ =
      (Math.PMFProduct.pmfPi mixed).bind
      (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
          apply congrArg
            (fun f =>
              (Math.PMFProduct.pmfPi mixed).bind f)
          funext pure
          rw [boundedOutcomeFromPure_eq_map_history]

open Classical in
/-- Native option-outcome unilateral-deviation law for the canonical
mixed-to-behavioral Kuhn realizer. -/
theorem mixedPureToBehavioralProfile_unilateral_deviation_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player))
    (who : Player)
    (deviation : view.BoundedBehavioralStrategy horizon who) :
    let mixedDeviation :=
      view.behavioralStrategyToMixedPure horizon hMenus who deviation
    view.boundedOutcomeFromBehavioral horizon
        (Function.update
          (view.mixedPureToBehavioralProfile horizon hMenus mixed)
          who deviation) steps =
      (Math.PMFProduct.pmfPi
        (Function.update mixed who mixedDeviation)).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI : ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  let mixedDeviation :=
    view.behavioralStrategyToMixedPure horizon hMenus who deviation
  let mixed' := Function.update mixed who mixedDeviation
  let βsrc := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed'
  let βorig := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  let βtgtCore : O.BehavioralProfile :=
    Function.update βorig who
      (view.behavioralStrategyToKuhn horizon who deviation)
  let nativeTarget : view.BoundedBehavioralProfile horizon :=
    Function.update
      (view.mixedPureToBehavioralProfile horizon hMenus mixed)
      who deviation
  have hnative :
      view.behavioralProfileOfKuhn horizon hMenus βtgtCore =
        nativeTarget := by
    funext player
    apply Subtype.ext
    funext info
    by_cases hplayer : player = who
    · subst player
      have hnativeWho : nativeTarget who = deviation := by
        simp [nativeTarget]
      rw [hnativeWho]
      change
        PMF.map Subtype.val (βtgtCore who info) =
          deviation.1 info
      have hcoreWho :
          βtgtCore who =
            view.behavioralStrategyToKuhn horizon who deviation := by
        simp [βtgtCore]
      rw [hcoreWho]
      exact view.behavioralStrategyToKuhn_map_val
        horizon who deviation info
    · have hcore :
          βtgtCore player info = βorig player info := by
        simp [βtgtCore, Function.update_of_ne hplayer]
      have hnativePlayer :
          nativeTarget player =
            view.mixedPureToBehavioralProfile horizon hMenus mixed player := by
        simp [nativeTarget, Function.update_of_ne hplayer]
      rw [hnativePlayer]
      change PMF.map Subtype.val (βtgtCore player info) =
        PMF.map Subtype.val (βorig player info)
      rw [hcore]
  have hcoreTrace :
      O.runDist steps βsrc = O.runDist steps βtgtCore := by
    simpa [O, mixedDeviation, mixed', βsrc, βorig, βtgtCore] using
      view.mixedPureToKuhnBehavioralProfile_unilateral_deviation_runDist
        horizon steps hMenus mixed who deviation
  have hAdequacy := view.kuhnRunAdequacy horizon hMenus steps
  have hsrcNative :
      view.boundedOutcomeFromBehavioral horizon
          (view.mixedPureToBehavioralProfile horizon hMenus mixed') steps =
        view.boundedOutcomeFromBehavioral horizon nativeTarget steps := by
    let historyOutcome : view.BoundedHistory horizon → Option M.Outcome :=
      fun history => M.outcome history.lastState.state
    let traceOutcome : List (view.BoundedHistory horizon) → Option M.Outcome :=
      fun trace => historyOutcome (O.lastState trace)
    have hsrcAdeq := hAdequacy.1 βsrc
    have htgtAdeq := hAdequacy.1 βtgtCore
    calc
      view.boundedOutcomeFromBehavioral horizon
          (view.mixedPureToBehavioralProfile horizon hMenus mixed') steps
          =
        PMF.map historyOutcome
          (view.runDist horizon steps
            (view.behavioralProfileOfKuhn horizon hMenus βsrc)) := by
            simp [historyOutcome,
              boundedOutcomeFromBehavioral_eq_map_history,
              mixedPureToBehavioralProfile, βsrc]
      _ =
        PMF.map historyOutcome
          (PMF.map O.lastState (O.runDist steps βsrc)) := by
            rw [hsrcAdeq]
      _ =
        PMF.map traceOutcome (O.runDist steps βsrc) := by
            rw [PMF.map_comp]
            rfl
      _ =
        PMF.map traceOutcome (O.runDist steps βtgtCore) := by
            rw [hcoreTrace]
      _ =
        PMF.map historyOutcome
          (PMF.map O.lastState (O.runDist steps βtgtCore)) := by
            rw [PMF.map_comp]
            rfl
      _ =
        PMF.map historyOutcome
          (view.runDist horizon steps nativeTarget) := by
            rw [htgtAdeq]
            rw [hnative]
      _ =
        view.boundedOutcomeFromBehavioral horizon nativeTarget steps := by
            simp [historyOutcome,
              boundedOutcomeFromBehavioral_eq_map_history]
  calc
    view.boundedOutcomeFromBehavioral horizon nativeTarget steps
        =
      view.boundedOutcomeFromBehavioral horizon
          (view.mixedPureToBehavioralProfile horizon hMenus mixed') steps :=
        hsrcNative.symm
    _ =
      (Math.PMFProduct.pmfPi mixed').bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
        exact
          view.mixedPureToBehavioralProfile_optionOutcome
            horizon steps hMenus mixed'
    _ =
      (Math.PMFProduct.pmfPi
          (Function.update mixed who mixedDeviation)).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
        rfl

/-- Native option-outcome mixed-to-behavioral Kuhn realization. -/
theorem kuhn_mixed_to_behavioral_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    ∃ behavioral : view.BoundedBehavioralProfile horizon,
      view.boundedOutcomeFromBehavioral horizon behavioral steps =
        (Math.PMFProduct.pmfPi mixed).bind
          (fun pure =>
            view.boundedOutcomeFromPure horizon pure steps) := by
  classical
  refine ⟨view.mixedPureToBehavioralProfile horizon hMenus mixed, ?_⟩
  exact
    view.mixedPureToBehavioralProfile_optionOutcome
      horizon steps hMenus mixed

open Classical in
/-- Convert a native legal behavioral profile to the product mixed profile over
native legal pure strategies obtained by independently sampling each player's
Kuhn-adapter localStrategy strategy. -/
noncomputable def behavioralToMixedPure
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    ∀ player, PMF (view.BoundedPureStrategy horizon player) :=
  let adapterBehavioral :=
    view.behavioralProfileToKuhn horizon hMenus behavioral
  fun player =>
    PMF.map
      (view.pureStrategyOfKuhn horizon hMenus player)
      ((view.kuhnModel horizon hMenus).behavioralToMixed
        adapterBehavioral player)

open Classical in
theorem behavioralToMixedPure_pmfPi
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    PMF.map
        (view.pureProfileOfKuhn horizon hMenus)
        ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
          (view.behavioralProfileToKuhn horizon hMenus behavioral)) =
      Math.PMFProduct.pmfPi
        (view.behavioralToMixedPure horizon hMenus behavioral) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let adapterBehavioral :=
    view.behavioralProfileToKuhn horizon hMenus behavioral
  change
    PMF.map
        (fun profile : O.PureProfile =>
          fun player =>
            view.pureStrategyOfKuhn horizon hMenus player
              (profile player))
        (O.behavioralToMixedJoint adapterBehavioral) =
      Math.PMFProduct.pmfPi
        (fun player =>
          PMF.map
            (view.pureStrategyOfKuhn horizon hMenus player)
            (O.behavioralToMixed adapterBehavioral player))
  simpa [O, adapterBehavioral, ObsModelCore.behavioralToMixedJoint,
    behavioralToMixedPure, pureProfileOfKuhn] using
    Math.PMFProduct.pmfPi_push_coordwise
      (A := fun player => O.LocalStrategy player)
      (B := fun player => view.BoundedPureStrategy horizon player)
      (O.behavioralToMixed adapterBehavioral)
      (fun player => view.pureStrategyOfKuhn horizon hMenus player)

theorem behavioralToMixedPure_update
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon)
    (who : Player)
    (deviation : view.BoundedBehavioralStrategy horizon who) :
    view.behavioralToMixedPure horizon hMenus
        (Function.update behavioral who deviation) =
      Function.update
        (view.behavioralToMixedPure horizon hMenus behavioral)
        who
        ((view.behavioralToMixedPure horizon hMenus
          (Function.update behavioral who deviation)) who) := by
  classical
  funext player
  by_cases h : player = who
  · subst player
    rw [Function.update_self]
  · rw [Function.update_of_ne h]
    have hprofile :
        view.behavioralProfileToKuhn horizon hMenus
            (Function.update behavioral who deviation) player =
          view.behavioralProfileToKuhn horizon hMenus behavioral player := by
      funext info
      simp [behavioralProfileToKuhn, Function.update, h]
    exact congrArg
      (fun localProfile =>
        PMF.map (view.pureStrategyOfKuhn horizon hMenus player)
          (Math.PMFProduct.pmfPi localProfile))
      hprofile

open Classical in
/-- Native option-outcome behavioral-to-correlated-pure Kuhn realization for
behavioral profiles represented in the Kuhn adapter, with the exact erased
adapter distribution exposed. -/
theorem kuhn_adapterBehavioral_to_erased_correlated_pure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (adapterBehavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile) :
    view.boundedOutcomeFromBehavioral horizon
        (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
        steps =
      (PMF.map
        (view.pureProfileOfKuhn horizon hMenus)
        ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
          adapterBehavioral)).bind fun pure =>
        view.boundedOutcomeFromPure horizon pure steps := by
  classical
  let O := view.kuhnModel horizon hMenus
  let historyOutcome : view.BoundedHistory horizon → Option M.Outcome :=
    fun history => M.outcome history.lastState.state
  let traceOutcome : List (view.BoundedHistory horizon) → Option M.Outcome :=
    fun trace => historyOutcome (O.lastState trace)
  letI :
      ∀ player info,
        Fintype (view.KuhnActionAtInfo horizon player info) :=
    fun player info => inferInstance
  let correlatedPureAdapter := O.behavioralToMixedJoint adapterBehavioral
  let erasePure : O.PureProfile → view.BoundedPureProfile horizon :=
    view.pureProfileOfKuhn horizon hMenus
  have hrun :=
    view.kuhn_behavioral_to_correlated_pure_core
      horizon steps hMenus adapterBehavioral
  have hAdequacy := view.kuhnRunAdequacy horizon hMenus steps
  have hPureAdequacy := view.kuhnAdapterPureRunAdequacy horizon hMenus steps
  have hAdeqBehavioral := hAdequacy.1 adapterBehavioral
  calc
    view.boundedOutcomeFromBehavioral horizon
        (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
        steps
        =
      PMF.map historyOutcome
        (view.runDist horizon steps
          (view.behavioralProfileOfKuhn horizon hMenus
            adapterBehavioral)) := by
          simp [historyOutcome,
            boundedOutcomeFromBehavioral_eq_map_history]
    _ =
      PMF.map historyOutcome
        (PMF.map O.lastState
          (O.runDist steps adapterBehavioral)) := by
          rw [← hAdeqBehavioral]
    _ =
      PMF.map traceOutcome
        (O.runDist steps adapterBehavioral) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map traceOutcome
        (correlatedPureAdapter.bind (O.runDistPure steps)) := by
          simpa [O, correlatedPureAdapter] using
            congrArg (PMF.map traceOutcome) hrun
    _ =
      correlatedPureAdapter.bind
        (fun pure =>
          PMF.map traceOutcome (O.runDistPure steps pure)) := by
          rw [PMF.map_bind]
    _ =
      correlatedPureAdapter.bind
        (fun pure =>
          PMF.map historyOutcome
            (view.runDist horizon steps
              (view.legalPureToBehavioral horizon
                (erasePure pure)))) := by
          apply congrArg
            (fun f => correlatedPureAdapter.bind f)
          funext pure
          rw [← hPureAdequacy pure]
          rw [PMF.map_comp]
          rfl
    _ =
      correlatedPureAdapter.bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon
            (erasePure pure) steps) := by
          apply congrArg
            (fun f => correlatedPureAdapter.bind f)
          funext pure
          rw [boundedOutcomeFromPure_eq_map_history]
    _ =
      (PMF.map erasePure correlatedPureAdapter).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
          rw [PMF.bind_map]
          rfl

/-- Native option-outcome behavioral-to-correlated-pure Kuhn realization for
behavioral profiles represented in the Kuhn adapter. The resulting distribution
is over native legal pure profiles obtained by erasing adapter pure
strategies. -/
theorem kuhn_adapterBehavioral_to_correlated_pure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (adapterBehavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile) :
    ∃ correlated : PMF (view.BoundedPureProfile horizon),
      view.boundedOutcomeFromBehavioral horizon
          (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
          steps =
        correlated.bind fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
  classical
  letI :
      ∀ player,
        Fintype ((view.kuhnModel horizon hMenus).InfoState player) :=
    fun player => Fintype.ofFinite _
  refine
    ⟨PMF.map
      (view.pureProfileOfKuhn horizon hMenus)
      ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
        adapterBehavioral), ?_⟩
  exact
    view.kuhn_adapterBehavioral_to_erased_correlated_pure_optionOutcome
      horizon steps hMenus adapterBehavioral

open Classical in
/-- Native option-outcome behavioral-to-product-mixed Kuhn realization for an
arbitrary native legal behavioral profile. -/
theorem kuhn_behavioral_to_mixedPure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    view.boundedOutcomeFromBehavioral horizon behavioral steps =
      (Math.PMFProduct.pmfPi
        (view.behavioralToMixedPure horizon hMenus behavioral)).bind
        fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
  classical
  let adapterBehavioral :=
    view.behavioralProfileToKuhn horizon hMenus behavioral
  calc
    view.boundedOutcomeFromBehavioral horizon behavioral steps
        =
      view.boundedOutcomeFromBehavioral horizon
        (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
        steps := by
          simp [adapterBehavioral]
    _ =
      (PMF.map
        (view.pureProfileOfKuhn horizon hMenus)
        ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
          adapterBehavioral)).bind fun pure =>
        view.boundedOutcomeFromPure horizon pure steps := by
          exact
            view.kuhn_adapterBehavioral_to_erased_correlated_pure_optionOutcome
              horizon steps hMenus adapterBehavioral
    _ =
      (Math.PMFProduct.pmfPi
        (view.behavioralToMixedPure horizon hMenus behavioral)).bind
        fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
          rw [view.behavioralToMixedPure_pmfPi horizon hMenus behavioral]

/-- Native option-outcome behavioral-to-correlated-pure Kuhn realization for
an arbitrary native legal behavioral profile. -/
theorem kuhn_behavioral_to_correlated_pure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    ∃ correlated : PMF (view.BoundedPureProfile horizon),
      view.boundedOutcomeFromBehavioral horizon behavioral steps =
        correlated.bind fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
  classical
  rcases
      view.kuhn_adapterBehavioral_to_correlated_pure_optionOutcome
        horizon steps hMenus
        (view.behavioralProfileToKuhn horizon hMenus behavioral) with
    ⟨correlated, hcorrelated⟩
  refine ⟨correlated, ?_⟩
  simpa using hcorrelated

end RoundView

end Machine

end Vegas
