/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Kuhn.PerfectRecall

/-!
# Kuhn adapter: strategy translation

Round-trip translation between native legal pure/behavioral strategies and Kuhn
adapter strategies, with the inverse laws and the behavioral-to-mixed-pure
factorization.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} {M : Machine Player}

namespace RoundView

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
        (Math.ProbabilityMassFunction.reweightPMF
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
    exact Math.ProbabilityMassFunction.sum_mul_pmf_ne_top
      (view.behavioralStrategyToKuhnMixed
        horizon hMenus player strategy)
      (fun localStrategy : O.LocalStrategy player =>
        Math.ParameterizedChain.pureRun O.pureStep O.init steps
          (Function.update profile player localStrategy) trace)
      (fun _ => PMF.coe_le_one _ trace)
  simpa [behavioralStrategyToKuhnMixed, O] using
    Math.PMFProduct.reweightPMF_pmfPi_push_coord_of_ignores'
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
        (Math.ProbabilityMassFunction.reweightPMF
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


end RoundView

end Machine

end Vegas
