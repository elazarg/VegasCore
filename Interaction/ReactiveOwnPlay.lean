/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import GameTheory.Analysis.Protocol.CounterfactualRegret

/-! # Own play is determined by reactive decision recall

Every stored entry records the observation and response at that decision.
Its preceding entries reconstruct the recall available then. Thus current
decision information determines the canonical own-play sequence. Inactive
information remains `none`; no observation of inactive rounds is introduced.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

def ownPlayFrom (earlier : List app.PlayerEntry) : List app.PlayerEntry →
    List (app.Info × app.Action)
  | [] => []
  | entry :: rest => ownPlayFrom (earlier ++ [entry]) rest ++
      [(some (earlier, entry.beforeView), entry.action)]

def recallOwnPlay (past : List app.PlayerEntry) : List (app.Info × app.Action) :=
  app.ownPlayFrom [] past

theorem ownPlayFrom_append (earlier past : List app.PlayerEntry) (entry : app.PlayerEntry) :
    app.ownPlayFrom earlier (past ++ [entry]) =
      (some (earlier ++ past, entry.beforeView), entry.action) :: app.ownPlayFrom earlier past := by
  induction past generalizing earlier with
  | nil => simp only [List.nil_append, ownPlayFrom, List.append_nil]
  | cons first rest ih =>
      simp only [List.cons_append, ownPlayFrom, ih, List.cons_append]
      simp only [List.append_assoc, List.singleton_append]

theorem recallOwnPlay_append (past : List app.PlayerEntry) (entry : app.PlayerEntry) :
    app.recallOwnPlay (past ++ [entry]) =
      (some (past, entry.beforeView), entry.action) :: app.recallOwnPlay past := by
  simpa only [recallOwnPlay, List.nil_append] using app.ownPlayFrom_append [] past entry

def recallAt (who : Principal) : app.ProtocolState → List app.PlayerEntry
  | none => []
  | some control => control.execution.recall who

variable [DecidableEq Principal]

theorem respond_ownPlay (execution : app.Execution) (who : Principal) (response : app.Action) :
    app.recallOwnPlay ((execution.respond app who response).recall who) =
      (some (execution.recall who, execution.observe app who), response) ::
        app.recallOwnPlay (execution.recall who) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ↓reduceIte, recallOwnPlay_append]
  | some transmission =>
      cases transmission <;> simp only [Execution.respond, ↓reduceIte, recallOwnPlay_append]

theorem trace_ownPlay (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) : ∀ {state} (history : (app.protocol initial horizon scheduler).Trace state),
    (app.signals initial horizon scheduler).ownPlay who history =
      app.recallOwnPlay (app.recallAt who state)
  | _, .start => rfl
  | after, .extend prior joint legal realized => by
      rename_i before
      rw [InfoSignals.ownPlay_extend]
      have earlier := trace_ownPlay initial horizon scheduler who prior
      have idle (inactive : ¬ (app.protocol initial horizon scheduler).active before who) :
          joint who = none :=
        LegalOption.eq_none_of_inactive _
          ((app.protocol initial horizon scheduler).legalOption_of_legal legal who) inactive
      cases before with
      | none =>
          have chosen := idle (by simp [protocol, actor])
          obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ realized
          simp only [chosen, earlier]
          rfl
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some owner =>
              cases FinDist.mem_support_pure.mp realized
              by_cases same : who = owner
              · subst owner
                cases chosen : joint who with
                | none =>
                    have impossible := legal.2 who
                    simp only [chosen, protocol, actor, Option.bind_some] at impossible
                    exact (impossible trivial).elim
                | some response =>
                    simp only [chosen, earlier, app.info, observe, ↓reduceIte, recallAt,
                      Option.getD_some]
                    exact (app.respond_ownPlay execution who response).symm
              · have inactive : ¬ (app.protocol initial horizon scheduler).active
                    (some ⟨remaining, some owner, execution⟩) who := by
                  simpa only [protocol, actor, Option.bind_some, Option.some.injEq] using
                    Ne.symm same
                rw [idle inactive, earlier]
                exact congrArg app.recallOwnPlay
                  (app.respond_recall_other execution owner who same _).symm
          | none =>
              have chosen := idle (by simp [protocol, actor])
              rw [chosen, earlier]
              cases remaining with
              | zero => cases FinDist.mem_support_pure.mp realized; rfl
              | succ remaining =>
                  obtain ⟨command, _, supported⟩ :=
                    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ realized)
                  obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
                  exact congrArg (fun recall => app.recallOwnPlay (recall who))
                    (app.environmentStep_recall execution next command moved).symm

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu)

theorem ownPlay_toRawTrace (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal) {state}
    (history : (menu.protocol initial horizon scheduler).Trace state) :
    (app.signals initial horizon scheduler).ownPlay who
        (menu.toRawTrace initial horizon scheduler history) =
      (menu.signals initial horizon scheduler).ownPlay who history := by
  induction history with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [toRawTrace, InfoSignals.ownPlay_extend, ih]
      cases joint who with
      | none => rfl
      | some response =>
          rw [app.info, menu.info]

theorem ownPlay_of_info_some (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal)
    (history : (menu.protocol initial horizon scheduler).History)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace =
      some (past, view)) :
    (menu.information initial horizon scheduler).ownPlay who history.trace =
      app.recallOwnPlay past := by
  change (menu.signals initial horizon scheduler).ownPlay who history.trace = _
  rw [← menu.ownPlay_toRawTrace initial horizon scheduler who history.trace,
    app.trace_ownPlay]
  change (menu.signals initial horizon scheduler).infoOf who history.trace = _ at observed
  rw [menu.info] at observed
  cases stateEq : history.state with
  | none => simp only [stateEq, observe] at observed; contradiction
  | some control =>
      by_cases active : control.actor = some who
      · simp only [stateEq, observe, active, ↓reduceIte] at observed
        have same := congrArg Prod.fst (Option.some.inj observed)
        exact congrArg app.recallOwnPlay same
      · simp only [stateEq, observe, active, ↓reduceIte] at observed
        contradiction

/-- At a decision site, private recall determines the whole canonical own-play
sequence even though the common inactive information state forgets it. -/
theorem ownPlay_at_site (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (first second : (menu.information initial horizon scheduler).InformationHistory who site.1) :
    (menu.information initial horizon scheduler).ownPlay who first.1.trace =
      (menu.information initial horizon scheduler).ownPlay who second.1.trace := by
  rcases site with ⟨observed, reachable⟩
  cases observed with
  | none =>
      obtain ⟨_, _, response, member⟩ := reachable
      change some response = none at member
      contradiction
  | some data =>
      exact (menu.ownPlay_of_info_some initial horizon scheduler who first.1 data.1 data.2
        first.2).trans
        (menu.ownPlay_of_info_some initial horizon scheduler who second.1 data.1 data.2
          second.2).symm

theorem commonPlayerReachAt (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    (strategy : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) (site : (menu.information initial horizon scheduler).InformationSite who) :
    InformationModel.CommonPlayerReachAt (menu.information initial horizon scheduler)
      strategy who site := by
  obtain ⟨reference, _running, _action⟩ := site.2
  refine ⟨(menu.information initial horizon scheduler).playerReachProbability
    strategy who reference.1.trace, ?_⟩
  intro history
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    menu.ownPlay_at_site initial horizon scheduler who site history reference]

end ResponseMenu
end Interaction.ReactiveApplication
