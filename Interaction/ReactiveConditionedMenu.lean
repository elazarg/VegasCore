module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveResponseMenu

@[expose] public section

/-! # Menu histories under restriction of the initial support -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) {restricted initial : PMF app.State} {horizon : Nat}
  {scheduler : app.Scheduler}

/-- The same legal responses and builder commands under an initializer with larger support. -/
def traceOfInitialSupportSubset (included : restricted.support ⊆ initial.support) :
    ∀ {state}, (menu.protocol restricted horizon scheduler).Trace state →
      (menu.protocol initial horizon scheduler).Trace state
  | _, .start => .start
  | _, .extend (source := before) prior joint legal realized =>
      .extend (traceOfInitialSupportSubset included prior) joint legal (by
        cases before with
        | none =>
          obtain ⟨start, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨start, included member, rfl⟩
        | some _ => exact realized)

theorem trace_at_root (trace : (menu.protocol initial horizon scheduler).Trace none) :
    trace = .start := by
  have bound := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler trace)
  rw [menu.toRawTrace_length] at bound
  change trace.length + (2 * horizon + 1) ≤ 2 * horizon + 1 at bound
  have root : ∀ {state} (t : (menu.protocol initial horizon scheduler).Trace state),
      t.length = 0 → HEq t (Trace.start (E := menu.protocol initial horizon scheduler)) := by
    intro state t zero
    cases t with
    | start => rfl
    | extend _ _ _ _ => cases zero
  exact eq_of_heq (root trace (by omega))

/-- Enlarging the initial support changes neither the controls nor the actions of a history. -/
def historyOfInitialSupportSubset (included : restricted.support ⊆ initial.support)
    (history : (menu.protocol restricted horizon scheduler).History) :
    (menu.protocol initial horizon scheduler).History :=
  ⟨history.state, menu.traceOfInitialSupportSubset included history.trace⟩

theorem traceOfInitialSupportSubset_injective (included : restricted.support ⊆ initial.support)
    {state} : Function.Injective
      (menu.traceOfInitialSupportSubset (scheduler := scheduler) (horizon := horizon)
        included (state := state)) := by
  intro first
  induction first with
  | start => intro other same; cases other <;> cases same; rfl
  | extend prior joint legal realized ih =>
      intro other same
      cases other with
      | start => cases same
      | extend prior' joint' legal' realized' =>
          simp only [traceOfInitialSupportSubset, Trace.extend.injEq] at same
          obtain ⟨rfl, traces, actions⟩ := same
          cases ih (eq_of_heq traces)
          cases actions
          rfl

theorem historyOfInitialSupportSubset_injective (included : restricted.support ⊆ initial.support) :
    Function.Injective (menu.historyOfInitialSupportSubset (scheduler := scheduler)
      (horizon := horizon) included) := by
  rintro ⟨first, t⟩ ⟨second, u⟩ eq
  cases congrArg History.state eq
  exact congrArg (History.mk _) (menu.traceOfInitialSupportSubset_injective included
    (eq_of_heq (History.mk.inj eq).2))

/-- Reinterpreting a history at larger initial support preserves each private view. -/
def infoHistoryOfInitialSupportSubset (included : restricted.support ⊆ initial.support)
    (who : Principal) (info : app.Info)
    (h : (menu.information restricted horizon scheduler).InformationHistory who info) :
    (menu.information initial horizon scheduler).InformationHistory who info :=
  ⟨menu.historyOfInitialSupportSubset included h.1, by
    calc
      _ = app.observe who h.1.state := menu.info initial horizon scheduler who _
      _ = _ := (menu.info restricted horizon scheduler who h.1.trace).symm.trans h.2⟩

theorem infoHistoryOfInitialSupportSubset_injective
    (included : restricted.support ⊆ initial.support)
    (who : Principal) (info : app.Info) :
    Function.Injective (menu.infoHistoryOfInitialSupportSubset (scheduler := scheduler)
      (horizon := horizon) included who info) := by
  intro a b eq
  apply Subtype.ext
  exact menu.historyOfInitialSupportSubset_injective included (congrArg Subtype.val eq)

theorem information_menu_initial_eq (who : Principal) (info : app.Info) :
    (menu.information restricted horizon scheduler).menu who info =
      (menu.information initial horizon scheduler).menu who info := by
  cases info <;> rfl

/-- A component choice is selected from the player's ordinary information. The menu
and hence its available local choices are independent of the initialization law. -/
def signalStrategy {Signal : Type*} {component : Signal → PMF app.State}
    (read : Principal → app.Info → Signal)
    (strategies : ∀ value who,
      (menu.information (component value) horizon scheduler).BehavioralPolicy who)
    (who : Principal) : (menu.information initial horizon scheduler).BehavioralPolicy who :=
  fun info => by
    cases info with
    | none => exact strategies (read who none) who none
    | some view => exact strategies (read who (some view)) who (some view)

/-- Reindex a legal local choice across initializers of the same ledger menu. -/
def choiceOfInitial (who : Principal) (info : app.Info)
    (choice : (menu.information initial horizon scheduler).Choice who info) :
    (menu.information restricted horizon scheduler).Choice who info :=
  ⟨choice.1, by
    rw [menu.information_menu_initial_eq (initial := initial)]
    exact choice.2⟩

theorem signalStrategy_apply {Signal : Type*} {component : Signal → PMF app.State}
    (read : Principal → app.Info → Signal)
    (strategies : ∀ value who,
      (menu.information (component value) horizon scheduler).BehavioralPolicy who)
    (who : Principal) (info : app.Info)
    (choice : (menu.information initial horizon scheduler).Choice who info) :
    menu.signalStrategy read strategies who info choice =
      strategies (read who info) who info (menu.choiceOfInitial who info choice) := by
  cases info <;> rfl

end Interaction.ReactiveApplication.ResponseMenu
