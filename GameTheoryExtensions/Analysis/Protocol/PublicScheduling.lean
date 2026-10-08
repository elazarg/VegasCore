/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit
import GameTheoryExtensions.Analysis.Protocol.ProportionalBeliefTransport
import GameTheoryExtensions.Analysis.Protocol.ReachBounds
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Sequential equilibrium under bounded public scheduling

A finite source protocol is expanded by a public scheduler: before every source
transition, a fixed number of public tokens is drawn from a kernel that reads
only a public projection of the source history, the transcript so far and the
number of draws still pending. Waits leave the source history unchanged and
offer no player a choice; a ready state offers exactly the source menus and
runs the source transition. Every player observes its source information
together with the public transcript and the pending count.

`GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium` lifts
every sequential equilibrium of the source model to one of the expansion with
the same law of erased terminal histories. The lift plays the source law at
every expanded decision; its beliefs are the source Bayes beliefs transported
along the fixed serialization of the transcript. The public projection must be
recoverable from every player's information at every decision (the two
hypotheses `recoverable` and `actors`), so that the scheduler's likelihood is
constant on every source information set and cancels in Bayes' rule.
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability ExecutionProtocol
open scoped ENNReal

variable {ι : Type} {E : ExecutionProtocol ι}

/-- A bounded public scheduler for a source protocol: a public projection of
source histories, the number of public draws before each source transition,
and the kernel of each draw, which reads the public projection of the current
source history, the public transcript so far and the number of draws still
pending. -/
structure PublicScheduler (E : ExecutionProtocol ι) (Pub Token : Type) where
  /-- The public projection the scheduler reads. -/
  pub : E.History → Pub
  /-- The number of public draws before each source transition. -/
  draws : ℕ
  /-- The kernel of one public draw. -/
  kernel : Pub → List Token → ℕ → PMF Token

namespace PublicScheduler

variable {Pub Token : Type} (S : PublicScheduler E Pub Token)

/-- An expanded state: the source history so far, the public transcript, and
the number of public draws still pending before the next source transition. -/
structure State (_S : PublicScheduler E Pub Token) where
  /-- The source history so far. -/
  source : E.History
  /-- The public transcript so far. -/
  transcript : List Token
  /-- Draws still pending before the next source transition. -/
  pending : ℕ

/-- Players act exactly when no draw is pending, with their source activity. -/
def active (s : S.State) (i : ι) : Prop :=
  match s.pending with
  | 0 => E.active s.source.state i
  | _ + 1 => False

/-- The source menus when no draw is pending; nothing while waiting. -/
def available (s : S.State) (i : ι) : Set (E.Action i) :=
  match s.pending with
  | 0 => E.available s.source.state i
  | _ + 1 => ∅

/-- The expansion stops exactly when the source history has stopped. -/
def terminal (s : S.State) : Prop := E.terminal s.source.state

/-- Legality in the expansion, before the protocol is assembled. -/
abbrev Legal (s : S.State) (joint : ∀ i, Option (E.Action i)) : Prop :=
  ¬ S.terminal s ∧ IsLegalJoint (S.active s) (S.available s) joint

/-- One wait draws a public token; a ready state runs one source transition
and resets the pending count. -/
def step : (s : S.State) → { joint : ∀ i, Option (E.Action i) // S.Legal s joint } → PMF S.State
  | ⟨h, τ, 0⟩, ⟨joint, legal⟩ =>
      (E.step h.state ⟨joint, legal⟩).bindOnSupport fun _ realized =>
        PMF.pure ⟨h.extend legal realized, τ, S.draws⟩
  | ⟨h, τ, p + 1⟩, _ =>
      (S.kernel (S.pub h) τ (p + 1)).map fun token => ⟨h, τ ++ [token], p⟩

/-- The expanded protocol. -/
@[reducible] def protocol : ExecutionProtocol ι where
  State := S.State
  Action := E.Action
  init := ⟨E.initHistory, [], S.draws⟩
  active := S.active
  available := S.available
  terminal := S.terminal
  step := S.step
  progress := by
    rintro ⟨h, τ, p⟩ running
    cases p with
    | zero =>
        obtain ⟨joint, legal⟩ := E.progress h.state running
        exact ⟨joint, legal⟩
    | succ p => exact ⟨E.noop, fun _ => id⟩

/-- Legality at a ready state is source legality. -/
theorem legal_ready (h : E.History) (τ : List Token) (joint : ∀ i, Option (E.Action i)) :
    S.protocol.Legal ⟨h, τ, 0⟩ joint ↔ E.Legal h.state joint :=
  Iff.rfl

/-- Nobody is active while a draw is pending. -/
@[simp] theorem active_waiting (h : E.History) (τ : List Token) (p : ℕ) (i : ι) :
    S.active ⟨h, τ, p + 1⟩ i = False :=
  rfl

/-- Activity at a ready state is source activity. -/
@[simp] theorem active_ready (h : E.History) (τ : List Token) (i : ι) :
    S.active ⟨h, τ, 0⟩ i = E.active h.state i :=
  rfl

/-- The menu at a ready state is the source menu. -/
@[simp] theorem available_ready (h : E.History) (τ : List Token) (i : ι) :
    S.available ⟨h, τ, 0⟩ i = E.available h.state i :=
  rfl

/-- The expansion is terminal exactly when the source history is. -/
theorem terminal_iff (s : S.State) : S.protocol.terminal s ↔ E.terminal s.source.state :=
  Iff.rfl

/-- The only legal joint action while a draw is pending is the no-op. -/
theorem eq_noop_of_legal_waiting (h : E.History) (τ : List Token) (p : ℕ)
    {joint : ∀ i, Option (E.Action i)} (legal : S.protocol.Legal ⟨h, τ, p + 1⟩ joint) :
    joint = S.protocol.noop :=
  S.protocol.eq_noop_of_legal_of_inactive legal fun _ => id

/-- A wait step appends one token and decrements the pending count. -/
theorem mem_step_waiting (h : E.History) (τ : List Token) (p : ℕ)
    (joint : { joint : ∀ i, Option (E.Action i) // S.protocol.Legal ⟨h, τ, p + 1⟩ joint })
    (target : S.State) :
    target ∈ (S.protocol.step ⟨h, τ, p + 1⟩ joint).support ↔
      ∃ token ∈ (S.kernel (S.pub h) τ (p + 1)).support, target = ⟨h, τ ++ [token], p⟩ := by
  change target ∈ ((S.kernel (S.pub h) τ (p + 1)).map _).support ↔ _
  rw [PMF.support_map]
  constructor
  · rintro ⟨token, drawn, rfl⟩
    exact ⟨token, drawn, rfl⟩
  · rintro ⟨token, drawn, rfl⟩
    exact ⟨token, drawn, rfl⟩

/-- A ready step runs the source transition and resets the pending count. -/
theorem mem_step_ready (h : E.History) (τ : List Token)
    (joint : { joint : ∀ i, Option (E.Action i) // S.protocol.Legal ⟨h, τ, 0⟩ joint })
    (target : S.State) :
    target ∈ (S.protocol.step ⟨h, τ, 0⟩ joint).support ↔
      ∃ (reached : E.State) (realized : reached ∈ (E.step h.state ⟨joint.1, joint.2⟩).support),
        target = ⟨h.extend joint.2 realized, τ, S.draws⟩ := by
  obtain ⟨joint, legal⟩ := joint
  change target ∈ ((E.step h.state ⟨joint, legal⟩).bindOnSupport _).support ↔ _
  rw [PMF.support_bindOnSupport]
  constructor
  · intro member
    obtain ⟨reached, realized, hit⟩ := Set.mem_iUnion₂.mp member
    exact ⟨reached, realized, (PMF.mem_support_pure_iff _ _).mp hit⟩
  · rintro ⟨reached, realized, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨reached, realized, (PMF.mem_support_pure_iff _ _).mpr rfl⟩

/-- The pending count never exceeds the draw budget, and the transcript has
exactly one token per draw taken so far. -/
theorem invariant : ∀ {s : S.State} (_ : S.protocol.Trace s),
    s.pending ≤ S.draws ∧
      s.transcript.length + s.pending = S.draws * (s.source.trace.length + 1)
  | _, .start => ⟨le_rfl, rfl⟩
  | _, .extend (source := before) prior joint legal realized => by
      obtain ⟨bound, count⟩ := invariant prior
      obtain ⟨h, τ, p⟩ := before
      dsimp only at bound count
      cases p with
      | zero =>
          obtain ⟨reached, realized', rfl⟩ := (S.mem_step_ready h τ ⟨joint, legal⟩ _).mp realized
          dsimp only [History.extend, Trace.length]
          constructor
          · exact le_rfl
          · simp only [add_zero] at count
            rw [count]
            ring
      | succ p =>
          obtain ⟨token, _, rfl⟩ := (S.mem_step_waiting h τ p ⟨joint, legal⟩ _).mp realized
          dsimp only
          simp only [List.length_append, List.length_singleton] at count ⊢
          omega

/-- Expanded histories have one transition per token and per source step. -/
theorem trace_length_eq : ∀ {s : S.State} (trace : S.protocol.Trace s),
    trace.length = s.transcript.length + s.source.trace.length
  | _, .start => rfl
  | _, .extend (source := before) prior joint legal realized => by
      have ih := trace_length_eq prior
      obtain ⟨h, τ, p⟩ := before
      dsimp only at ih
      cases p with
      | zero =>
          obtain ⟨reached, realized', rfl⟩ := (S.mem_step_ready h τ ⟨joint, legal⟩ _).mp realized
          dsimp only [Trace.length, History.extend]
          omega
      | succ p =>
          obtain ⟨token, _, rfl⟩ := (S.mem_step_waiting h τ p ⟨joint, legal⟩ _).mp realized
          dsimp only [Trace.length]
          simp only [List.length_append, List.length_singleton]
          omega

/-- A source horizon bounds the expansion by one draw budget per source step. -/
theorem boundedHorizon {bound : ℕ} (bounded : E.BoundedHorizon bound) :
    S.protocol.BoundedHorizon ((S.draws + 1) * bound) := by
  intro s trace long
  obtain ⟨_, count⟩ := S.invariant trace
  have length := S.trace_length_eq trace
  apply bounded s.source.state s.source.trace
  by_contra short
  have short' : s.source.trace.length < bound := Nat.lt_of_not_le short
  have : s.transcript.length ≤ S.draws * (s.source.trace.length + 1) := by omega
  nlinarith

/-! ## The expanded information model -/

variable (M : InformationModel E)

/-- Every player observes its source information, the public transcript and
the pending count; a transition reports the new values of all three. -/
def signals : InfoSignals S.protocol where
  PublicSignal := List Token × ℕ
  PrivateSignal i := M.InfoState i
  initialPublic := ([], S.draws)
  initialPrivate i := M.infoOf i E.initHistory.trace
  publicSignal event := (event.target.transcript, event.target.pending)
  privateSignal i event := M.infoOf i event.target.source.trace
  InfoState i := M.InfoState i × List Token × ℕ
  initInfo _ priv pub := (priv, pub.1, pub.2)
  pushInfo _ _ _ priv pub := (priv, pub.1, pub.2)

/-- The expanded information of a history is the source information of its
source history with the public transcript and pending count. -/
theorem infoOf_eq (i : ι) : ∀ {s : S.State} (trace : S.protocol.Trace s),
    (S.signals M).infoOf i trace = (M.infoOf i s.source.trace, s.transcript, s.pending)
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- The expanded menu: the source menu when no draw is pending, silence
otherwise. -/
def menu (i : ι) : (S.signals M).InfoState i → Set (Option (E.Action i))
  | (info, _, 0) => M.menu i info
  | (_, _, _ + 1) => {none}

/-- The menu at a ready information value is the source menu. -/
@[simp] theorem menu_ready (i : ι) (info : M.InfoState i) (τ : List Token) :
    S.menu M i (info, τ, 0) = M.menu i info :=
  rfl

/-- The menu while a draw is pending is silence. -/
@[simp] theorem menu_waiting (i : ι) (info : M.InfoState i) (τ : List Token) (p : ℕ) :
    S.menu M i (info, τ, p + 1) = {none} :=
  rfl

/-- The expanded information model. -/
def model : InformationModel S.protocol where
  toInfoSignals := S.signals M
  menu := S.menu M
  menu_adequate := by
    rintro i ⟨h, τ, p⟩ trace choice
    rw [S.infoOf_eq M i trace]
    dsimp only
    cases p with
    | zero =>
        rw [S.menu_ready, M.menu_adequate i h.trace choice]
        cases choice with
        | none => simp only [LegalOption, active_ready]
        | some action => simp only [LegalOption, active_ready, available_ready]
    | succ p =>
        rw [S.menu_waiting]
        cases choice with
        | none => simp only [LegalOption, active_waiting, Set.mem_singleton_iff, not_false_eq_true]
        | some action =>
            simp only [LegalOption, active_waiting, Set.mem_singleton_iff, reduceCtorEq,
              false_and]

/-- Choices at a ready information value are source choices. -/
theorem choice_ready (i : ι) (info : M.InfoState i) (τ : List Token) :
    (S.model M).Choice i (info, τ, 0) = M.Choice i info :=
  rfl

instance (i : ι) [DecidableEq (M.InfoState i)] [DecidableEq Token] :
    DecidableEq ((S.model M).InfoState i) :=
  inferInstanceAs (DecidableEq (M.InfoState i × List Token × ℕ))

/-! ## Case analysis on expanded histories -/

/-- The source history of an expanded history. -/
abbrev erase (x : S.protocol.History) : E.History := x.state.source

/-- A waiting history extended by one draw. -/
def waitExtend {h : E.History} {τ : List Token} {p : ℕ}
    (prior : S.protocol.Trace ⟨h, τ, p + 1⟩) (running : ¬ E.terminal h.state) (token : Token)
    (drawn : token ∈ (S.kernel (S.pub h) τ (p + 1)).support) : S.protocol.History :=
  (⟨⟨h, τ, p + 1⟩, prior⟩ : S.protocol.History).extend
    (S.protocol.noop_isLegal running fun _ => id)
    ((S.mem_step_waiting h τ p ⟨S.protocol.noop, S.protocol.noop_isLegal running fun _ => id⟩
      ⟨h, τ ++ [token], p⟩).mpr ⟨token, drawn, rfl⟩)

/-- A ready history extended by one source transition. -/
def readyExtend {h : E.History} {τ : List Token} (prior : S.protocol.Trace ⟨h, τ, 0⟩)
    {joint : ∀ i, Option (E.Action i)} (legal : E.Legal h.state joint) {reached : E.State}
    (realized : reached ∈ (E.step h.state ⟨joint, legal⟩).support) : S.protocol.History :=
  (⟨⟨h, τ, 0⟩, prior⟩ : S.protocol.History).extend ((S.legal_ready h τ joint).mpr legal)
    ((S.mem_step_ready h τ ⟨joint, legal⟩ ⟨h.extend legal realized, τ, S.draws⟩).mpr
      ⟨reached, realized, rfl⟩)

/-- Every expanded history is initial, a draw after a waiting history, or a
source transition after a ready history. -/
theorem history_cases (x : S.protocol.History) :
    x = S.protocol.initHistory ∨
      (∃ (h : E.History) (τ : List Token) (p : ℕ) (prior : S.protocol.Trace ⟨h, τ, p + 1⟩)
        (running : ¬ E.terminal h.state) (token : Token)
        (drawn : token ∈ (S.kernel (S.pub h) τ (p + 1)).support),
        x = S.waitExtend prior running token drawn) ∨
      ∃ (h : E.History) (τ : List Token) (prior : S.protocol.Trace ⟨h, τ, 0⟩)
        (joint : ∀ i, Option (E.Action i)) (legal : E.Legal h.state joint) (reached : E.State)
        (realized : reached ∈ (E.step h.state ⟨joint, legal⟩).support),
        x = S.readyExtend prior legal realized := by
  obtain ⟨s, trace⟩ := x
  cases trace with
  | start => exact Or.inl rfl
  | @extend before _ prior joint legal realized =>
      obtain ⟨h, τ, p⟩ := before
      cases p with
      | zero =>
          obtain ⟨reached, realized', rfl⟩ :=
            (S.mem_step_ready h τ ⟨joint, legal⟩ _).mp realized
          exact Or.inr (Or.inr ⟨h, τ, prior, joint, legal, reached, realized', rfl⟩)
      | succ p =>
          obtain ⟨token, drawn, rfl⟩ := (S.mem_step_waiting h τ p ⟨joint, legal⟩ _).mp realized
          obtain rfl := S.eq_noop_of_legal_waiting h τ p legal
          exact Or.inr (Or.inl ⟨h, τ, p, prior, legal.1, token, drawn, rfl⟩)

theorem waitExtend_state {h : E.History} {τ : List Token} {p : ℕ}
    (prior : S.protocol.Trace ⟨h, τ, p + 1⟩) (running : ¬ E.terminal h.state) (token : Token)
    (drawn : token ∈ (S.kernel (S.pub h) τ (p + 1)).support) :
    (S.waitExtend prior running token drawn).state = ⟨h, τ ++ [token], p⟩ :=
  rfl

theorem readyExtend_state {h : E.History} {τ : List Token}
    (prior : S.protocol.Trace ⟨h, τ, 0⟩) {joint : ∀ i, Option (E.Action i)}
    (legal : E.Legal h.state joint) {reached : E.State}
    (realized : reached ∈ (E.step h.state ⟨joint, legal⟩).support) :
    (S.readyExtend prior legal realized).state = ⟨h.extend legal realized, τ, S.draws⟩ :=
  rfl

theorem waitExtend_length {h : E.History} {τ : List Token} {p : ℕ}
    (prior : S.protocol.Trace ⟨h, τ, p + 1⟩) (running : ¬ E.terminal h.state) (token : Token)
    (drawn : token ∈ (S.kernel (S.pub h) τ (p + 1)).support) :
    (S.waitExtend prior running token drawn).trace.length = prior.length + 1 :=
  rfl

theorem readyExtend_length {h : E.History} {τ : List Token}
    (prior : S.protocol.Trace ⟨h, τ, 0⟩) {joint : ∀ i, Option (E.Action i)}
    (legal : E.Legal h.state joint) {reached : E.State}
    (realized : reached ∈ (E.step h.state ⟨joint, legal⟩).support) :
    (S.readyExtend prior legal realized).trace.length = prior.length + 1 :=
  rfl

/-- Two expanded histories ending at the same state are equal: the state
records the source history, the transcript and the pending count, which
together determine every transition taken. -/
theorem eq_of_state_eq : ∀ (n : ℕ) (x y : S.protocol.History), x.trace.length = n →
    x.state = y.state → x = y := by
  intro n
  induction n with
  | zero =>
      intro x y length same
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · rcases S.history_cases y with rfl | ⟨h', τ', p', prior', running', token', drawn', rfl⟩ |
            ⟨h', τ', prior', joint', legal', reached', realized', rfl⟩
        · rfl
        · exact absurd (congrArg (fun s : S.State => s.transcript.length) same)
            (by simp [initHistory, waitExtend_state])
        · exact absurd (congrArg (fun s : S.State => s.source.trace.length) same)
            (by simp [initHistory, readyExtend_state, History.extend, Trace.length])
      · rw [S.waitExtend_length] at length
        omega
      · rw [S.readyExtend_length] at length
        omega
  | succ n ih =>
      intro x y length same
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · simp [initHistory, Trace.length] at length
      · rcases S.history_cases y with rfl | ⟨h', τ', p', prior', running', token', drawn', rfl⟩ |
            ⟨h', τ', prior', joint', legal', reached', realized', rfl⟩
        · exact absurd (congrArg (fun s : S.State => s.transcript.length) same)
            (by simp [initHistory, waitExtend_state])
        · rw [S.waitExtend_state, S.waitExtend_state, State.mk.injEq] at same
          obtain ⟨rfl, append, rfl⟩ := same
          obtain ⟨rfl, single⟩ := List.append_inj' append rfl
          obtain rfl := List.singleton_inj.mp single
          have priors := ih ⟨⟨h, τ, p + 1⟩, prior⟩ ⟨⟨h, τ, p + 1⟩, prior'⟩
            (by rw [S.waitExtend_length] at length; change prior.length = n; omega) rfl
          cases priors
          rfl
        · obtain ⟨bound, _⟩ := S.invariant prior
          rw [S.waitExtend_state, S.readyExtend_state, State.mk.injEq] at same
          dsimp only at bound
          omega
      · rcases S.history_cases y with rfl | ⟨h', τ', p', prior', running', token', drawn', rfl⟩ |
            ⟨h', τ', prior', joint', legal', reached', realized', rfl⟩
        · exact absurd (congrArg (fun s : S.State => s.source.trace.length) same)
            (by simp [initHistory, readyExtend_state, History.extend, Trace.length])
        · obtain ⟨bound, _⟩ := S.invariant prior'
          rw [S.readyExtend_state, S.waitExtend_state, State.mk.injEq] at same
          dsimp only at bound
          omega
        · rw [S.readyExtend_state, S.readyExtend_state, State.mk.injEq] at same
          obtain ⟨extended, rfl, -⟩ := same
          obtain ⟨hs, htr⟩ := h
          obtain ⟨hs', htr'⟩ := h'
          obtain ⟨rfl, extended'⟩ := History.mk.inj extended
          cases extended'
          have priors := ih ⟨⟨⟨hs, htr⟩, τ, 0⟩, prior⟩ ⟨⟨⟨hs, htr⟩, τ, 0⟩, prior'⟩
            (by rw [S.readyExtend_length] at length; change prior.length = n; omega) rfl
          cases priors
          rfl

/-! ## Lifting source policies -/

/-- A source choice as an expanded choice at a ready information value. -/
def liftChoice (i : ι) (info : M.InfoState i) (τ : List Token) (choice : M.Choice i info) :
    (S.model M).Choice i (info, τ, 0) :=
  ⟨choice.1, choice.2⟩

/-- An expanded choice at a ready information value as a source choice. -/
def unliftChoice (i : ι) (info : M.InfoState i) (τ : List Token)
    (choice : (S.model M).Choice i (info, τ, 0)) : M.Choice i info :=
  ⟨choice.1, choice.2⟩

@[simp] theorem liftChoice_val (i : ι) (info : M.InfoState i) (τ : List Token)
    (choice : M.Choice i info) : (S.liftChoice M i info τ choice).1 = choice.1 :=
  rfl

@[simp] theorem liftChoice_unliftChoice (i : ι) (info : M.InfoState i) (τ : List Token)
    (choice : (S.model M).Choice i (info, τ, 0)) :
    S.liftChoice M i info τ (S.unliftChoice M i info τ choice) = choice :=
  rfl

@[simp] theorem unliftChoice_liftChoice (i : ι) (info : M.InfoState i) (τ : List Token)
    (choice : M.Choice i info) :
    S.unliftChoice M i info τ (S.liftChoice M i info τ choice) = choice :=
  rfl

theorem liftChoice_injective (i : ι) (info : M.InfoState i) (τ : List Token) :
    Function.Injective (S.liftChoice M i info τ) :=
  fun _ _ same => Subtype.ext (congrArg Subtype.val same)

/-- The silent choice while a draw is pending. -/
def idle (i : ι) (info : M.InfoState i) (τ : List Token) (p : ℕ) :
    (S.model M).Choice i (info, τ, p + 1) :=
  ⟨none, rfl⟩

/-- The lift of a source policy: the source law at every ready information
value, silence while a draw is pending. -/
def liftPolicy (i : ι) (policy : M.BehavioralPolicy i) : (S.model M).BehavioralPolicy i
  | (info, τ, 0) => (policy info).map (S.liftChoice M i info τ)
  | (info, τ, p + 1) => PMF.pure (S.idle M i info τ p)

@[simp] theorem liftPolicy_ready (i : ι) (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (τ : List Token) :
    S.liftPolicy M i policy (info, τ, 0) = (policy info).map (S.liftChoice M i info τ) :=
  rfl

@[simp] theorem liftPolicy_waiting (i : ι) (policy : M.BehavioralPolicy i)
    (info : M.InfoState i) (τ : List Token) (p : ℕ) :
    S.liftPolicy M i policy (info, τ, p + 1) = PMF.pure (S.idle M i info τ p) :=
  rfl

/-- The lift of a source profile. -/
def liftProfile (profile : ∀ i, M.BehavioralPolicy i) : ∀ i, (S.model M).BehavioralPolicy i :=
  fun i => S.liftPolicy M i (profile i)

/-- The lifted law at a ready value, forgetting legality, is the source law. -/
theorem liftPolicy_map_val (i : ι) (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (τ : List Token) :
    (S.liftPolicy M i policy (info, τ, 0)).map Subtype.val = (policy info).map Subtype.val := by
  rw [liftPolicy_ready, PMF.map_comp]
  rfl

/-! ## The public transcript and the scheduler likelihood -/

/-- The public projections of a source history and all its prefixes, most
recent first. -/
def pubTrace : ∀ {s : E.State}, E.Trace s → List Pub
  | _, .start => [S.pub E.initHistory]
  | _, .extend prior joint legal realized =>
      S.pub ⟨_, .extend prior joint legal realized⟩ :: pubTrace prior

theorem pubTrace_length : ∀ {s : E.State} (trace : E.Trace s),
    (S.pubTrace trace).length = trace.length + 1
  | _, .start => rfl
  | _, .extend prior _ _ _ => by
      simp only [pubTrace, List.length_cons, Trace.length, pubTrace_length prior]

/-- The head of the public transcript is the projection of the history. -/
theorem pubTrace_head : ∀ (h : E.History), (S.pubTrace h.trace).head? = some (S.pub h)
  | ⟨_, .start⟩ => rfl
  | ⟨_, .extend _ _ _ _⟩ => rfl

/-- Equal public transcripts give equal projections of the histories. -/
theorem pub_eq_of_pubTrace_eq {h h' : E.History}
    (same : S.pubTrace h.trace = S.pubTrace h'.trace) : S.pub h = S.pub h' := by
  have := (S.pubTrace_head h).symm.trans ((congrArg List.head? same).trans (S.pubTrace_head h'))
  exact Option.some.inj this

/-- The product of the kernel probabilities of the draws along an expanded
history: one factor per wait, none per source transition. -/
def likelihood : ∀ {s : S.State}, S.protocol.Trace s → ℝ≥0∞
  | _, .start => 1
  | _, .extend (source := before) (target := after) prior joint legal _ =>
      likelihood prior * match before.pending with
        | 0 => 1
        | _ + 1 => (S.protocol.step before ⟨joint, legal⟩) after

/-- The state reached by a draw determines the token drawn. -/
theorem waitTarget_injective (h : E.History) (τ : List Token) (p : ℕ) :
    Function.Injective fun token : Token => (⟨h, τ ++ [token], p⟩ : S.State) := by
  intro first second same
  have := (State.mk.inj same).2.1
  exact List.singleton_inj.mp (List.append_cancel_left this)

/-- The probability of a draw is its kernel probability. -/
theorem step_waiting_apply (h : E.History) (τ : List Token) (p : ℕ)
    (joint : { joint : ∀ i, Option (E.Action i) // S.protocol.Legal ⟨h, τ, p + 1⟩ joint })
    (token : Token) :
    (S.protocol.step ⟨h, τ, p + 1⟩ joint) ⟨h, τ ++ [token], p⟩ =
      S.kernel (S.pub h) τ (p + 1) token := by
  change ((S.kernel (S.pub h) τ (p + 1)).map _) _ = _
  exact pmf_map_apply_of_injective _ (S.waitTarget_injective h τ p) token

/-- The probability of a source transition is its source probability. -/
theorem step_ready_apply (h : E.History) (τ : List Token)
    (joint : { joint : ∀ i, Option (E.Action i) // S.protocol.Legal ⟨h, τ, 0⟩ joint })
    {reached : E.State} (realized : reached ∈ (E.step h.state ⟨joint.1, joint.2⟩).support) :
    (S.protocol.step ⟨h, τ, 0⟩ joint) ⟨h.extend joint.2 realized, τ, S.draws⟩ =
      (E.step h.state ⟨joint.1, joint.2⟩) reached := by
  obtain ⟨joint, legal⟩ := joint
  change ((E.step h.state ⟨joint, legal⟩).bindOnSupport fun _ realized =>
    PMF.pure (⟨h.extend legal realized, τ, S.draws⟩ : S.State)) _ = _
  exact bindOnSupport_pure_apply_of_injective (E.step h.state ⟨joint, legal⟩)
    (fun _ realized => ⟨h.extend legal realized, τ, S.draws⟩)
    (fun _ _ _ _ same => congrArg (fun s : S.State => s.source.state) same) reached realized

theorem likelihood_waitExtend {h : E.History} {τ : List Token} {p : ℕ}
    (prior : S.protocol.Trace ⟨h, τ, p + 1⟩) (running : ¬ E.terminal h.state) (token : Token)
    (drawn : token ∈ (S.kernel (S.pub h) τ (p + 1)).support) :
    S.likelihood (S.waitExtend prior running token drawn).trace =
      S.likelihood prior * S.kernel (S.pub h) τ (p + 1) token := by
  change S.likelihood prior * (S.protocol.step ⟨h, τ, p + 1⟩ _) ⟨h, τ ++ [token], p⟩ = _
  rw [S.step_waiting_apply]

theorem likelihood_readyExtend {h : E.History} {τ : List Token}
    (prior : S.protocol.Trace ⟨h, τ, 0⟩) {joint : ∀ i, Option (E.Action i)}
    (legal : E.Legal h.state joint) {reached : E.State}
    (realized : reached ∈ (E.step h.state ⟨joint, legal⟩).support) :
    S.likelihood (S.readyExtend prior legal realized).trace = S.likelihood prior := by
  change S.likelihood prior * 1 = _
  rw [mul_one]

theorem likelihood_pos : ∀ {s : S.State} (trace : S.protocol.Trace s), 0 < S.likelihood trace
  | _, .start => zero_lt_one
  | _, .extend (source := before) prior joint legal realized => by
      have ih := likelihood_pos prior
      obtain ⟨h, τ, p⟩ := before
      cases p with
      | zero =>
          change 0 < S.likelihood prior * 1
          rw [mul_one]
          exact ih
      | succ p =>
          change 0 < S.likelihood prior * (S.protocol.step ⟨h, τ, p + 1⟩ ⟨joint, legal⟩) _
          exact ENNReal.mul_pos ih.ne' ((PMF.apply_pos_iff _ _).mpr realized).ne'

theorem likelihood_le_one : ∀ {s : S.State} (trace : S.protocol.Trace s),
    S.likelihood trace ≤ 1
  | _, .start => le_rfl
  | _, .extend (source := before) prior joint legal realized => by
      have ih := likelihood_le_one prior
      obtain ⟨h, τ, p⟩ := before
      cases p with
      | zero =>
          change S.likelihood prior * 1 ≤ 1
          rw [mul_one]
          exact ih
      | succ p =>
          change S.likelihood prior * (S.protocol.step ⟨h, τ, p + 1⟩ ⟨joint, legal⟩) _ ≤ 1
          exact mul_le_one' ih (PMF.coe_le_one _ _)

/-! ## Constancy of the likelihood on information fibers -/

/-- Two expanded histories with the same transcript and pending count whose
source histories have the same public transcript have the same likelihood. -/
theorem likelihood_congr : ∀ (n : ℕ) (x y : S.protocol.History), x.trace.length = n →
    S.pubTrace (S.erase x).trace = S.pubTrace (S.erase y).trace →
    x.state.transcript = y.state.transcript → x.state.pending = y.state.pending →
    S.likelihood x.trace = S.likelihood y.trace := by
  intro n
  induction n with
  | zero =>
      intro x y length pubs transcripts _
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · rcases S.history_cases y with rfl | ⟨h', τ', p', prior', running', token', drawn', rfl⟩ |
            ⟨h', τ', prior', joint', legal', reached', realized', rfl⟩
        · rfl
        · exact absurd (congrArg List.length transcripts) (by simp [initHistory, waitExtend_state])
        · have := congrArg List.length pubs
          rw [S.pubTrace_length, S.pubTrace_length] at this
          change E.initHistory.trace.length + 1 =
            (h'.extend legal' realized').trace.length + 1 at this
          simp only [initHistory, History.extend, Trace.length] at this
          omega
      · rw [S.waitExtend_length] at length
        omega
      · rw [S.readyExtend_length] at length
        omega
  | succ n ih =>
      intro x y length pubs transcripts pendings
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · simp [initHistory, Trace.length] at length
      · rcases S.history_cases y with rfl | ⟨h', τ', p', prior', running', token', drawn', rfl⟩ |
            ⟨h', τ', prior', joint', legal', reached', realized', rfl⟩
        · exact absurd (congrArg List.length transcripts) (by simp [initHistory, waitExtend_state])
        · rw [S.waitExtend_state, S.waitExtend_state] at transcripts pendings
          dsimp only at transcripts pendings
          obtain ⟨rfl, single⟩ := List.append_inj' transcripts rfl
          obtain rfl := List.singleton_inj.mp single
          subst pendings
          have priorLength : prior.length = n := by
            rw [S.waitExtend_length] at length
            omega
          have pubEq : S.pub h = S.pub h' := S.pub_eq_of_pubTrace_eq pubs
          rw [S.likelihood_waitExtend, S.likelihood_waitExtend, pubEq]
          exact congrArg (fun weight => weight * S.kernel (S.pub h') τ (p + 1) token)
            (ih ⟨⟨h, τ, p + 1⟩, prior⟩ ⟨⟨h', τ, p + 1⟩, prior'⟩ priorLength pubs rfl rfl)
        · obtain ⟨bound, _⟩ := S.invariant prior
          rw [S.waitExtend_state, S.readyExtend_state] at pendings
          dsimp only at bound pendings
          omega
      · rcases S.history_cases y with rfl | ⟨h', τ', p', prior', running', token', drawn', rfl⟩ |
            ⟨h', τ', prior', joint', legal', reached', realized', rfl⟩
        · have := congrArg List.length pubs
          rw [S.pubTrace_length, S.pubTrace_length] at this
          change (h.extend legal realized).trace.length + 1 =
            E.initHistory.trace.length + 1 at this
          simp only [initHistory, History.extend, Trace.length] at this
          omega
        · obtain ⟨bound, _⟩ := S.invariant prior'
          rw [S.readyExtend_state, S.waitExtend_state] at pendings
          dsimp only at bound pendings
          omega
        · rw [S.readyExtend_state, S.readyExtend_state] at transcripts
          dsimp only at transcripts
          subst transcripts
          have priorLength : prior.length = n := by
            rw [S.readyExtend_length] at length
            omega
          have tails : S.pubTrace h.trace = S.pubTrace h'.trace := by
            change S.pubTrace (h.extend legal realized).trace =
              S.pubTrace (h'.extend legal' realized').trace at pubs
            exact List.tail_eq_of_cons_eq pubs
          rw [S.likelihood_readyExtend, S.likelihood_readyExtend]
          exact ih ⟨⟨h, τ, 0⟩, prior⟩ ⟨⟨h', τ, 0⟩, prior'⟩ priorLength tails rfl rfl

/-! ## Replaying a transcript over another source history -/

/-- A source history with a one-element public transcript is initial. -/
private theorem eq_initHistory_of_pubTrace_singleton (h : E.History)
    (single : S.pubTrace h.trace = [S.pub E.initHistory]) : h = E.initHistory := by
  obtain ⟨s, trace⟩ := h
  cases trace with
  | start => rfl
  | extend prior joint legal realized =>
      have := congrArg List.length single
      simp only [pubTrace, List.length_cons, List.length_nil, S.pubTrace_length] at this
      omega

/-- Every transcript of an expanded history can be replayed over any
nonterminal source history with the same public transcript. -/
theorem exists_replay : ∀ (n : ℕ) (x : S.protocol.History), x.trace.length = n →
    ∀ h' : E.History, ¬ E.terminal h'.state →
      S.pubTrace h'.trace = S.pubTrace (S.erase x).trace →
      ∃ y : S.protocol.History, y.state = ⟨h', x.state.transcript, x.state.pending⟩ := by
  intro n
  induction n with
  | zero =>
      intro x length h' _ pubs
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · obtain rfl := S.eq_initHistory_of_pubTrace_singleton h' pubs
        exact ⟨S.protocol.initHistory, rfl⟩
      · rw [S.waitExtend_length] at length
        omega
      · rw [S.readyExtend_length] at length
        omega
  | succ n ih =>
      intro x length h' running' pubs
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · simp [initHistory, Trace.length] at length
      · have priorLength : prior.length = n := by
          rw [S.waitExtend_length] at length
          omega
        obtain ⟨⟨s, trace⟩, same⟩ := ih ⟨⟨h, τ, p + 1⟩, prior⟩ priorLength h' running' pubs
        dsimp only at same
        subst same
        have pubEq : S.pub h' = S.pub h := S.pub_eq_of_pubTrace_eq pubs
        have drawn' : token ∈ (S.kernel (S.pub h') τ (p + 1)).support := by
          rwa [pubEq]
        exact ⟨S.waitExtend trace running' token drawn', rfl⟩
      · obtain ⟨s', trace'⟩ := h'
        cases trace' with
        | start =>
            have := congrArg List.length pubs
            rw [S.pubTrace_length, S.pubTrace_length] at this
            change Trace.length (Trace.start : E.Trace E.init) + 1 =
              (h.extend legal realized).trace.length + 1 at this
            simp only [History.extend, Trace.length] at this
            omega
        | extend prior' joint' legal' realized' =>
            have priorLength : prior.length = n := by
              rw [S.readyExtend_length] at length
              omega
            have tails : S.pubTrace prior' = S.pubTrace h.trace := by
              change S.pubTrace (Trace.extend prior' joint' legal' realized') =
                S.pubTrace (h.extend legal realized).trace at pubs
              exact List.tail_eq_of_cons_eq pubs
            obtain ⟨⟨s, trace⟩, same⟩ := ih ⟨⟨h, τ, 0⟩, prior⟩ priorLength ⟨_, prior'⟩ legal'.1
              tails
            dsimp only at same
            subst same
            exact ⟨S.readyExtend trace legal' realized', rfl⟩

/-! ## Sites of the expansion -/

/-- No draw is pending at a decision site of the expansion. -/
theorem pending_eq_zero (who : ι) (site : (S.model M).InformationSite who) :
    site.1.2.2 = 0 := by
  obtain ⟨⟨info, τ, p⟩, _, _, action, mem⟩ := site
  cases p with
  | zero => rfl
  | succ p => exact absurd (Set.mem_singleton_iff.mp mem) (by simp)

/-- The source information value of a history in a decision fiber of the
expansion is the first component of the site. -/
theorem erase_mem (who : ι) (site : (S.model M).InformationSite who)
    (x : (S.model M).InformationHistory who site.1) :
    M.infoOf who (S.erase x.1).trace = site.1.1 := by
  have := x.2
  rw [show (S.model M).infoOf who x.1.trace = (S.signals M).infoOf who x.1.trace from rfl,
    S.infoOf_eq] at this
  exact congrArg Prod.fst this

theorem transcript_mem (who : ι) (site : (S.model M).InformationSite who)
    (x : (S.model M).InformationHistory who site.1) :
    x.1.state.transcript = site.1.2.1 := by
  have := x.2
  rw [show (S.model M).infoOf who x.1.trace = (S.signals M).infoOf who x.1.trace from rfl,
    S.infoOf_eq] at this
  exact congrArg (fun info => info.2.1) this

theorem pending_mem (who : ι) (site : (S.model M).InformationSite who)
    (x : (S.model M).InformationHistory who site.1) :
    x.1.state.pending = site.1.2.2 := by
  have := x.2
  rw [show (S.model M).infoOf who x.1.trace = (S.signals M).infoOf who x.1.trace from rfl,
    S.infoOf_eq] at this
  exact congrArg (fun info => info.2.2) this

/-- The source decision site underlying a decision site of the expansion. -/
def sourceSite (who : ι) (site : (S.model M).InformationSite who) : M.InformationSite who :=
  ⟨site.1.1, by
    obtain ⟨⟨info, τ, p⟩, x, running, action, mem⟩ := site
    cases p with
    | zero =>
        exact ⟨⟨S.erase x.1, S.erase_mem M who ⟨(info, τ, 0), x, running, action, mem⟩ x⟩,
          running, action, mem⟩
    | succ p => exact absurd (Set.mem_singleton_iff.mp mem) (by simp)⟩

@[simp] theorem sourceSite_val (who : ι) (site : (S.model M).InformationSite who) :
    (S.sourceSite M who site).1 = site.1.1 :=
  rfl

/-- The source history of a fiber history lies in the source fiber. -/
def eraseHistory (who : ι) (site : (S.model M).InformationSite who)
    (x : (S.model M).InformationHistory who site.1) :
    M.InformationHistory who (S.sourceSite M who site).1 :=
  ⟨S.erase x.1, S.erase_mem M who site x⟩

/-- The lift of a fully mixed source profile is fully mixed. -/
theorem liftProfile_fullSupport (profile : ∀ i, M.BehavioralPolicy i)
    (full : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (profile i site.1).support) :
    ∀ i (site : (S.model M).InformationSite i) (choice : (S.model M).Choice i site.1),
      choice ∈ (S.liftProfile M profile i site.1).support := by
  intro i site choice
  obtain ⟨⟨info, τ, p⟩, witness⟩ := site
  cases p with
  | zero =>
      change choice ∈ ((profile i info).map (S.liftChoice M i info τ)).support
      rw [PMF.mem_support_map_iff]
      exact ⟨S.unliftChoice M i info τ choice,
        full i (S.sourceSite M i ⟨(info, τ, 0), witness⟩) _, rfl⟩
  | succ p =>
      obtain ⟨_, _, action, mem⟩ := witness
      exact absurd (Set.mem_singleton_iff.mp mem) (by simp)

/-! ## Decision recall of the expansion -/

/-- The expanded own-play record read off a source history and a transcript:
each own source move, stamped with the transcript at its stage. -/
def stampedOwnPlay (i : ι) (τ : List Token) :
    ∀ {s : E.State}, E.Trace s → List ((S.model M).InfoState i × E.Action i)
  | _, .start => []
  | _, .extend prior joint _ _ =>
      match joint i with
      | some action =>
          ((M.infoOf i prior, τ.take (S.draws * (prior.length + 1)), 0), action) ::
            stampedOwnPlay i τ prior
      | none => stampedOwnPlay i τ prior

/-- Appending a token after every stage read so far changes no stamp. -/
theorem stampedOwnPlay_append (i : ι) (τ : List Token) (token : Token) :
    ∀ {s : E.State} (trace : E.Trace s), S.draws * trace.length ≤ τ.length →
      S.stampedOwnPlay M i (τ ++ [token]) trace = S.stampedOwnPlay M i τ trace
  | _, .start, _ => rfl
  | _, .extend prior joint legal realized, bound => by
      have shorter : S.draws * prior.length ≤ τ.length := by
        simp only [Trace.length] at bound
        nlinarith
      have ih := stampedOwnPlay_append i τ token prior shorter
      rcases choice : joint i with _ | action
      · simp only [stampedOwnPlay, choice, ih]
      · simp only [stampedOwnPlay, choice, ih]
        rw [List.take_append_of_le_length]
        simpa only [Trace.length] using bound

/-- The own-play record of an expanded history is the stamped source record. -/
theorem ownPlay_lift (i : ι) : ∀ {s : S.State} (trace : S.protocol.Trace s),
    (S.model M).ownPlay i trace = S.stampedOwnPlay M i s.transcript s.source.trace
  | _, .start => rfl
  | _, .extend (source := before) prior joint legal realized => by
      have ih := ownPlay_lift i prior
      obtain ⟨h, τ, p⟩ := before
      have count := (S.invariant prior).2
      have bound := (S.invariant prior).1
      dsimp only at count bound ih
      cases p with
      | zero =>
          obtain ⟨reached, realized', rfl⟩ := (S.mem_step_ready h τ ⟨joint, legal⟩ _).mp realized
          have info : (S.model M).infoOf i prior = (M.infoOf i h.trace, τ, 0) :=
            S.infoOf_eq M i prior
          dsimp only [History.extend]
          rw [InfoSignals.ownPlay_extend]
          rcases choice : joint i with _ | action
          · simp only [stampedOwnPlay, choice, ih]
          · simp only [stampedOwnPlay, choice, ih, info]
            rw [List.take_of_length_le]
            omega
      | succ p =>
          obtain ⟨token, _, rfl⟩ := (S.mem_step_waiting h τ p ⟨joint, legal⟩ _).mp realized
          obtain rfl := S.eq_noop_of_legal_waiting h τ p legal
          dsimp only
          rw [InfoSignals.ownPlay_extend]
          change (S.model M).ownPlay i prior = _
          rw [ih, S.stampedOwnPlay_append]
          nlinarith

/-- Source histories with the same own play and the same public transcript
have the same stamped records: the public projection fixes who is active at
every stage, so the stamps fall at the same stages. -/
theorem stampedOwnPlay_congr
    (actors : ∀ i (h h' : E.History), S.pub h = S.pub h' →
      (E.active h.state i ↔ E.active h'.state i))
    (i : ι) (τ : List Token) :
    ∀ {s : E.State} (trace : E.Trace s) {s' : E.State} (trace' : E.Trace s'),
      M.ownPlay i trace = M.ownPlay i trace' → S.pubTrace trace = S.pubTrace trace' →
      S.stampedOwnPlay M i τ trace = S.stampedOwnPlay M i τ trace'
  | _, .start, _, .start, _, _ => rfl
  | _, .start, _, .extend prior' _ _ _, _, pubs => by
      have := congrArg List.length pubs
      simp only [pubTrace, List.length_cons, List.length_nil, S.pubTrace_length] at this
      omega
  | _, .extend prior _ _ _, _, .start, _, pubs => by
      have := congrArg List.length pubs
      simp only [pubTrace, List.length_cons, List.length_nil, S.pubTrace_length] at this
      omega
  | _, .extend (source := before) prior joint legal realized, _,
      .extend (source := before') prior' joint' legal' realized', own, pubs => by
      have tails : S.pubTrace prior = S.pubTrace prior' := List.tail_eq_of_cons_eq pubs
      have lengths : prior.length = prior'.length := by
        have := congrArg List.length tails
        rwa [S.pubTrace_length, S.pubTrace_length, Nat.add_right_cancel_iff] at this
      have activity : E.active before i ↔ E.active before' i :=
        actors i ⟨before, prior⟩ ⟨before', prior'⟩
          (S.pub_eq_of_pubTrace_eq (h := ⟨before, prior⟩) (h' := ⟨before', prior'⟩) tails)
      have legalOption := E.legalOption_of_legal legal i
      have legalOption' := E.legalOption_of_legal legal' i
      rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend] at own
      rcases choice : joint i with _ | action <;> rcases choice' : joint' i with _ | action' <;>
        rw [choice] at legalOption own <;> rw [choice'] at legalOption' own <;>
        simp only [LegalOption] at legalOption legalOption'
      · simp only [stampedOwnPlay, choice, choice']
        exact stampedOwnPlay_congr actors i τ prior prior' own tails
      · exact absurd (activity.mpr legalOption'.1) legalOption
      · exact absurd (activity.mp legalOption.1) legalOption'
      · simp only [List.cons.injEq, Prod.mk.injEq] at own
        obtain ⟨⟨infos, rfl⟩, rest⟩ := own
        simp only [stampedOwnPlay, choice, choice', infos, lengths, List.cons.injEq, true_and]
        exact stampedOwnPlay_congr actors i τ prior prior' rest tails

/-- **Decision recall of the expansion.** Source decision recall, with the
public transcript and the actors recoverable from every player's
information, gives decision recall of the expanded model. -/
theorem decisionRecall (recall : M.DecisionRecall)
    (recoverable : ∀ i (site : M.InformationSite i)
      (h h' : M.InformationHistory i site.1), S.pubTrace h.1.trace = S.pubTrace h'.1.trace)
    (actors : ∀ i (h h' : E.History), S.pub h = S.pub h' →
      (E.active h.state i ↔ E.active h'.state i)) :
    (S.model M).DecisionRecall := by
  intro who site first second
  rw [S.ownPlay_lift M who first.1.trace, S.ownPlay_lift M who second.1.trace,
    S.transcript_mem M who site first, S.transcript_mem M who site second]
  exact S.stampedOwnPlay_congr M actors who _ first.1.state.source.trace
    second.1.state.source.trace
    (recall who (S.sourceSite M who site) (S.eraseHistory M who site first)
      (S.eraseHistory M who site second))
    (recoverable who (S.sourceSite M who site) (S.eraseHistory M who site first)
      (S.eraseHistory M who site second))

/-! ## Erasing reachability -/

/-- Reachability in the expansion erases to reachability in the source. -/
theorem erase_reaches {x y : S.protocol.History} (reach : S.protocol.HistoryReaches x y) :
    E.HistoryReaches (S.erase x) (S.erase y) := by
  obtain ⟨fuel, reach⟩ := reach
  induction reach with
  | refl => exact ⟨0, .refl 0 _⟩
  | @step fuel x y joint legal reached realized rest ih =>
      obtain ⟨⟨h, τ, p⟩, trace⟩ := x
      cases p with
      | zero =>
          obtain ⟨reached', realized', rfl⟩ := (S.mem_step_ready h τ ⟨joint, legal⟩ _).mp realized
          obtain ⟨fuel', rest'⟩ := ih
          exact ⟨fuel' + 1, .step joint legal realized' rest'⟩
      | succ p =>
          obtain ⟨token, _, rfl⟩ := (S.mem_step_waiting h τ p ⟨joint, legal⟩ _).mp realized
          exact ih

/-- A history reached from a ready history by at least one transition erases
to a history reached from the source history after a source transition. -/
theorem erase_reaches_extend {x y : S.protocol.History} (ready : x.state.pending = 0)
    (reach : S.protocol.HistoryReaches x y) (different : y ≠ x) :
    ∃ (joint : ∀ i, Option (E.Action i)) (legal : E.Legal (S.erase x).state joint)
      (reached : E.State) (realized : reached ∈ (E.step (S.erase x).state ⟨joint, legal⟩).support),
      E.HistoryReaches ((S.erase x).extend legal realized) (S.erase y) := by
  obtain ⟨fuel, reach⟩ := reach
  cases reach with
  | refl => exact absurd rfl different
  | @step fuel x y joint legal reached realized rest =>
      obtain ⟨⟨h, τ, p⟩, trace⟩ := x
      cases p with
      | zero =>
          obtain ⟨reached', realized', rfl⟩ := (S.mem_step_ready h τ ⟨joint, legal⟩ _).mp realized
          exact ⟨joint, legal, reached', realized', S.erase_reaches ⟨fuel, rest⟩⟩
      | succ p => exact absurd ready (by simp)

/-! ## One-step masses and the reach-weight factorization -/

variable [Fintype ι]

/-- The last joint action of a history, if any. -/
private def lastJoint {E' : ExecutionProtocol ι} : E'.History → Option (∀ i, Option (E'.Action i))
  | ⟨_, .start⟩ => none
  | ⟨_, .extend _ joint _ _⟩ => some joint

/-- The mass of one realized extension in the one-step behavioral law is the
joint-action mass times the transition mass. -/
private theorem runBehavioralFrom_one_apply {E' : ExecutionProtocol ι} (M' : InformationModel E')
    (policies : ∀ i, M'.BehavioralPolicy i) (history : E'.History)
    (hterm : ¬ E'.terminal history.state)
    (joint : { joint : ∀ i, Option (E'.Action i) // E'.Legal history.state joint })
    {target : E'.State} (realized : target ∈ (E'.step history.state joint).support) :
    (M'.runBehavioralFrom policies 1 history) (history.extend joint.2 realized) =
      (M'.behavioralJoint policies history.trace hterm) joint *
        (E'.step history.state joint) target := by
  classical
  rw [show (1 : ℕ) = 0 + 1 from rfl, M'.runBehavioralFrom_succ_of_not_terminal policies 0 hterm,
    PMF.bind_apply]
  have inner (draw : { joint : ∀ i, Option (E'.Action i) // E'.Legal history.state joint }) :
      ((E'.step history.state draw).bindOnSupport fun _ realized' =>
          M'.runBehavioralFrom policies 0 (history.extend draw.2 realized'))
        (history.extend joint.2 realized) =
      if draw = joint then (E'.step history.state joint) target else 0 := by
    have pure : (fun (reached : E'.State) (realized' : reached ∈
        (E'.step history.state draw).support) =>
          M'.runBehavioralFrom policies 0 (history.extend draw.2 realized')) =
        fun reached realized' => PMF.pure (history.extend draw.2 realized') := by
      funext reached realized'
      rfl
    rw [pure]
    split_ifs with same
    · subst same
      exact bindOnSupport_pure_apply_of_injective (E'.step history.state draw)
        (fun _ realized' => history.extend draw.2 realized')
        (fun _ _ _ _ same => congrArg History.state same) target realized
    · rw [PMF.bindOnSupport_apply, ENNReal.tsum_eq_zero]
      intro reached
      split_ifs with zero
      · exact mul_zero _
      · rw [PMF.pure_apply_of_ne, mul_zero]
        intro collision
        apply same
        apply Subtype.ext
        exact (Option.some.inj (congrArg lastJoint collision)).symm
  simp_rw [inner, mul_ite, mul_zero]
  exact tsum_ite_eq joint _

/-- A joint-action mass, as the product of the players' local masses on the
bare options. -/
private theorem behavioralJoint_apply_eq_prod {E' : ExecutionProtocol ι}
    (M' : InformationModel E') (policies : ∀ i, M'.BehavioralPolicy i) {state : E'.State}
    (trace : E'.Trace state) (hterm : ¬ E'.terminal state)
    (joint : { joint : ∀ i, Option (E'.Action i) // E'.Legal state joint }) :
    (M'.behavioralJoint policies trace hterm) joint =
      ∏ i, ((policies i (M'.infoOf i trace)).map Subtype.val) (joint.1 i) := by
  rw [← pmf_map_apply_of_injective (M'.behavioralJoint policies trace hterm)
    Subtype.val_injective joint, M'.behavioralJoint_map_val, independentProduct_apply]

/-- The lifted joint law at a ready history has the source joint masses. -/
theorem behavioralJoint_lift_apply (profile : ∀ i, M.BehavioralPolicy i) {h : E.History}
    {τ : List Token} (trace : S.protocol.Trace ⟨h, τ, 0⟩) (hterm : ¬ E.terminal h.state)
    (joint : ∀ i, Option (E.Action i)) (legal : E.Legal h.state joint) :
    ((S.model M).behavioralJoint (S.liftProfile M profile) trace hterm) ⟨joint, legal⟩ =
      (M.behavioralJoint profile h.trace hterm) ⟨joint, legal⟩ := by
  rw [behavioralJoint_apply_eq_prod, behavioralJoint_apply_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  have info : (S.model M).infoOf i trace = (M.infoOf i h.trace, τ, 0) := S.infoOf_eq M i trace
  change ((S.liftPolicy M i (profile i) ((S.model M).infoOf i trace)).map Subtype.val) _ = _
  rw [info, S.liftPolicy_map_val]

/-- The lifted joint law while a draw is pending is the no-op. -/
theorem behavioralJoint_lift_waiting (profile : ∀ i, M.BehavioralPolicy i) {h : E.History}
    {τ : List Token} {p : ℕ} (trace : S.protocol.Trace ⟨h, τ, p + 1⟩)
    (hterm : ¬ E.terminal h.state) :
    (S.model M).behavioralJoint (S.liftProfile M profile) trace hterm =
      PMF.pure ⟨S.protocol.noop, S.protocol.noop_isLegal hterm fun _ => id⟩ :=
  (S.model M).behavioralJoint_eq_pure_of_no_active _ trace hterm fun _ => id

/-- **Reach weights factor.** The reach weight of an expanded history under a
lifted profile is the source reach weight of its source history times the
scheduler likelihood of its transcript. -/
theorem historyReachWeight_lift (profile : ∀ i, M.BehavioralPolicy i) :
    ∀ (n : ℕ) (x : S.protocol.History), x.trace.length = n →
      (S.model M).historyReachWeight (S.liftProfile M profile) x =
        M.historyReachWeight profile (S.erase x) * S.likelihood x.trace := by
  intro n
  induction n with
  | zero =>
      intro x length
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · rw [InformationModel.historyReachWeight_initHistory]
        change 1 = M.historyReachWeight profile E.initHistory * 1
        rw [InformationModel.historyReachWeight_initHistory, mul_one]
      · rw [S.waitExtend_length] at length
        omega
      · rw [S.readyExtend_length] at length
        omega
  | succ n ih =>
      intro x length
      rcases S.history_cases x with rfl | ⟨h, τ, p, prior, running, token, drawn, rfl⟩ |
          ⟨h, τ, prior, joint, legal, reached, realized, rfl⟩
      · simp [initHistory, Trace.length] at length
      · have positive : 0 < (S.waitExtend prior running token drawn).trace.length := by
          rw [S.waitExtend_length]
          omega
        rw [(S.model M).historyReachWeight_eq_prior_mul _ _ positive]
        change (S.model M).historyReachWeight (S.liftProfile M profile) ⟨⟨h, τ, p + 1⟩, prior⟩ *
          (S.model M).runBehavioralFrom (S.liftProfile M profile) 1 ⟨⟨h, τ, p + 1⟩, prior⟩
            (S.waitExtend prior running token drawn) = _
        have priorLength : prior.length = n := by
          rw [S.waitExtend_length] at length
          omega
        rw [ih ⟨⟨h, τ, p + 1⟩, prior⟩ priorLength, S.likelihood_waitExtend]
        unfold waitExtend
        rw [runBehavioralFrom_one_apply (S.model M) (S.liftProfile M profile)
          ⟨⟨h, τ, p + 1⟩, prior⟩ running, S.step_waiting_apply,
          S.behavioralJoint_lift_waiting M profile prior running, PMF.pure_apply_self, one_mul,
          mul_assoc]
        rfl
      · have positive : 0 < (S.readyExtend prior legal realized).trace.length := by
          rw [S.readyExtend_length]
          omega
        rw [(S.model M).historyReachWeight_eq_prior_mul _ _ positive]
        change (S.model M).historyReachWeight (S.liftProfile M profile) ⟨⟨h, τ, 0⟩, prior⟩ *
          (S.model M).runBehavioralFrom (S.liftProfile M profile) 1 ⟨⟨h, τ, 0⟩, prior⟩
            (S.readyExtend prior legal realized) = _
        have priorLength : prior.length = n := by
          rw [S.readyExtend_length] at length
          omega
        rw [ih ⟨⟨h, τ, 0⟩, prior⟩ priorLength, S.likelihood_readyExtend]
        unfold readyExtend
        rw [runBehavioralFrom_one_apply (S.model M) (S.liftProfile M profile)
          ⟨⟨h, τ, 0⟩, prior⟩ legal.1, S.step_ready_apply,
          S.behavioralJoint_lift_apply M profile prior legal.1 joint legal]
        have source : M.historyReachWeight profile (h.extend legal realized) =
            M.historyReachWeight profile h *
              ((M.behavioralJoint profile h.trace legal.1) ⟨joint, legal⟩ *
                (E.step h.state ⟨joint, legal⟩) reached) := by
          rw [M.historyReachWeight_eq_prior_mul _ _ (by simp [History.extend, Trace.length])]
          change M.historyReachWeight profile h * M.runBehavioralFrom profile 1 h _ = _
          rw [runBehavioralFrom_one_apply M profile h legal.1 ⟨joint, legal⟩ realized]
        change _ = M.historyReachWeight profile (h.extend legal realized) * S.likelihood prior
        rw [source]
        ring

/-! ## The Bayes projection -/

/-- **Bayes beliefs project.** Under a fully mixed source profile, the Bayes
belief of the lifted profile at a decision site of the expansion, pushed to
source histories, is the source Bayes belief at the underlying source site:
the scheduler likelihood is constant on the fiber and cancels. The source
fibers must be nonterminal and the public transcript recoverable from every
player's information at its decisions. -/
theorem bayesBelief_lift_map (profile : ∀ i, M.BehavioralPolicy i)
    (full : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (profile i site.1).support)
    (antichainM : M.DecisionInformationAntichain)
    (antichainN : (S.model M).DecisionInformationAntichain)
    (nonterminal : ∀ i (site : M.InformationSite i), site.AllNonterminal)
    (recoverable : ∀ i (site : M.InformationSite i)
      (h h' : M.InformationHistory i site.1), S.pubTrace h.1.trace = S.pubTrace h'.1.trace)
    (who : ι) (site : (S.model M).InformationSite who) :
    ((S.model M).bayesBelief (S.liftProfile M profile) who site (antichainN who site)
        ((S.model M).informationMass_pos_of_fullSupport _
          (S.liftProfile_fullSupport M profile full) who site)).map
        (S.eraseHistory M who site) =
      M.bayesBelief profile who (S.sourceSite M who site) (antichainM who _)
        (M.informationMass_pos_of_fullSupport profile full who _) := by
  classical
  obtain ⟨witness, _, _⟩ := site.2
  refine InformationModel.bayesBelief_projection_of_proportional_reach (S.model M) M
    (S.liftProfile M profile) profile S.erase who site (S.sourceSite M who site)
    (fun x member => S.erase_mem M who site ⟨x, member⟩)
    (S.likelihood witness.1.trace) ?_ (S.likelihood_pos _).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (S.likelihood_le_one _))
    (antichainN who site) (antichainM who _) _ _
  intro history
  have running : ¬ E.terminal history.1.state := nonterminal who _ history
  have pubs : S.pubTrace history.1.trace = S.pubTrace (S.erase witness.1).trace :=
    recoverable who (S.sourceSite M who site) history (S.eraseHistory M who site witness)
  obtain ⟨y, same⟩ := S.exists_replay witness.1.trace.length witness.1 rfl history.1 running pubs
  have member : (S.model M).infoOf who y.trace = site.1 := by
    rw [show (S.model M).infoOf who y.trace = (S.signals M).infoOf who y.trace from rfl,
      S.infoOf_eq, same]
    dsimp only
    rw [history.2, S.transcript_mem M who site witness, S.pending_mem M who site witness]
    rfl
  have weight : (S.model M).historyReachWeight (S.liftProfile M profile) y =
      M.historyReachWeight profile history.1 * S.likelihood witness.1.trace := by
    rw [S.historyReachWeight_lift M profile _ y rfl]
    congr 1
    · change M.historyReachWeight profile y.state.source = _
      rw [same]
    · exact S.likelihood_congr _ y witness.1 rfl
        (by change S.pubTrace y.state.source.trace = _; rw [same]; exact pubs)
        (by rw [same, S.transcript_mem M who site witness])
        (by rw [same, S.pending_mem M who site witness])
  rw [tsum_eq_single ⟨y, member⟩]
  · rw [ite_eq_left (by change y.state.source = history.1; rw [same]), weight, mul_comm]
  · intro other different
    rw [ite_eq_right]
    intro erased
    apply different
    apply Subtype.ext
    apply S.eq_of_state_eq other.1.trace.length other.1 y rfl
    rw [same]
    change (⟨other.1.state.source, other.1.state.transcript, other.1.state.pending⟩ : S.State) = _
    rw [S.transcript_mem M who site other, S.pending_mem M who site other,
      ← S.transcript_mem M who site witness, ← S.pending_mem M who site witness]
    exact congrArg (fun h : E.History => (⟨h, _, _⟩ : S.State)) erased

/-! ## The erased terminal law -/

/-- Terminal play from a terminal history is that history. -/
private theorem runBehavioralTerminalFrom_of_terminal {E' : ExecutionProtocol ι}
    (M' : InformationModel E') (certificate : E'.WellFoundedHistories)
    (policies : ∀ i, M'.BehavioralPolicy i) {h : E'.History} (terminal : E'.terminal h.state) :
    M'.runBehavioralTerminalFrom certificate policies h = PMF.pure h :=
  E'.randomizedBackwardLaw_of_terminal terminal

/-- The joint law of a lifted profile at a ready history is the source joint
law, transported along the identity of legal joint actions. -/
theorem behavioralJoint_lift (profile : ∀ i, M.BehavioralPolicy i) {h : E.History}
    {τ : List Token} (trace : S.protocol.Trace ⟨h, τ, 0⟩) (hterm : ¬ E.terminal h.state) :
    (S.model M).behavioralJoint (S.liftProfile M profile) trace hterm =
      (M.behavioralJoint profile h.trace hterm).map
        (fun joint => ⟨joint.1, (S.legal_ready h τ joint.1).mpr joint.2⟩) := by
  ext ⟨joint, legal⟩
  rw [S.behavioralJoint_lift_apply M profile trace hterm joint legal]
  have injective : Function.Injective
      (fun joint : { joint : ∀ i, Option (E.Action i) // E.Legal h.state joint } =>
        (⟨joint.1, (S.legal_ready h τ joint.1).mpr joint.2⟩ :
          { joint : ∀ i, Option (E.Action i) // S.protocol.Legal ⟨h, τ, 0⟩ joint })) :=
    fun _ _ same => Subtype.ext (congrArg Subtype.val same)
  exact (pmf_map_apply_of_injective _ injective ⟨joint, legal⟩).symm

/-- **Erased terminal law.** Terminal play of a lifted profile from an expanded
history, with the transcript erased, is source terminal play from its source
history: waits are chance moves that sum to one, and source transitions
carry the source laws. -/
theorem erase_terminalLaw {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : ∀ i, M.BehavioralPolicy i) :
    ∀ (k : ℕ) (x : S.protocol.History), (S.draws + 1) * bound ≤ x.trace.length + k →
      ((S.model M).runBehavioralTerminalFrom (S.boundedHorizon bounded).wellFoundedHistories
          (S.liftProfile M profile) x).map S.erase =
        M.runBehavioralTerminalFrom bounded.wellFoundedHistories profile (S.erase x) := by
  intro k
  induction k with
  | zero =>
      intro x horizon
      have terminal : S.protocol.terminal x.state :=
        S.boundedHorizon bounded x.state x.trace (by omega)
      rw [runBehavioralTerminalFrom_of_terminal _ _ _ terminal,
        runBehavioralTerminalFrom_of_terminal M _ profile (h := S.erase x) terminal, PMF.pure_map]
  | succ k ih =>
      intro x horizon
      by_cases terminal : S.protocol.terminal x.state
      · rw [runBehavioralTerminalFrom_of_terminal _ _ _ terminal,
          runBehavioralTerminalFrom_of_terminal M _ profile (h := S.erase x) terminal,
          PMF.pure_map]
      obtain ⟨⟨h, τ, p⟩, trace⟩ := x
      have horizon' : ∀ (joint : _) (legal : S.protocol.Legal ⟨h, τ, p⟩ joint) (reached : _)
          (realized : reached ∈ (S.protocol.step ⟨h, τ, p⟩ ⟨joint, legal⟩).support),
          (S.draws + 1) * bound ≤
            ((⟨⟨h, τ, p⟩, trace⟩ : S.protocol.History).extend legal realized).trace.length + k := by
        intro joint legal reached realized
        change (S.draws + 1) * bound ≤ trace.length + 1 + k
        change (S.draws + 1) * bound ≤ trace.length + (k + 1) at horizon
        omega
      rw [(S.model M).runBehavioralTerminalFrom_of_not_terminal _ _ terminal]
      cases p with
      | zero =>
          rw [M.runBehavioralTerminalFrom_of_not_terminal _ _ terminal,
            S.behavioralJoint_lift M profile trace terminal, PMF.bind_map, PMF.map_bind]
          apply bind_congr_on_support
          intro joint _
          simp only [Function.comp_apply]
          rw [map_bindOnSupport]
          change ((E.step h.state ⟨joint.1, joint.2⟩).bindOnSupport fun _ realized =>
            PMF.pure (⟨h.extend joint.2 realized, τ, S.draws⟩ : S.State)).bindOnSupport _ = _
          rw [PMF.bindOnSupport_bindOnSupport]
          apply bindOnSupport_congr
          intro reached realized
          rw [PMF.pure_bindOnSupport]
          exact ih _ (horizon' _ _ _ _)
      | succ p =>
          rw [S.behavioralJoint_lift_waiting M profile trace terminal, PMF.pure_bind]
          apply map_bindOnSupport_const
          intro reached realized
          obtain ⟨token, _, rfl⟩ := (S.mem_step_waiting h τ p _ _).mp realized
          exact ih _ (horizon' _ _ _ _)

/-- Any profile that agrees with a lifted profile on the cone of an expanded
history has the erased source terminal law from it. -/
theorem erase_terminalLaw_of_agree {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : ∀ i, M.BehavioralPolicy i) (expanded : ∀ i, (S.model M).BehavioralPolicy i)
    (x : S.protocol.History)
    (agree : ∀ y, S.protocol.HistoryReaches x y → ¬ S.protocol.terminal y.state → ∀ i,
      expanded i ((S.model M).infoOf i y.trace) =
        S.liftProfile M profile i ((S.model M).infoOf i y.trace)) :
    ((S.model M).runBehavioralTerminalFrom (S.boundedHorizon bounded).wellFoundedHistories
        expanded x).map S.erase =
      M.runBehavioralTerminalFrom bounded.wellFoundedHistories profile (S.erase x) := by
  rw [(S.model M).runBehavioralTerminalFrom_congr _ x agree]
  exact S.erase_terminalLaw M bounded profile ((S.draws + 1) * bound) x (Nat.le_add_left _ _)

/-! ## Local deviations at a ready site -/

variable [DecidableEq ι]

/-- A decision site of the expansion presented by its source information,
transcript and decision witness. -/
abbrev readySite (who : ι) (info : M.InfoState who) (τ : List Token)
    (witness : (S.model M).IsDecisionInfo who (info, τ, 0)) : (S.model M).InformationSite who :=
  ⟨(info, τ, 0), witness⟩

omit [Fintype ι] in
/-- Replacing the local law of a lifted profile at a ready site agrees, on the
cone of every history of that site, with the lift of the source profile whose
local law at the underlying source site is replaced by the unlifted law. The
source site is never revisited after acting there, by decision recall. -/
theorem lift_withLaw_agree [∀ i, DecidableEq (M.InfoState i)] [DecidableEq Token]
    (recall : M.DecisionRecall) (profile : ∀ i, M.BehavioralPolicy i) (who : ι)
    (info : M.InfoState who) (τ : List Token)
    (witness : (S.model M).IsDecisionInfo who (info, τ, 0))
    (law : PMF ((S.model M).Choice who (info, τ, 0)))
    (x : (S.model M).InformationHistory who (S.readySite M who info τ witness).1) :
    ∀ y, S.protocol.HistoryReaches x.1 y → ¬ S.protocol.terminal y.state → ∀ i,
      Profile.update (sig := (S.model M).behavioralSignature) (S.liftProfile M profile) who
          ((S.liftProfile M profile who).withLaw (info, τ, 0) law) i
          ((S.model M).infoOf i y.trace) =
        S.liftProfile M (Profile.update (sig := M.behavioralSignature) profile who
          ((profile who).withLaw info (law.map (S.unliftChoice M who info τ)))) i
          ((S.model M).infoOf i y.trace) := by
  intro y reach running i
  by_cases player : i = who
  swap
  · rw [Profile.update_of_ne _ _ player]
    change _ = S.liftPolicy M i (Profile.update (sig := M.behavioralSignature) profile who _ i) _
    rw [Profile.update_of_ne _ _ player]
    rfl
  subst player
  rw [Profile.update_same]
  change _ = S.liftPolicy M i (Profile.update (sig := M.behavioralSignature) profile i _ i) _
  rw [Profile.update_same]
  rw [show (S.model M).infoOf i y.trace = (S.signals M).infoOf i y.trace from rfl, S.infoOf_eq]
  by_cases same : y = x.1
  · obtain rfl := same
    have infoEq : M.infoOf i x.1.state.source.trace = info := S.erase_mem M i _ x
    rw [show x.1.state.transcript = τ from S.transcript_mem M i _ x,
      show x.1.state.pending = 0 from S.pending_mem M i _ x, infoEq,
      InformationModel.BehavioralPolicy.withLaw_self, liftPolicy_ready,
      InformationModel.BehavioralPolicy.withLaw_self, PMF.map_comp]
    exact (PMF.map_id law).symm
  · have active : E.active (S.erase x.1).state i := by
      have := InformationModel.InformationSite.active (S.model M)
        (S.readySite M i info τ witness) x
      have pending := S.pending_mem M i _ x
      change S.active x.1.state i at this
      change x.1.state.pending = 0 at pending
      revert this
      change S.active ⟨x.1.state.source, x.1.state.transcript, x.1.state.pending⟩ i → _
      rw [pending]
      exact id
    obtain ⟨joint, legal, reached, realized, rest⟩ :=
      S.erase_reaches_extend (S.pending_mem M i _ x) reach same
    obtain ⟨fuel, rest⟩ := rest
    have eraseInfo : M.infoOf i (S.erase x.1).trace = info :=
      S.erase_mem M i (S.readySite M i info τ witness) x
    have differentInfo : M.infoOf i y.state.source.trace ≠ info := by
      rw [← eraseInfo]
      exact recall.infoOf_ne_after_step i legal realized active rest
    have differentSite : (M.infoOf i y.state.source.trace, y.state.transcript, y.state.pending) ≠
        (info, τ, 0) := fun equal => differentInfo (congrArg Prod.fst equal)
    rw [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ differentSite]
    cases y.state.pending with
    | zero =>
        rw [liftPolicy_ready, InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ differentInfo]
        rfl
    | succ p => rfl

/-! ## Finitely many expanded histories -/

omit [Fintype ι] [DecidableEq ι] in
/-- With finitely many source histories, finitely supported kernels and a
source horizon, the expansion has finitely many histories. -/
theorem finite_history [Finite ι] [Finite E.History] {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (finiteKernel : ∀ pub τ p, (S.kernel pub τ p).support.Finite)
    (profile : ∀ i, M.BehavioralPolicy i)
    (full : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (profile i site.1).support) : Finite S.protocol.History := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let assessment : (S.model M).BehavioralAssessment :=
    InformationModel.BehavioralAssessment.ofStrategy (S.liftProfile M profile)
  have mixed : assessment.IsFullyMixed := S.liftProfile_fullSupport M profile full
  have lengths : ∀ x : S.protocol.History, x.trace.length ≤ (S.draws + 1) * bound := by
    intro ⟨state, trace⟩
    cases trace with
    | start => exact Nat.zero_le _
    | extend prior joint legal realized =>
        have before : prior.length < (S.draws + 1) * bound := by
          by_contra tooLong
          exact legal.1 (S.boundedHorizon bounded _ prior (by omega))
        exact Nat.succ_le_of_lt before
  have choices : ∀ x : S.protocol.History, ¬ S.protocol.terminal x.state → ∀ i,
      (S.liftProfile M profile i ((S.model M).infoOf i x.trace)).support.Finite := by
    intro ⟨⟨h, τ, p⟩, trace⟩ running i
    rw [show (S.model M).infoOf i trace = (S.signals M).infoOf i trace from rfl, S.infoOf_eq]
    cases p with
    | zero =>
        have : Finite ((S.model M).Choice i (M.infoOf i h.trace, τ, 0)) :=
          M.finite_choice_of_nonterminal h running i
        exact Set.toFinite _
    | succ p =>
        change (PMF.pure (S.idle M i (M.infoOf i h.trace) τ p)).support.Finite
        rw [PMF.support_pure]
        exact Set.finite_singleton _
  have steps : ∀ {state : S.State}
      (draw : { joint : ∀ i, Option (E.Action i) // S.protocol.Legal state joint }),
      (S.protocol.step state draw).support.Finite := by
    intro ⟨h, τ, p⟩ draw
    cases p with
    | zero =>
        change ((E.step h.state ⟨draw.1, draw.2⟩).bindOnSupport fun _ realized =>
          PMF.pure (⟨h.extend draw.2 realized, τ, S.draws⟩ : S.State)).support.Finite
        rw [PMF.support_bindOnSupport]
        refine Set.Finite.biUnion' (ExecutionProtocol.FiniteTransitions.of_finite_history h
          draw.2.1 ⟨draw.1, draw.2⟩) ?_
        intro reached realized
        rw [PMF.support_pure]
        exact Set.finite_singleton _
    | succ p =>
        change ((S.kernel (S.pub h) τ (p + 1)).map _).support.Finite
        rw [PMF.support_map]
        exact (finiteKernel _ _ _).image _
  have cover := Set.finite_iUnion fun index : Fin ((S.draws + 1) * bound + 1) =>
    (S.model M).runBehavioralFrom_support_finite_of_finite_branching (S.liftProfile M profile)
      index.val S.protocol.initHistory choices steps
  apply Set.finite_univ_iff.mp
  apply cover.subset
  intro x _
  exact Set.mem_iUnion.mpr ⟨⟨x.trace.length, by have := lengths x; omega⟩,
    mixed.history_supported x.trace⟩

/-! ## Transport of continuation laws at ready sites -/

/-- The expanded continuation law at a ready site under the lifted Bayes
assessment, erased to source outcomes, is the source continuation law at the
underlying source site under the source assessment, for any pair of local
replacement policies that agree, lifted, on every continuation. -/
theorem lift_assessmentLaw
    {bound : ℕ} (bounded : E.BoundedHorizon bound) (recall : M.DecisionRecall)
    (nonterminal : ∀ i (site : M.InformationSite i), site.AllNonterminal)
    (recoverable : ∀ i (site : M.InformationSite i)
      (h h' : M.InformationHistory i site.1), S.pubTrace h.1.trace = S.pubTrace h'.1.trace)
    (actors : ∀ i (h h' : E.History), S.pub h = S.pub h' →
      (E.active h.state i ↔ E.active h'.state i))
    (assessment : M.BehavioralAssessment) (full : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent M assessment
      recall.decisionInformationAntichain)
    (who : ι) (info : M.InfoState who) (τ : List Token)
    (witness : (S.model M).IsDecisionInfo who (info, τ, 0))
    (policyN : (S.model M).BehavioralPolicy who) (policyM : M.BehavioralPolicy who)
    (agree : ∀ x : (S.model M).InformationHistory who (S.readySite M who info τ witness).1,
      ∀ y, S.protocol.HistoryReaches x.1 y → ¬ S.protocol.terminal y.state → ∀ i,
        Profile.update (sig := (S.model M).behavioralSignature)
            (S.liftProfile M assessment.strategy) who policyN i ((S.model M).infoOf i y.trace) =
          S.liftProfile M (Profile.update (sig := M.behavioralSignature) assessment.strategy who
            policyM) i ((S.model M).infoOf i y.trace))
    {Outcome : Type*} (observe : E.History → Outcome) :
    ((S.model M).assessmentLawWith ((S.model M).truncatedRunner ((S.draws + 1) * bound))
        ((S.model M).bayesAssessment (S.liftProfile M assessment.strategy)
          (S.liftProfile_fullSupport M assessment.strategy full)
          (S.decisionRecall M recall recoverable actors).decisionInformationAntichain)
        (S.readySite M who info τ witness) policyN).map (fun x => observe (S.erase x)) =
      (M.assessmentLawWith (M.truncatedRunner bound) assessment
        (S.sourceSite M who (S.readySite M who info τ witness)) policyM).map observe := by
  classical
  unfold InformationModel.assessmentLawWith
  rw [InformationModel.bayesAssessment_strategy, PMF.map_bind, PMF.map_bind]
  have inner (x : (S.model M).InformationHistory who (S.readySite M who info τ witness).1) :
      PMF.map (fun y => observe (S.erase y))
          ((S.model M).truncatedRunner ((S.draws + 1) * bound)
            (Profile.update (sig := (S.model M).behavioralSignature)
              (S.liftProfile M assessment.strategy) who policyN) x.1) =
        PMF.map observe (M.truncatedRunner bound
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who policyM)
          (S.erase x.1)) := by
    rw [show (fun y : S.protocol.History => observe (S.erase y)) = observe ∘ S.erase from rfl,
      ← PMF.map_comp]
    change PMF.map observe (PMF.map S.erase ((S.model M).runBehavioralFrom _ _ x.1)) =
      PMF.map observe (M.runBehavioralFrom _ _ (S.erase x.1))
    rw [← (S.model M).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
        (S.boundedHorizon bounded).wellFoundedHistories (S.boundedHorizon bounded),
      S.erase_terminalLaw_of_agree M bounded _ _ x.1 (agree x),
      M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
        bounded.wellFoundedHistories bounded]
  rw [bind_congr_on_support _ (fun x _ => inner x)]
  rw [show (fun x : (S.model M).InformationHistory who (S.readySite M who info τ witness).1 =>
      PMF.map observe (M.truncatedRunner bound
        (Profile.update (sig := M.behavioralSignature) assessment.strategy who policyM)
        (S.erase x.1))) =
      (fun h : M.InformationHistory who (S.sourceSite M who (S.readySite M who info τ witness)).1 =>
        PMF.map observe (M.truncatedRunner bound
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who policyM)
          h.1)) ∘ S.eraseHistory M who (S.readySite M who info τ witness) from rfl,
    ← PMF.bind_map]
  change (PMF.map (S.eraseHistory M who (S.readySite M who info τ witness))
    ((S.model M).bayesBelief (S.liftProfile M assessment.strategy) who
      (S.readySite M who info τ witness)
      ((S.decisionRecall M recall recoverable actors).decisionInformationAntichain who
        (S.readySite M who info τ witness))
      ((S.model M).informationMass_pos_of_fullSupport _
        (S.liftProfile_fullSupport M assessment.strategy full) who
        (S.readySite M who info τ witness)))).bind _ = _
  rw [S.bayesBelief_lift_map M assessment.strategy full recall.decisionInformationAntichain
    (S.decisionRecall M recall recoverable actors).decisionInformationAntichain nonterminal
    recoverable who (S.readySite M who info τ witness)]
  rw [(InformationModel.BehavioralAssessment.isBayesConsistentAt_iff M assessment who
    (S.sourceSite M who (S.readySite M who info τ witness)) _
    (M.informationMass_pos_of_fullSupport assessment.strategy full who _)).mp
    (bayes who _ _)]

/-- **Local comparisons at ready sites.** Under the lifted Bayes assessment of a
fully mixed Bayes-consistent source assessment, every local deviation at a
decision site of the expansion has exactly the gain of the corresponding local
deviation at the underlying source site. -/
theorem localComparison [∀ i, DecidableEq (M.InfoState i)] [DecidableEq Token]
    {bound : ℕ} (bounded : E.BoundedHorizon bound) (recall : M.DecisionRecall)
    (nonterminal : ∀ i (site : M.InformationSite i), site.AllNonterminal)
    (recoverable : ∀ i (site : M.InformationSite i)
      (h h' : M.InformationHistory i site.1), S.pubTrace h.1.trace = S.pubTrace h'.1.trace)
    (actors : ∀ i (h h' : E.History), S.pub h = S.pub h' →
      (E.active h.state i ↔ E.active h'.state i))
    (assessment : M.BehavioralAssessment) (full : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent M assessment
      recall.decisionInformationAntichain)
    {Outcome : Type*} (observe : E.History → Outcome) (utility : Outcome → ι → ℝ)
    (who : ι) (site : (S.model M).InformationSite who)
    (law : PMF ((S.model M).Choice who site.1)) :
    let lifted := (S.model M).bayesAssessment (S.liftProfile M assessment.strategy)
      (S.liftProfile_fullSupport M assessment.strategy full)
      (S.decisionRecall M recall recoverable actors).decisionInformationAntichain
    let comparison := (S.model M).assessmentComparisonWith
      ((S.model M).truncatedRunner ((S.draws + 1) * bound)) (fun x => observe (S.erase x))
      lifted who (site, (lifted.strategy who).withLaw site.1 law)
    expect comparison.alternative (utility · who) -
        expect comparison.prescribed (utility · who) ≤ 0 ∨
      ∃ mixture : PMF (M.AssessmentDeviation who),
        expect comparison.alternative (utility · who) -
            expect comparison.prescribed (utility · who) ≤
          expect mixture (fun deviation =>
            let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner bound)
              observe assessment who deviation
            expect sourceComparison.alternative (utility · who) -
              expect sourceComparison.prescribed (utility · who)) + 0 := by
  intro lifted comparison
  obtain ⟨⟨info, τ, p⟩, witness⟩ := site
  cases p with
  | succ p =>
      exact absurd (S.pending_eq_zero M who ⟨(info, τ, p + 1), witness⟩) (Nat.succ_ne_zero p)
  | zero =>
      right
      refine ⟨PMF.pure (S.sourceSite M who (S.readySite M who info τ witness),
        (assessment.strategy who).withLaw info (law.map (S.unliftChoice M who info τ))), ?_⟩
      rw [expect_pure, add_zero]
      dsimp only
      have prescribed : comparison.prescribed =
          (M.assessmentComparisonWith (M.truncatedRunner bound) observe assessment who
            (S.sourceSite M who (S.readySite M who info τ witness),
              (assessment.strategy who).withLaw info
                (law.map (S.unliftChoice M who info τ)))).prescribed := by
        change ((S.model M).assessmentLawWith _ lifted (S.readySite M who info τ witness)
          (S.liftProfile M assessment.strategy who)).map _ =
          (M.assessmentLawWith _ assessment _ (assessment.strategy who)).map observe
        exact S.lift_assessmentLaw M bounded recall nonterminal recoverable actors assessment
          full bayes who info τ witness _ _ (fun _ _ _ _ i => by
            rw [Profile.update_eq_self, Profile.update_eq_self]) observe
      have alternative : comparison.alternative =
          (M.assessmentComparisonWith (M.truncatedRunner bound) observe assessment who
            (S.sourceSite M who (S.readySite M who info τ witness),
              (assessment.strategy who).withLaw info
                (law.map (S.unliftChoice M who info τ)))).alternative := by
        change ((S.model M).assessmentLawWith _ lifted (S.readySite M who info τ witness)
          ((S.liftProfile M assessment.strategy who).withLaw (info, τ, 0) law)).map _ =
          (M.assessmentLawWith _ assessment _ _).map observe
        exact S.lift_assessmentLaw M bounded recall nonterminal recoverable actors assessment
          full bayes who info τ witness _ _
          (S.lift_withLaw_agree M recall assessment.strategy who info τ witness law) observe
      rw [prescribed, alternative]

/-! ## The preservation theorem -/

/-- **Sequential equilibrium under bounded public scheduling.** Let a finite
source model have decision recall, nonterminal decision fibers, and a public
projection that every player can recover, with the actors, from its
information at each of its decisions. Then every sequential equilibrium of the
source model has a sequential equilibrium of the expansion by any finitely
supported public scheduler, with the same law of erased terminal histories,
whose strategy plays the source law at every decision of the expansion. -/
theorem expanded_sequentialEquilibrium [Finite E.History] {bound : ℕ}
    (bounded : E.BoundedHorizon bound) (recall : M.DecisionRecall)
    (nonterminal : ∀ i (site : M.InformationSite i), site.AllNonterminal)
    (recoverable : ∀ i (site : M.InformationSite i)
      (h h' : M.InformationHistory i site.1), S.pubTrace h.1.trace = S.pubTrace h'.1.trace)
    (actors : ∀ i (h h' : E.History), S.pub h = S.pub h' →
      (E.active h.state i ↔ E.active h'.state i))
    (finiteKernel : ∀ pub τ p, (S.kernel pub τ p).support.Finite)
    {Outcome : Type*} (observe : E.History → Outcome) (utility : Outcome → ι → ℝ)
    (source : M.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium recall.decisionInformationAntichain
      bounded.wellFoundedHistories (fun i h => utility (observe h) i)) :
    ∃ target : (S.model M).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (S.decisionRecall M recall recoverable actors).decisionInformationAntichain
        (S.boundedHorizon bounded).wellFoundedHistories
        (fun i x => utility (observe (S.erase x)) i) ∧
      ((S.model M).runBehavioralTerminalFrom (S.boundedHorizon bounded).wellFoundedHistories
          target.strategy S.protocol.initHistory).map (fun x => observe (S.erase x)) =
        (M.runBehavioralTerminalFrom bounded.wellFoundedHistories source.strategy
          E.initHistory).map observe ∧
      ∀ i (site : (S.model M).InformationSite i),
        target.strategy i site.1 = S.liftProfile M source.strategy i site.1 := by
  classical
  obtain ⟨sequence, admissible, converges⟩ := equilibrium.2
  have mixed : ∀ n, (sequence n).IsFullyMixed := fun n => (admissible n).1
  have bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent M (sequence n)
      recall.decisionInformationAntichain := fun n => (admissible n).2
  have : Finite S.protocol.History :=
    S.finite_history M bounded finiteKernel (sequence 0).strategy (mixed 0)
  have truncated := (source.isSequentialEquilibrium_iff_truncated_of_bounded M
    recall.decisionInformationAntichain bounded.wellFoundedHistories bounded _).mp equilibrium
  let targetSequence (n : ℕ) : (S.model M).BehavioralAssessment :=
    (S.model M).bayesAssessment (S.liftProfile M (sequence n).strategy)
      (S.liftProfile_fullSupport M (sequence n).strategy (mixed n))
      (S.decisionRecall M recall recoverable actors).decisionInformationAntichain
  have initialized (n : ℕ) :
      ((S.model M).runBehavioral (targetSequence n).strategy ((S.draws + 1) * bound)).map
          (fun x => observe (S.erase x)) =
        (M.runBehavioral (sequence n).strategy bound).map observe := by
    rw [← InformationModel.runBehavioralTerminalFrom_initHistory _
        (S.boundedHorizon bounded).wellFoundedHistories _ (S.boundedHorizon bounded),
      ← InformationModel.runBehavioralTerminalFrom_initHistory _ bounded.wellFoundedHistories _
        bounded,
      show (fun x : S.protocol.History => observe (S.erase x)) = observe ∘ S.erase from rfl,
      ← PMF.map_comp]
    change PMF.map observe (PMF.map S.erase ((S.model M).runBehavioralTerminalFrom _
      (S.liftProfile M (sequence n).strategy) S.protocol.initHistory)) = _
    rw [S.erase_terminalLaw M bounded _ ((S.draws + 1) * bound) _ (Nat.le_add_left _ _)]
    rfl
  obtain ⟨target, targetEquilibrium, law, index, increasing, targetConverges⟩ :=
    InformationModel.exists_sequentialEquilibrium_limit_of_local_comparisons observe
      (fun x => observe (S.erase x)) bound ((S.draws + 1) * bound) (S.boundedHorizon bounded)
      (S.decisionRecall M recall recoverable actors) utility source sequence converges
      truncated.1 targetSequence
      (fun n => InformationModel.bayesAssessment_isFullyMixed (S.model M) _ _ _)
      (fun n => InformationModel.bayesAssessment_isBayesConsistent (S.model M) _ _ _)
      (fun _ => 0) tendsto_const_nhds
      (fun n who site law => S.localComparison M bounded recall nonterminal recoverable actors
        (sequence n) (mixed n) (bayes n) observe utility who site law)
      initialized
  refine ⟨target, ?_, ?_, ?_⟩
  · exact (target.isSequentialEquilibrium_iff_truncated_of_bounded (S.model M) _
      (S.boundedHorizon bounded).wellFoundedHistories (S.boundedHorizon bounded) _).mpr
      targetEquilibrium
  · rw [InformationModel.runBehavioralTerminalFrom_initHistory _ _ _ (S.boundedHorizon bounded),
      InformationModel.runBehavioralTerminalFrom_initHistory _ _ _ bounded]
    exact law
  · intro i site
    obtain ⟨⟨info, τ, p⟩, witness⟩ := site
    cases p with
    | succ p =>
        exact absurd (S.pending_eq_zero M i ⟨(info, τ, p + 1), witness⟩) (Nat.succ_ne_zero p)
    | zero =>
        have sourceLimit : PMFConvergesPointwise
            (fun n => (sequence (index n)).strategy i info) (source.strategy i info) :=
          fun value => (converges.strategy i (S.sourceSite M i (S.readySite M i info τ witness))
            value).comp increasing.tendsto_atTop
        have liftedLimit : PMFConvergesPointwise
            (fun n => (targetSequence (index n)).strategy i (info, τ, 0))
            (S.liftProfile M source.strategy i (info, τ, 0)) := by
          intro choice
          change Filter.Tendsto (fun n =>
              ((sequence (index n)).strategy i info).map (S.liftChoice M i info τ) choice) _
            (nhds (((source.strategy i info).map (S.liftChoice M i info τ)) choice))
          rw [← S.liftChoice_unliftChoice M i info τ choice]
          simp only [pmf_map_apply_of_injective _ (S.liftChoice_injective M i info τ)]
          exact sourceLimit _
        exact (targetConverges.strategy i (S.readySite M i info τ witness)).unique liftedLimit

end PublicScheduler

end GameTheory.Protocol
