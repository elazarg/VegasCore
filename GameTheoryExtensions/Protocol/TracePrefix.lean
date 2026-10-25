/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Protocol.History

/-! # Prefixes of histories

A history is a *prefix* of another when the other extends it by finitely many
realized transitions (`GameTheory.Protocol.ExecutionProtocol.TracePrefix`).
A prefix is no longer than the history it is a prefix of
(`GameTheory.Protocol.ExecutionProtocol.TracePrefix.length_le`).
-/

namespace GameTheory.Protocol

variable {ι : Type*}

namespace ExecutionProtocol

variable {E : ExecutionProtocol ι}

/-- **A prefix of a history**: the history itself, or a prefix of the history
it extends. -/
inductive TracePrefix {first : E.State} (prefixTrace : E.Trace first) :
    {second : E.State} → E.Trace second → Prop
  | refl : TracePrefix prefixTrace prefixTrace
  | extend {source target : E.State} {prior : E.Trace source}
      (earlier : TracePrefix prefixTrace prior) (joint : ∀ i, Option (E.Action i))
      (isLegal : E.Legal source joint)
      (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
      TracePrefix prefixTrace (prior.extend joint isLegal realized)

theorem TracePrefix.length_le {first second : E.State} {prefixTrace : E.Trace first}
    {trace : E.Trace second} (isPrefix : TracePrefix prefixTrace trace) :
    prefixTrace.length ≤ trace.length := by
  induction isPrefix with
  | refl => exact le_rfl
  | extend _ _ _ _ ih => exact ih.trans (Nat.le_succ _)

/-- The canonical continuation between a history prefix and that same full
history uses exactly their trace-length difference. -/
theorem TracePrefix.reachesWithin {first second : E.State} {prefixTrace : E.Trace first}
    {trace : E.Trace second} (isPrefix : TracePrefix prefixTrace trace) :
    E.ReachesWithin (trace.length - prefixTrace.length) ⟨first, prefixTrace⟩ ⟨second, trace⟩ := by
  induction isPrefix with
  | refl => simpa only [Nat.sub_self] using (ReachesWithin.refl 0 ⟨first, prefixTrace⟩)
  | @extend source target prior earlier joint legal realized ih =>
      have last : E.ReachesWithin 1 ⟨source, prior⟩ ⟨target, prior.extend joint legal realized⟩ :=
        .step joint legal realized (.refl 0 _)
      have path := ih.trans last
      have fuel : prior.length - prefixTrace.length + 1 =
          (prior.extend joint legal realized).length - prefixTrace.length := by
        have bounded := earlier.length_le
        simp only [Trace.length]
        omega
      rw [fuel] at path
      exact path

theorem TracePrefix.trans {first second third : E.State} {firstTrace : E.Trace first}
    {secondTrace : E.Trace second} {thirdTrace : E.Trace third}
    (left : TracePrefix firstTrace secondTrace) (right : TracePrefix secondTrace thirdTrace) :
    TracePrefix firstTrace thirdTrace := by
  induction right with
  | refl => exact left
  | extend _ joint isLegal realized ih => exact .extend ih joint isLegal realized

theorem TracePrefix.start : ∀ {state : E.State} (trace : E.Trace state),
    TracePrefix (Trace.start : E.Trace E.init) trace
  | _, .start => .refl
  | _, .extend prior joint isLegal realized =>
      .extend (TracePrefix.start prior) joint isLegal realized

/-- A prefix as long as the history is the history. -/
theorem TracePrefix.eq_of_length {first second : E.State} {prefixTrace : E.Trace first}
    {trace : E.Trace second} (isPrefix : TracePrefix prefixTrace trace)
    (sameLength : prefixTrace.length = trace.length) :
    (⟨first, prefixTrace⟩ : E.History) = ⟨second, trace⟩ := by
  cases isPrefix with
  | refl => rfl
  | extend earlier _ _ _ =>
      have := earlier.length_le
      simp only [Trace.length] at sameLength
      omega

/-- **Two prefixes of one history of the same length are equal.** -/
theorem TracePrefix.eq_of_same_length {first second third : E.State}
    {firstTrace : E.Trace first} {secondTrace : E.Trace second} {trace : E.Trace third}
    (firstPrefix : TracePrefix firstTrace trace) (secondPrefix : TracePrefix secondTrace trace)
    (sameLength : firstTrace.length = secondTrace.length) :
    (⟨first, firstTrace⟩ : E.History) = ⟨second, secondTrace⟩ := by
  induction trace with
  | start =>
      cases firstPrefix
      cases secondPrefix
      rfl
  | extend prior joint isLegal realized ih =>
      cases firstPrefix with
      | refl =>
          exact (secondPrefix.eq_of_length sameLength.symm).symm
      | extend firstEarlier _ _ _ =>
          cases secondPrefix with
          | refl =>
              exact TracePrefix.eq_of_length (.extend firstEarlier joint isLegal realized)
                sameLength
          | extend secondEarlier _ _ _ => exact ih firstEarlier secondEarlier

/-- A finite realized history path retains its actual starting trace as a prefix. -/
theorem ReachesWithin.tracePrefix {fuel : Nat} {first last : E.History}
    (reached : E.ReachesWithin fuel first last) : TracePrefix first.trace last.trace := by
  induction reached with
  | refl => exact .refl
  | step joint legal realized rest ih =>
      exact (TracePrefix.extend .refl joint legal realized).trans ih

/-- Every entry into a state predicate along an actual trace extension has an
actual transition witness between the original start and endpoint histories. -/
theorem TracePrefix.exists_entering_transition {first last : E.State}
    {initialTrace : E.Trace first} {finish : E.Trace last} (path : TracePrefix initialTrace finish)
    (predicate : E.State → Prop) (outside : ¬ predicate first) (inside : predicate last) :
    ∃ (before after : E.State) (prior : E.Trace before) (joint : ∀ who, Option (E.Action who))
      (legal : E.Legal before joint) (moved : after ∈ (E.step before ⟨joint, legal⟩).support),
      TracePrefix initialTrace prior ∧ TracePrefix (prior.extend joint legal moved) finish ∧
        ¬ predicate before ∧ predicate after := by
  classical
  revert inside
  induction path with
  | refl => exact fun inside => False.elim (outside inside)
  | @extend source target prior earlier joint legal moved ih =>
      intro inside
      by_cases previous : predicate source
      · obtain ⟨before, after, history, actions, allowed, realized, retained, suffix,
          wasOutside, isInside⟩ := ih previous
        exact ⟨before, after, history, actions, allowed, realized, retained,
          .extend suffix joint legal moved, wasOutside, isInside⟩
      · exact ⟨source, target, prior, joint, legal, moved, earlier, .refl, previous, inside⟩

/-- A strict history extension exposes its actual final legal transition. -/
theorem TracePrefix.exists_last_transition {first last : E.State}
    {initialTrace : E.Trace first} {finish : E.Trace last} (path : TracePrefix initialTrace finish)
    (longer : initialTrace.length < finish.length) :
    ∃ (before : E.State) (prior : E.Trace before) (joint : ∀ who, Option (E.Action who))
      (legal : E.Legal before joint) (moved : last ∈ (E.step before ⟨joint, legal⟩).support),
      TracePrefix initialTrace prior ∧
        finish = prior.extend joint legal moved := by
  cases path with
  | refl => exact False.elim ((Nat.lt_irrefl _) longer)
  | extend earlier joint legal moved => exact ⟨_, _, joint, legal, moved, earlier, rfl⟩

end ExecutionProtocol

end GameTheory.Protocol
