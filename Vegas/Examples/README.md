# Vegas Examples

The examples are organized by the layer of the stack they exercise.

## Checked Programs

- `Prisoners.lean`: a two-player commit/reveal Prisoner's Dilemma.
- `MatchingPennies.lean`: a zero-sum commit/reveal game.
- `BattleOfTheSexes.lean`: a coordination game with two pure equilibria.
- `MontyHall.lean`: a small protocol with legality constraints on the host's
  action and payoff facts about switching versus staying.
- `SyntaxConstructors.lean`: a minimal checked program that exercises
  deterministic `letExpr` and public `sample`.
- `BackendExamples.lean`: the identity backend refinement and its trace
  projection theorem, used as a small backend API smoke test.

These files are good entry points for a programmer writing a new Vegas program:
define the source program, prove well-formedness/legal guards/finite domains,
then expose `pureKernelGame` and `pmfBehavioralKernelGame`.

## Solution Concepts

`SolutionConcepts.lean` gives compact theorem-proving examples for the
GameTheory layer used by Vegas:

- dominant strategies, best responses, and Nash equilibria;
- strict Nash equilibria;
- zero-sum and team games;
- exact potential games and Nash via potential maximization;
- second-price auction truthfulness through the reusable Vickrey theorem;
- checked payoff facts for the existing Vegas programs, including Monty Hall.

This file intentionally uses small deterministic kernel games where that makes
the solution concept clearer than going through the full compiler.

## Generated Strategic Semantics

`StrategicSemantics.lean` connects checked Vegas programs to the generated
strategic and trace presentations:

- constructs a legal generated pure strategy/profile for any finite checked
  program;
- proves pure expected utility, Nash, and dominance are invariant under
  replacing public outcomes by round histories;
- proves the corresponding PMF-behavioral Nash transport;
- instantiates the Kuhn PMF theorem for the example programs;
- proves that a concrete source-level Prisoner's Dilemma action compiles to an
  initially available protocol-graph action.

This is the layer reviewers should inspect when asking whether examples are
using the generated games, not only hand-written normal-form models.

## Useful Future Examples

- a full Vegas-encoded second-price auction, not only the GameTheory Vickrey
  theorem;
- a generated-strategy proof for a named policy, such as "always defect" or
  "always switch";
- a trace-level theorem about an explicit run of Monty Hall;
- a non-identity backend refinement with internal events.
