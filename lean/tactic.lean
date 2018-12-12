-- This tries to prove a property by just running the evaluator.
meta def dec_trivial_tac : tactic unit := do
  tgt ← tactic.target,
  tactic.apply $ (`(@of_as_true) : expr) tgt,
  tactic.triv
