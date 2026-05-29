### PVS Proof Commands

| Command | Action |
| :--- | :--- |
| `(assert)` | Decision procedure and auto-rewrites |
| `(case "<e>")` | Case analysis on boolean expression `<e>` |
| `(decompose-equality <fnum>)` | Decompose equality in formula `<fnum>` |
| `(eval-expr "<e>")` | Evaluate the ground expression `<e>` |
| `(eval-formula <fnum>)` | Evaluate the ground formula in `<fnum>` |
| `(expand "<name>" <fnum> <n>)` | Expand `<n>`-th occurrence of `<name>` in formula number `<fnum>` |
| `(expand* "<nm1>" ... "<nmn>")` | Expand `<nm1> `... `<nmn>` everywhere in the sequent |
| `(flatten <fnum>)`| Eliminate conjunctions in the antecedent and disjunctions in the consequent |
| `(grind)` | A super-duper strategy |
| `(grind-reals)` | Grind plus auto-rewrite with real number properties |
| `(ground)` | Propositional simplification plus decision procedures |
| `(help <proof-command>)` | Display usage information of `<proof-command>` |
| `(induct "<var>")` | Inductive proof on variable `<var>` |
| `(inst? <fnum>)` | Guess instantiation of quantifier in formula `<fnum>` |
| `(inst <fnum> "<e1>" ... "<en>")` | Instantiate universal formula in `<fnum>` with expressions `<e1>` ... `<en>` |
| `(lemma "<name>")` | Introduce lemma called `<name>`|
| `(name "<name>" "<e>")` | Introduce constant `<name>` and make it equals to expression `<e>` |
| `(name-replace "<name>" "<e>")` | Replace `<name>` by expression `<e>` everywhere in the sequent |
| `(replace <fnum>)` | Left-right replacement of an equality in formula number `<fnum>` |
| `(replace <fnum> :dir rl)` | Right-left replacement of an equality in formula number `<fnum>` |
| `(rewrite "<name>")` | Left-right rewriting of equality lemma `<name>` |
| `(rewrite <name> :dir rl)` | Right-left rewriting of equality lemma `<name>` |
| `(skeep <fnum> :preds? t)` | Eliminate universal quantifier in formula number `<fnum>` with skolem constants and introduce their type predicates |
| `(split <fnum>)`| Eliminate disjunctions in the antecedent and conjunctions in the consequent |
| `(typepred "<e>")` | Introduce the type predicate of expression `<e>` into the sequent |
