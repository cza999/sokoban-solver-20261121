# Sokoban Solver — Push-Optimal A*

A Sokoban solver built for make.fun's "Build the best Sokoban solver" bounty:
https://make.fun/bounty/sokoban-solver-01-run-20261121

One program, `main.ts` (Node 22, no dependencies), answers a set of 5
Sokoban levels in XSB format: it reads `/input/<id>/level.txt` and writes
the player's moves to `/output/<id>/solution.txt`.

## How it works

The contest scores *pushes*, not moves — a solution one push over the
optimum earns less than half marks — so the search runs in push space
and optimises pushes exactly:

- **Room decomposition.** Levels from this generator are a hallway with
  small rooms off it. A box pushed into the hallway can never return, so
  each room is independent: the solver cuts the hallway (its squares are
  dead squares), solves each room separately with the other rooms' boxes
  standing as walls, and concatenates the walks. A whole-level search is
  the fallback for levels that do not decompose.
- **A\* over pushes.** A state is the sorted box squares plus the
  player's reachable region (named by its lowest square). The heuristic
  is the cheapest box→goal assignment by lone-box push distances,
  precomputed per goal by reverse pull search — admissible, so the first
  solution found is push-optimal.
- **Deadlock pruning.** Dead squares (reverse pull reachability from the
  goals) and frozen 2×2 blocks of walls/boxes are pruned; neither can
  remove a solvable state.
- **Deterministic.** No clock, no randomness. Budgets count states, not
  seconds, so two runs write byte-identical answers.

On the kit's practice set it solves all 5 levels in exactly the optimal
push counts (13, 16, 29, 47, 60), in about 0.3 s for the whole set.

## Run locally

```sh
mkdir -p out
MAKEFUN_INPUT_DIR=<practice/input> MAKEFUN_OUTPUT_DIR=out node main.ts
```

## License

MIT — see `LICENSE`.
