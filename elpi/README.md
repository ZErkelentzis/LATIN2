Generated ELPI Provers
---

As described [here](https://kwarc.info/people/mkohlhase/submit/mmtelpi.pdf), MMT can generate ELPI provers from some inference rules described in MMT-LF.
This directory contains various examples of the generated provers.
Most of the used ELPI code is generated from inference rules in `../source/logics`.


#### Running the Examples

You need to have the following software installed:
- [ELPI](https://github.com/LPCIC/elpi)
- If you want to generated the ELPI code yourself, you need current development version of [MMT](https://uniformal.github.io//doc/setup/)

The generated ELPI code is located at `../export/lf-elpi/content/latin..NONE/`.
Due to [a bug](https://github.com/LPCIC/elpi/issues/49) in ELPI, `accumulate` can import rules several times.
This results in an exponential slow-down of the provers.
To circumvent this, the `accumulate.sh` script collects the relevant code into files in the `generated` folder.

With all this in place, you should be able to run the provers by calling e.g.
```elpi -no-tc pl_nd_backchaining.elpi```
and the entering the command `main.`.


#### The different Provers

- `pl_nd_backchaining.elpi` - prover for propositional logic using backchaining.
- `pl_nd_id_dfs.elpi` - prover for propositional logic using iterative deepening with a simple depth-first search instead of backchaining.
- `pl_tab_prover.elpi` - tableau prover for propositional logic.
- `pl_tab_open_branches.elpi` - prints open branches after filling a tableau for propositional logic.
- `fol_nd_backchaining.elpi` - prover for first-order logic using backchaining.
- `fol_tab_prover.elpi` - *very* experimental tableau prover for first-order logic.
