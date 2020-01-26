Generated ELPI Provers
---

As described [here](https://kwarc.info/people/mkohlhase/submit/mmtelpi.pdf), MMT can generate ELPI provers from some inference rules described in MMT-LF.
Specifically, provers are successfully generated from natural deduction and tableau rules.
This directory contains various demos of the generated provers.
The generated ELPI code is located at `../export/lf-elpi/content/latin..NONE/`.


#### Running the examples

You need to have the following software installed:
- [ELPI](https://github.com/LPCIC/elpi)
- If you want to generated the ELPI code yourself, you need current development version of [MMT](https://uniformal.github.io//doc/setup/)

Due to [a bug](https://github.com/LPCIC/elpi/issues/49) in ELPI, `accumulate` can import rules several times.
This results in an exponential slow-down of the provers.
To circumvent this, the `accumulate.sh` script collects the relevant code into files in the `generated` folder.

With all this in place, you should be able to run the provers by calling e.g.
```elpi -no-tc pl_nd_backchaining.elpi```
and the entering the command `main.`.



