# MMT/LATIN2 Archive

This is the second generation of the *<u>L</u>ogic <u>At</u>las and <u>In</u>tegrator* (*LATIN*) Project: an effort to develop methods, techniques, and tools for interfacing logics and related formal systems.
See [\[CHK11-paper\]][CHK11-paper] and [\[CHK11-slides\]][CHK11-slides] for the original project description.
A more recent project description can be found at [\[RR-modlog\]][modlog-paper].

See [./CITATION](./CITATION) for how to cite.

## Building

<!-- TODO: comment out this in the future: First issue `git submodule init` and `git submodule update` in order for the submodule `lib/tptp-parser` to be cloned -->

### Building individual files (for endusers)

The `master` branch is supposed to already contain all build artifacts, hence there should be no need to build everything from scratch for end users.
End users can just modify files to their liking and build these individually, e.g., by using the [MMT IntelliJ Plugin](https://uniformal.github.io/doc/applications/intellij/).

However, if you modify large portions or face peculiar build errors (like ["no backend applicable", "invalid object"](https://github.com/UniFormal/uniformal.github.io/wiki/Errors
)), you might want to try rebuilding as follows.

### Building everything from scratch (for elaborate endusers / developers)

From the [MMT shell](https://uniformal.github.io/doc/applications/shell.html), run the following commands:

```shell
file <file system path to LATIN2>/build-omdoc.msl --noqueue
build MMT/LATIN2 lf-scala
build MMT/LATIN2 mmt-omdoc logic/drt/drt.mmt
build MMT/LATIN2 lf-scala logic/drt
build MMT/LATIN2 scala-bin
```

As of today (2021-11-08), it is expected that you see parsing or typechecking errors during the procedure above.
Most end users are not affected by them.

> **A note on build order:** The formalizations as well as Scala files in this archive require a specific build order. In particular, there are many circular dependencies between `.mmt` files themselves as well as between them and Scala files.
> Unfortunately, the MMT build system cannot deal with such complex dependency management at time of writing, hence the build order has to be manually prescribed.
> Furthermore, due to the circular dependencies, an iterative approach to building is necessary until – hopefully – an error-free fixpoint is reached.
> The build file [`build-omdoc.msl`](./build-omdoc.msl) in this archive accounts for both points.

If you don't know how to use the MMT shell, here's one way to open and initialize it:

1. Close all MMT instances, including *all* IntelliJ IDE projects (if you have the MMT plugin installed), even those not being MMT projects

   This is just a safety measure to ensure that really nothing interferes with our build process below.
2. Start the MMT shell: `java -jar mmt.jar`
3. If you don't have an `mmt.rc`\*, tell MMT about the location of your archives: `mathpath archive [root path of your archives]`, e.g. `mathpath archive ../../my-archives`

   Typically, the root path contains, besides this LATIN2 repository, also the [urtheories](https://gl.mathhub.info/MMT/urtheories) and [LFX](https://gl.mathhub.info/MMT/LFX) archives as (transitive) subdirectories.<br>
   \*) if you don't know about that file, you probably don't have one.

## Contributors

The current maintainer is [Florian Rabe][frabe].
A list of all current and previous contributors:

- [Florian Rabe][frabe]: created LATIN2 in year YYYY (TODO), maintaining and advising people contributing to it ever since 
- [Navid Roux][nroux]: contributed in years 2019 -- 2021 various formalizations  (incl. Curry Howard, translations in type theory), added documentary source code at various places, and integrated diagram operators (TODO: link to it) in their thesis (TODO: link to it) as to replace XYZ lines of code by a single macro invocation 
- [Dennis Müller][dmueller]: TODO
- [Annika Schmidt][aschmidt]: contributed in 2021 formalizations of set theory in their M.Sc. thesis (TODO: link to it), of translations from type to set theory, and completely reworked the build script

and various other [people of the kwarc research group](https://kwarc.info/people/).

## Bibliography

**\[CHK11\]**: Project Abstract: Logic Atlas and Integrator (LATIN), Mihai Codescu, Fulya Horozal, Michael Kohlhase, Till Mossakowski, Florian Rabe, 2011 <br>
               Intelligent Computer Mathematics, J. Davenport, W. Farmer, F. Rabe, J. Urban (eds.), pp. 289-291 , volume 6824 of Lecture Notes in Computer Science, Springer. [PDF][CHK11-paper], [Slides PDF][CHK11-slides].

<!-- Keep this in sync with the CITATION file, please -->

    @InProceedings{CodHorKoh:palai11,
      title = {Project Abstract: Logic Atlas and Integrator ({LATIN})},
      author = {Mihai Codescu and Fulya Horozal and Michael Kohlhase and Till Mossakowski and Florian Rabe},
      pages = {289--291},
      year = {2011},
      url = {https://kwarc.info/people/frabe/Research/CHKMR_latinabs_11.pdf},
      doi = {10.1007/978-3-642-22673-1_24},
      isbn = "978-3-642-22673-1",
      booktitle = {{Intelligent Computer Mathematics}},
      editor = {James Davenport and William Farmer and Florian Rabe and Josef Urban},
      number = {6824},
      series = {Lecture Notes in Computer Science},
      volume = {6824},
      publisher = {Springer Verlag},
      address = "Berlin, Heidelberg",

      abstract="LATIN aims at developing methods, techniques, and tools for interfacing logics and related formal systems. These systems are at the core of mathematics and computer science and are implemented in systems like (semi-)automated theorem provers, model checkers, computer algebra systems, constraint solvers, or concept classifiers. Unfortunately, these systems have differing domains of applications, foundational assumptions, and input languages, which makes them non-interoperable and difficult to compare and evaluate in practice."
    }

**[modlog]:** Modular Formalizations of Formal Systems, Florian Rabe, Navid Roux, 2021 (unpublished). [PDF][modlog-paper].

[CHK11-paper]: https://kwarc.info/people/frabe/Research/CHKMR_latinabs_11.pdf
[CHK11-slides]: https://kwarc.info/people/frabe/Research/slides/CHKMR_latinabs_11.pdf
[modlog-paper]: https://kwarc.info/people/frabe/Research/RR_modlog_21.pdf

[dmueller]: https://kwarc.info/people/dmueller/
[frabe]: https://kwarc.info/people/frabe/
[nroux]: https://kwarc.info/people/nroux/
[aschmidt]: https://kwarc.info/people/aschmidt/