# MMT/LATIN2 Archive

This is the second generation of the LATIN atlas, an effort to "develop[...] methods, techniques, and tools for interfacing logics and related formal systems." \[[CHK11 paper][CHK11-paper], [CHK11 slides][CHK11-slides]\]


## Building

### Building individual files for endusers

The master branch is supposed to already contain all build artifacts, hence there should be no need to build everything from scratch for end users.
End users can just modify files to their liking and build these individually, e.g. by using the [MMT IntelliJ Plugin](https://uniformal.github.io/doc/applications/intellij/).

However, if you modify large portions or face peculiar build errors (like ["no backend applicable", "invalid object"](https://github.com/UniFormal/uniformal.github.io/wiki/Errors
)), you might want to try rebuilding as follows.

### Complete Rebuilding for elaborate endusers / developers

<<<<<<< HEAD
> **A note on build order:** The formalizations in this archive require a specific build order. In particular, many `.mmt` files have circular dependencies.
=======
> **A note on build order:** The formalizations as well as Scala files in this archive require a specific build order. In particular, there are many circular dependencies between `.mmt` files themselves as well as between them and Scala files.
>>>>>>> devel
> Unfortunately, the MMT build system cannot deal with such complex dependency management at time of writing, hence the build order has to be manually prescribed.
> Furthermore, due to the circular dependencies, an iterative approach to building is necessary until – hopefully – an error-free fixpoint is reached.
> The build file [`build-omdoc.msl`](./build-omdoc.msl) in this archive accounts for both points.

Rebuilding amounts to the following:


1. Close all MMT instances, including *all* IntelliJ IDE projects (if you have the MMT plugin installed), even those not being MMT projects

   This is just a safety measure to ensure that really nothing interferes with our build process below.
2. Start the MMT shell: `java -jar mmt.jar`
3. If you don't have an `mmt.rc`\*, tell MMT about the location of your archives: `mathpath archive [root path of your archives]`, e.g. `mathpath archive ../../my-archives`

   Typically, the root path contains, besides this LATIN2 repository, also the [urtheories](https://gl.mathhub.info/MMT/urtheories) and [LFX](https://gl.mathhub.info/MMT/LFX) archives as (transitive) subdirectories.<br>
   \*) if you don't know about that file, you probably don't have one.
4. Run the build file: `file [path to LATIN2 archive]/build-omdoc.msl`
5. Possibly repeat step 3 once more

You probably still get errors in steps 3 and 4. Try ignoring them and just continuing with what you wanted to do initially.
For example, if you wanted to initially build `pl.mmt`, but that failed with peculiar errors, try building that file individually now, e.g. from within IntelliJ with the MMT plugin.
Ideally, that should build errorfree now.

## Maintainers / Contact

- [Navid Roux](https://kwarc.info/people/nroux/) (currently responsible for building and making releases of LATIN2, advised by Florian Rabe)
- [Florian Rabe](https://kwarc.info/people/frabe/) (responsible for LATIN2 in general)


## Bibliography

**\[CHK11\]**: Project Abstract: Logic Atlas and Integrator (LATIN), Mihai Codescu, Fulya Horozal, Michael Kohlhase, Till Mossakowski, Florian Rabe, 2011 <br>
               Intelligent Computer Mathematics, J. Davenport, W. Farmer, F. Rabe, J. Urban (eds.), pp. 289-291 , volume 6824 of Lecture Notes in Computer Science, Springer. [PDF][CHK11-paper], [Slides PDF][CHK11-slides].

    @inproceedings{CHKMR:latinabs:11,
      author = "M. Codescu and F. Horozal and M. Kohlhase and T. Mossakowski and F. Rabe",
      title = "{Project Abstract: Logic Atlas and Integrator (LATIN)}",
      year = "2011",
      pages = "289--291",
      booktitle = "Intelligent Computer Mathematics",
      editor = "J. Davenport and W. Farmer and F. Rabe and J. Urban",
      publisher = "Springer"
    }


[CHK11-paper]: https://kwarc.info/people/frabe/Research/CHKMR_latinabs_11.pdf
[CHK11-slides]: https://kwarc.info/people/frabe/Research/slides/CHKMR_latinabs_11.pdf