# Logic Atlas and Integrator

See https://uniformal.github.io/doc/archives/LATIN/LATIN2.html for background information, contributors, and publications.

# Viewing and Editing

The repository is hosted by gitlab at https://gl.mathhub.info/MMT/LATIN2 which includes syntax highlighting.

Additionally, the files can be viewed using MMT's semantic interaction services at https://mathhub.info/
But keep in mind that this system is a research product itself and not always stable.

To edit files and contribute, users can use any text editor, but it is recommended to use one of the [MMT IDEs](https://uniformal.github.io//doc/applications/ides.html).

# Building

## Master Branch

The `master` branch is co-released with the MMT system, i.e., the latest `master` branch of MMT can/should be used with the latest `master` of LATIN2.

Human-edited files are in the folders `source` (for MMT content) and `scala` (for supplementary Scala sources).
Other folders are produced by building and should not be committed.

To build, run the build script in this repository with MMT, e.g., by
```
PATH/TO/MMT/deploy/mmt file build.msl
```

Each folder contains its own build script, and these are called by the above.
To rebuild only the files in that folder, the respective build script can be used.

Individual files can be built via MMT or from within an MMT IDE.

## Individual files

If you modify large portions or face peculiar build errors (like ["no backend applicable", "invalid object"](https://github.com/UniFormal/uniformal.github.io/wiki/Errors
)), you might want to try rebuilding as follows.

## Whole archive

From the [MMT shell](https://uniformal.github.io/doc/applications/shell.html), run the following commands:

```shell
file <file system path to LATIN2>/build-omdoc.msl --noqueue
build MMT/LATIN2 lf-scala
build MMT/LATIN2 mmt-omdoc logic/drt/drt.mmt
build MMT/LATIN2 lf-scala logic/drt
build MMT/LATIN2 scala-bin
```

As of 2021-11-08, it is expected that you see parsing or typechecking errors during the procedure above.
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
