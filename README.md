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
