# Accompanying Formalizations for the paper [“Systematic Translation of Formalizations of Type Theory from Intrinsic to Extrinsic Style”](https://kwarc.info/people/frabe/Research/RR_softening_21.pdf)

[“Systematic Translation of Formalizations of Type Theory from Intrinsic to Extrinsic Style”](https://kwarc.info/people/frabe/Research/RR_softening_21.pdf) by Florian Rabe and Navid Roux is a paper currently under review.

This is a self-contained formalization closely following the submitted paper.

Many parts for this formalization have been extracted and adapted from the surrounding [LATIN2 archive](https://gl.mathhub.info/MMT/LATIN2/-/tree/devel) to be closer to the paper and easier to understand.
For example, LATIN2 employs much more fine-grained theory graphs split over many directories and files and uses MMT features not discussed in the paper.

## Usage

1. Get the latest MMT development binary
   1. Go to [our GitHub Actions CI](https://github.com/UniFormal/MMT/actions?query=branch%3Adevel+event%3Apush+is%3Acompleted) and click on the top workflow run (even if it shows a red X for failure)
   2. Download `mmt.jar` from there (you need to have a GitHub account due to GitHub policies for binaries from GitHub Actions)
2. Create a new directory on your file system (e.g., `archives/MMT`) and clone the following archives of formalization:
   1. MMT/urtheories: `git clone -b devel https://gl.mathhub.info/MMT/urtheories.git`
   2. MMT/LFX: `git clone -b devel https://gl.mathhub.info/MMT/LFX.git`
   3. MMT/LATIN2:  `git clone -b devel https://gl.mathhub.info/MMT/LATIN2.git`
3. Start the MMT shell via `java -jar mmt.jar`.
   1. Deny running the setup
   2. Run `mathpath archive archives/MMT`
   3. `build MMT/LATIN2 mmt-omdoc casestudies/softening2021/1-basics.mmt`
   4. `build MMT/LATIN2 mmt-omdoc casestudies/softening2021/2-hardtyped-library.mmt`
   5. `build MMT/LATIN2 mmt-omdoc casestudies/softening2021/3-softening.mmt` 
4. ?