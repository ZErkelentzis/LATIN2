package latin2.tptp

import info.kwarc.mmt.api.StructuralElement
import info.kwarc.mmt.api.archives.BuildTask
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.presentation.{RenderingHandler, StructurePresenter}
import lf.{FOL, FOLEQ, FOLEQDesc, FOLEQDescND, FOLEQND, FOLND, SFOL, SFOLEQ, SFOLEQND, SFOLND}

class TPTPExporter extends StructurePresenter {
  override def apply(e : StructuralElement, standalone: Boolean = false)(implicit rh : RenderingHandler): Unit = {}

  /** a string identifying this build target, used for parsing commands, logging, error messages */
  override def key: String = "tptp"

  override val outExt: String = "ax"

  override def exportTheory(thy : Theory, bf: BuildTask): Unit = {
    //TODO: check if FOL and SFOL at the same time

    outputTo(getOutFileForModule(thy.path).get) {
      if (controller.library.hasImplicit(FOL._path, thy.path)) {
        //println("detected FOL")
        //val root = getOutFileForModule(thy.path).get
        //val includes = thy.getIncludesWithoutMeta.flatMap(in => { //TODO: extract
        //  if (controller.library.hasImplicit(in, FOL._path)) {
        //    None
        //  } else {
        //    Some(root.relativize(getOutFileForModule(in).get).toString, Nil)
        //  }
        //})
        //rh(new FOLExporter().export_theory(thy, includes)(controller).pretty)
        rh(new FOLExporter().export_theory_flattened(thy)(controller).pretty)
      } else if (controller.library.hasImplicit(SFOL._path, thy.path)) {
        println("detected SFOL")
        //val root = getOutFileForModule(thy.path).get
        //val includes = thy.getIncludesWithoutMeta.flatMap(in => { //TODO: extract
        //  if (controller.library.hasImplicit(in, SFOL._path)) {
        //    None
        //  } else {
        //    Some(root.relativize(getOutFileForModule(in).get).toString, Nil)
        //  }
        //})
        //rh(new SFOLExporter().export_theory(thy, includes)(controller).pretty)
        rh(new SFOLExporter().export_theory_flattened(thy)(controller).pretty)
      } else {
        println("no LF detected")
      }
    }
  }

}
