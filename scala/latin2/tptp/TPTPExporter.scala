package latin2.tptp

import info.kwarc.mmt.api.{CPath, GeneralError, GlobalName, MPath, RuleSet, StructuralElement}
import info.kwarc.mmt.api.archives.BuildTask
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.{Context, Term}
import info.kwarc.mmt.api.presentation.{RenderingHandler, StructurePresenter}
import info.kwarc.mmt.api.proving.{AutomatedProver, ProvingUnit}
import info.kwarc.mmt.api.utils.FilePath
import leo.datastructures.TPTP.{Include, Problem}
import lf.{FOL, FOLEQ, FOLEQDesc, FOLEQDescND, FOLEQND, FOLND, HOL, SFOL, SFOLEQ, SFOLEQND, SFOLND}

import scala.sys.process.Process

class TPTPExporter extends StructurePresenter with AutomatedProver { //TODO: does TPTPExporter have to be class (MMT Extension)
  override def apply(e : StructuralElement, standalone: Boolean = false)(implicit rh : RenderingHandler): Unit = {}

  /** a string identifying this build target, used for parsing commands, logging, error messages */
  override def key: String = "tptp"

  override val outExt: String = "ax"

  override def exportTheory(thy : Theory, bf: BuildTask): Unit = {
    //TODO: check if FOL and SFOL at the same time

    var output_string = ""
    if (controller.library.hasImplicit(HOL._path, thy.path)) {
      println("detected HOL")
      output_string = HOLExporter.exportStub(thy)(controller).pretty + "\n"
    } else if (controller.library.hasImplicit(SFOL._path, thy.path)) {
      println("detected SFOL")
      output_string = SFOLExporter.exportStub(thy)(controller).pretty + "\n"
    } else if (controller.library.hasImplicit(FOL._path, thy.path)) {
      println("detected FOL")
      output_string = FOLExporter.exportStub(thy)(controller).pretty + "\n"
    } else {
      println("no known Logic detected")
    }
    if (!output_string.isEmpty) {
      outputTo(getOutFileForModule(thy.path).get) {
        rh(output_string)
      }
    }

  }

  def combineStubs(p: MPath, ctx: Context, t: Term)(implicit ctrl: Controller): Option[Problem] = {
    if (controller.library.hasImplicit(HOL._path, p)) {
      Some(HOLExporter.combineStubs(p, ctx, t))
    } else if (controller.library.hasImplicit(SFOL._path, p)) {
      Some(SFOLExporter.combineStubs(p, ctx, t))
    } else if (controller.library.hasImplicit(FOL._path, p)) {
      Some(???)//FOLExporter.combineStubs(p, ctx, t)
    } else {
      log(GeneralError("no known Logic detected"))
      None
    }
  }
  def translate_include(home_path: MPath, in: MPath) : Include = {
    val home = getOutFileForModule(home_path).get
    val include = home.relativize(getOutFileForModule(in).get).toString
    ((include, (Seq(), Seq())))
  }

  def exportProblem(problem: Problem, path: MPath) : String = {
    val file_path = getOutFileForModule(path).get.setExtension("p")
    outputTo(file_path) {
      rh(problem.pretty)
    }
    file_path.toString
  }

  def callExternalATP(path: String)(implicit  ctrl: Controller) = {
    println(s"""java -jar ${sys.env("LEO3")} $path """)
    val pb = Process(s"""java -jar ${sys.env("LEO3")} $path """)
    val result = pb.!!
    println(result)

  }

  def callInternalATP(path: String)(implicit  ctrl: Controller) = {
    leo.Main.main(Array(path))
  }

  /**
    * tries to prove a proof obligation automatically
    *
    * @param rules  the proof rules to use
    * @param levels the depth of the breadth-first searches
    * @return true if the goal was solved and possibly a proof term
    */
  override def apply(pu: ProvingUnit, rules: RuleSet, levels: Int): (Boolean, Option[Term]) = {
    val mod = MPath(pu.component.get.parent.toTriple._1.get, pu.component.get.parent.toTriple._2.get)
    val problem = combineStubs(mod, pu.context, pu.tp)(this.controller)
    val result = problem.map(exportProblem(_, mod)).map(path => callInternalATP(path)(this.controller)).isDefined
    log("ATP Result: " + result)
    (result, None)
  }

}
