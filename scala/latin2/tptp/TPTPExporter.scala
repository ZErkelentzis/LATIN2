package latin2.tptp

import info.kwarc.mmt.api.archives.BuildTask
import info.kwarc.mmt.api.checking.UnknownTerm
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.{Context, OMSemiFormal, Term, Text}
import info.kwarc.mmt.api.presentation.{RenderingHandler, StructurePresenter}
import info.kwarc.mmt.api.proving.{AutomatedProver, ProvingUnit}
import info.kwarc.mmt.api.utils.File
import info.kwarc.mmt.api.utils.File.read
import info.kwarc.mmt.api.{GeneralError, MPath, RuleSet, StructuralElement}
import leo.datastructures.TPTP.{Include, Problem}
import lf.{FOL, HOL, SFOL}

import java.security.DigestInputStream
import scala.sys.process.Process

class TPTPExporter extends StructurePresenter with AutomatedProver { //TODO: does TPTPExporter have to be class (MMT Extension)
  override def apply(e : StructuralElement, standalone: Boolean = false)(implicit rh : RenderingHandler): Unit = {}

  /** a string identifying this build target, used for parsing commands, logging, error messages */
  override def key: String = "tptp"

  override val outExt: String = "ax"

  var atpEnabled = true

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

  def callInternalATP(path: String): (Boolean, Option[String]) = {
    import java.io.{ByteArrayOutputStream, PrintStream}
    val baos = new ByteArrayOutputStream
    val printStream = new PrintStream(baos)
    //System.setOut(printStream)
    val err = System.err
    System.setErr(printStream)
    Console.withOut(printStream) {
      //Console.withErr(printStream) {
        leo.Main.main(Array(path, "-p"))
      //}
    }
    System.setErr(err)
    //println("OUT/ERR:\n"+baos.toString)
    parseResult(baos.toString)
  }

  def parseResult(log: String): (Boolean, Option[String]) = {
    val lines = log.split("\\R")
    val statusIndex = lines.indexWhere((line) => line.startsWith("% SZS status"))
    val status = lines(statusIndex).stripPrefix("% SZS status ").startsWith("Theorem")
    val proofIndexStart = lines.indexWhere((line) => line.startsWith("% SZS output start Refutation")) + 1
    val proofIndexEnd = lines.indexWhere((line) => line.startsWith("% SZS output end Refutation")) - 1
    val proofLines = Option(lines.slice(proofIndexStart, proofIndexEnd)).filter(_.nonEmpty)
    val proof = proofLines.map((lines) => lines.slice(proofIndexStart, proofIndexEnd).mkString("\n"))
    (status, proof)
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

    //TODO: build stubs, before combining
    val problem_path = combineStubs(mod, pu.context, pu.tp)(this.controller) match {
      case Some(problem) => exportProblem(problem, mod)
      case None => return (true, None)
    }

    //check if proof cached
    val proof_path = getOutFileForModule(mod).get.setExtension("proof.tptp")
    val cached = if (proof_path.exists()) {
      import java.io.BufferedReader
      import java.io.FileReader
      val br = new BufferedReader(new FileReader(proof_path))
      val first_line = br.readLine
      if (first_line == metadata_line(problem_path)) {
        true
      } else {
        false
      }
    } else {
      false
    }

    if (cached) {
      println("Proof to '" + mod + "' cached. Skipping..")
      return (true, None)
    };

    val result = callInternalATP(problem_path)

    //Caching proof
    result._2 match {
      case Some(proof) => outputTo(proof_path) {
        rh(metadata_line(problem_path) + "\n" + proof)
      }
    }

    (result._1, result._2.map(proof => UnknownTerm(OMSemiFormal(Text("tptp", proof)))))
  }

  def metadata_line(problem_path: String): String = {
    import java.security.MessageDigest
    import java.io.FileInputStream
    val buffer = new Array[Byte](8192)
    val md = MessageDigest.getInstance("SHA-256")
    val dis = new DigestInputStream(new FileInputStream(problem_path), md)
    try { while (dis.read(buffer) != -1) { } } finally { dis.close() }

    "% " + md.digest.map("%02x".format(_)).mkString
  }
}
