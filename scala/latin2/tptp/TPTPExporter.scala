package latin2.tptp

import info.kwarc.mmt.api._
import archives.{Archive, BuildTask, Dim}
import checking.UnknownTerm
import frontend.{Controller, Extension}
import info.kwarc.mmt.api
import modules.Theory
import objects.{Context, OMSReplacer, OMSemiFormal, OMV, Obj, Sub, Substitution, Term, Text, VarDecl}
import presentation.{RenderingHandler, StructurePresenter}
import proving.{AutomatedProver, ProvingUnit}
import symbols.{Constant, PlainInclude}
import utils.listmap
import leo.datastructures.TPTP.{AnnotatedFormula, Comment, FOFAnnotated, Include, Problem, TFFAnnotated, THFAnnotated}
import lf.Proofs.ded

import java.security.DigestInputStream
import java.util.Base64
import scala.collection.mutable.ArrayBuffer
import scala.io.Source
import scala.sys.process.Process

class TPTPExporter extends StructurePresenter with AutomatedProver { //TODO: does TPTPExporter have to be class (MMT Extension)
  override val priority: Int = 5

  override def apply(e : StructuralElement, standalone: Boolean = false)(implicit rh : RenderingHandler): Unit = {}

  /** a string identifying this build target, used for parsing commands, logging, error messages */
  override def key: String = "tptp"

  override val outExt: String = "ax"

  var atpEnabled = true
  // timeout for HOL ATP in seconds
  // can be re-set in apply method
  // this can be useful e.g. to set a shorter timeout for proof obligations generated during type-checking
  private var timeout = 60

  private def select_exporter(path: MPath): Option[logicExporter] = {
    val logicExporters = controller.extman.get(classOf[logicExporter])
    val applicableExporters = logicExporters filter {
      exp => controller.library.hasImplicit(exp.theoryPath, path)
    }

    applicableExporters match {
      case Nil =>
        println("no known Logic detected")
        None
      case List(exp) =>
        Some(exp)
      case exp::tl =>
        var maxPriority = exp.priority
        var used_exporter = exp
        tl foreach {lE =>
          if (lE.priority > maxPriority) {
            maxPriority = lE.priority
            used_exporter = lE
          }
        }
        Some(used_exporter)
    }
  }

  override def exportTheory(thy : Theory, bf: BuildTask): Unit = {
    //TODO: check if FOL and SFOL at the same time

    val logicExporter = select_exporter(thy.path)
    val output_string = logicExporter match {
      case Some(exporter) => exporter.export_theory(thy)(controller).pretty + "\n"
      case None => "% LOGIC UNSUPPORTED!\n"
    }
    if (output_string.nonEmpty) {
      outputTo(outFileForModule(thy.path)) {
        rh(output_string)
      }
    }
  }

  def combineStubs(p: MPath, ctx: Context, t: Term)(implicit ctrl: Controller): Option[Problem] = {
    val exporter = select_exporter(p)
    exporter match {
      case Some(exporter) => Some(exporter.combineStubs(p, ctx, t))
      case None =>
        log(GeneralError("no known Logic detected"))
        None
    }
  }
  def translate_include(home_path: MPath, in: MPath) : Include = {
    val home = outFileForModule(home_path)
    val include = home.relativize(outFileForModule(in)).toString
    ((include, (Seq(), Seq())))
  }

  private def defaultOutFileForModule(path: MPath) = {
    val latin2archive = controller.backend.getArchive("MMT/LATIN2").get
    val owningArchive = controller.backend.findOwningArchive(path) getOrElse {
      log ("Cannot find owning archive for file at "+path.toString+", using default archive LATIN2.")
      latin2archive
    }
    val outDim = Dim("export", key)
    (owningArchive / outDim / archives.Archive.MMTPathToContentPath(path.mainModule)).setExtension(outExt)
  }

  def outFileForModule(path: MPath) = getOutFileForModule(path).getOrElse(defaultOutFileForModule(path))

  private def exportProblem(problem: Problem, path: MPath, postfix: String) : String = {
    val file_path = outFileForModule(path).setExtension(postfix + "p")
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
    import java.io.{FileOutputStream, File}
    // TODO: Check if output already exists?
    val outputFile = new File(path+".log")
    val fos = new FileOutputStream(outputFile)
    Console.withOut(fos) {
      leo.Main.main(Array(path, "-p", "-t", timeout.toString, "-v", "1"))
    }
    fos.close()
    val outputLines = Source.fromFile(outputFile).getLines.toList
    parseResult(outputLines)
  }

  def parseResult(lines: List[String]): (Boolean, Option[String]) = {
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
   * @param rules   the proof rules to use
   * @param levels  the depth of the breadth-first searches
   * @return true if the goal was solved and possibly a proof term
   */
  override def apply(pu: ProvingUnit, rules: RuleSet, levels: Int): (Boolean, Option[Term]) = {
    this.apply(pu, rules, levels, this.timeout)
  }

  /**
    * tries to prove a proof obligation automatically within a given time limit
    *
    * @param rules  the proof rules to use
    * @param levels the depth of the breadth-first searches
    * @param timeout the timeout in seconds for the underlying HOL ATP
    * @return true if the goal was solved and possibly a proof term
    */
  def apply(pu: ProvingUnit, rules: RuleSet, levels: Int, timeout: Int): (Boolean, Option[Term]) = {
    val mod = MPath(pu.component.get.parent.toTriple._1.get, pu.component.get.parent.toTriple._2.get)
    this.timeout = timeout

    //TODO: build stubs, before combining
    val combinedStubs = combineStubs(mod, pu.context, pu.tp)(this.controller)
    // TODO: Can we always assume that the conjecture is the last formula, currently I think yes
    val conjectureNameO = combinedStubs.flatMap(_.formulas.lastOption).map(_.name)
    val pathPostfix = conjectureNameO.map(s => s + ".").getOrElse("")
    val problem_path = combinedStubs match {
      case Some(problem) => exportProblem(problem, mod, pathPostfix)
      case None => return (true, None)
    }

    //check if proof cached
    val proof_path = outFileForModule(mod).setExtension(pathPostfix + "proof.tptp")
    if (proof_path.exists()) {
      import java.io.BufferedReader
      import java.io.FileReader
      val br = new BufferedReader(new FileReader(proof_path))
      val first_line = br.readLine
      if (first_line == metadata_line(problem_path)) {
        println("Proof for problem in '" + proof_path.toString + "' cached. Skipping..")
        val proof = Iterator.continually(br.readLine()).takeWhile(_ != null).mkString
        return (true, Some(UnknownTerm(OMSemiFormal(Text("tptp", proof)))))
      }
    }

    val result = callInternalATP(problem_path)

    //Caching proof
    result._2 match {
      case Some(proof) => outputTo(proof_path) {
        rh(metadata_line(problem_path) + "\n" + proof)
      }
      case _ => log("Failed to prove conjecture.")
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
    "% " + Base64.getEncoder.encodeToString(md.digest)
  }
}

trait logicExporter extends Extension {
  var comments = Map[String, Seq[Comment]]()
  var currentFormulaComments = Seq[Comment]()

  // used to replace assumptions in the conjecture with references to declarations stating them
  var assSubstitution: List[Sub] = Nil
  // used for a definition expansions before the translation
  var definitionSubstituents: List[(GlobalName, Term)] = Nil

  // the following line causes definition expansion, replace with trivial replacer to disable
  def replacer: OMSReplacer = OMSReplacer.apply(listmap(definitionSubstituents, _))

  val theoryPath: MPath
  // to ensure the correct exporter is applied at the right time
  val priority: Int

  def export_theory(theory: Theory, includes: Seq[Include] = Nil)(implicit ctrl: Controller): Problem = {
    val formulas = translate_theory(theory).map {
      case THFAnnotated(nm, "", st, an) => THFAnnotated(nm, "axiom", st, an)
      case TFFAnnotated(nm, "", st, an) => TFFAnnotated(nm, "axiom", st, an)
      case FOFAnnotated(nm, "", st, an) => FOFAnnotated(nm, "axiom", st, an)
      case x => x
    }
    val ret = Problem(includes, formulas, comments)
    // clear global variable before the exporter is called on the next theory
    comments = Map()
    ret
  }

  // Needs to be added after each annotated construction translating a declaration
  def add_formula_comment(name: String) = {
    if (currentFormulaComments.nonEmpty) {
      comments += (name -> currentFormulaComments)
      currentFormulaComments = Seq()
    }
  }

  def tptp_conjecture(conj: Term): AnnotatedFormula

  def combineStubs(p: MPath, ctx: Context, t: Term)(implicit ctrl: Controller): Problem = {
    var includes = ArrayBuffer[MPath]()
    val formulas = ArrayBuffer[AnnotatedFormula]()

    val decls = ctrl.getTheory(p).getDeclarations
    //for (x <- ctrl.getTheory(p.module).getDeclarations.takeWhile(x => x.parent == p)) {
    for (x <- decls.take(decls.length - 1)) {
      x match {
        case PlainInclude(t) => includes += t._1
        case c: Constant =>
          val cReplaced = c.translate(replacer.toTranslator(), c.home, ctx)
          formulas ++= translate_constant(cReplaced)
      }
    }
    val assumptions = Context(ctx.variables.filter(_.feature.isEmpty):_*).mapVarDecls {//ctx.mapVarDecls {//
      case (ctx, vd: VarDecl) =>
        val vdRenamed = vd ^ assSubstitution
        val vdTr = replacer.toTranslator().applyVarDecl(ctx, vdRenamed)
        translate_var_decl(p.module, vdTr, ctx)
    }.flatten.distinct

    formulas ++= assumptions

    val ded(origConjecture) = t ^ assSubstitution
    val conjecture = replacer.toTranslator().apply(ctx, origConjecture)
    val conjStr = controller.presenter.asString(conjecture)
    log("Trying to prove "+conjStr+" using tptp exporter and HOL prover and in context: "+ctx.toStr(true))
    // if (conjecture != origConjecture)
    //  log("The unreplaced conjecture is: " + controller.presenter.asString(origConjecture))

    formulas += tptp_conjecture(conjecture)
    add_formula_comment("conjecture")

    /* log("The overall problem is: ")
    formulas foreach { form =>
      log(form.pretty)
    }
    log("\n\n") */

    val tptp_exporter = ctrl.extman.get(classOf[TPTPExporter]).head

    val ret = Problem(includes.map(i => tptp_exporter.translate_include(p.module, i)).toSeq, formulas.toList, comments)
    comments = Map()
    ret
  }

  def translate_var_decl(thy_path: MPath, vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[AnnotatedFormula] =
    translate_decl(thy_path ? vd.name, vd.tp, vd.df, ctx)

  def translate_constant(c: Constant)(implicit ctrl: Controller): List[AnnotatedFormula] =
    translate_decl(c.path, c.tp, c.df, Context(c.path.module))

  /**
   *
   * @param theory the theory to translate (includes are already flattened)
   * @param ctrl the controller
   *
   * @return the translation of the theory into TPTPFormulaKind
   * @effects if anythings unexpected happens during the translation of a declaration,
   * this should be documented as an additional comment in `currentFormulaComments`
   * then after each translation of a declaration `add_formula_comment` should be called
   */
  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[AnnotatedFormula]

  /**
   *
   * @param path
   * @param tp
   * @param df
   * @param ctx
   * @param ctrl
   * @return
   */
  def translate_decl(path: GlobalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[AnnotatedFormula]
}