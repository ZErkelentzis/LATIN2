package latin2.tptp

import info.kwarc.mmt.api.MPath
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.symbols.{Constant, PlainInclude}
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.lf.{ApplySpine, Lambda}
import latin2.sfol.CommonSymbols.DedList
import leo.datastructures.TPTP.{AnnotatedFormula, Comment, FOF, FOFAnnotated, Include, Problem}
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.ExistentialQuantification.uexists
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.UniversalQuantification.uforall

import scala.collection.mutable.ArrayBuffer

object FOLExporter {
  var comments = Map[String, Seq[Comment]]()
  var currentFormulaComments = Seq[Comment]()
  def combineStubs(p: MPath, ctx: Context, t: Term)(implicit ctrl: Controller): Problem = {
    var includes = ArrayBuffer[MPath]()
    val formulas = ArrayBuffer[AnnotatedFormula]()

    val decls = ctrl.getTheory(p).getDeclarations
    //for (x <- ctrl.getTheory(p.module).getDeclarations.takeWhile(x => x.parent == p)) {
    for (x <- decls.take(decls.length - 1)) {
      x match {
        case PlainInclude(t) => includes += t._1
        case c: Constant => formulas ++= translate_constant(c)
      }
    }
    val axioms = ctx.mapVarDecls {
      case (ctx, vd: VarDecl) =>
        translate_var_decl(vd, ctx)(ctrl)
    }.flatten.distinct

    formulas ++= axioms

    val ded(conjecture) = t
    formulas += FOFAnnotated("conjecture", "conjecture", FOF.Logical(translate_formula(conjecture)), None)
    add_formula_comment("conjecture")

    val tptp_exporter = ctrl.extman.get(classOf[TPTPExporter]).head

    val ret = Problem(includes.map(i => tptp_exporter.translate_include(p.module, i)).toSeq, formulas.toList, comments)
    comments = Map()
    ret
  }


  def exportStub(theory: Theory)(implicit ctrl: Controller): Problem = {
    export_theory(theory, Nil)
  }

  def export_theory(theory: Theory, includes: Seq[Include])(implicit ctrl: Controller): Problem = {
    val formulas = translate_theory(theory).map(x => if (x.role == "") {
      x.copy(role = "axiom")
    } else x)
    val ret = Problem(includes, formulas, comments)
    comments = Map()
    ret
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[FOFAnnotated] = {
    theory.getConstants.flatMap(translate_constant)
  }

  def translate_var_decl(vd: VarDecl, ctx: Context)(implicit ctrl: Controller): Option[FOFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = vd.tp.map(ctrl.simplifier(_, simplicationUnit))

    newTp match {
      case Some(ded(formula)) =>
        Some(FOFAnnotated(vd.name.toString, "", FOF.Logical(translate_formula(formula)), None))
      case _ => None
    }
  }

  def translate_constant(c: Constant)(implicit ctrl: Controller): Option[FOFAnnotated] = {
    val ctx = Context(c.path.module)
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = c.tp.map(ctrl.simplifier(_, simplicationUnit))

    newTp match {
      case Some(ded(formula)) =>
        Some(FOFAnnotated(c.name.toString, "", FOF.Logical(translate_formula(formula)), None))
      case _ => None
    }
  }

  // Needs to be added after each Annotated construction involving `translate_formula`
  def add_formula_comment(name: String) = {
    if (currentFormulaComments.nonEmpty) {
      comments += (name -> currentFormulaComments)
      currentFormulaComments = Seq()
    }
  }


  def translate_formula(t: Term): FOF.Formula = t match {
    case uforall(Lambda(v, _, body)) =>
      FOF.QuantifiedFormula(
        FOF.!,
        Seq(
          "V_" + v.toPath
        ),
        translate_formula(body)
      )
    case uexists(Lambda(v, _, body)) =>
      FOF.QuantifiedFormula(
        FOF.?,
        Seq(
          "V_" + v.toPath
        ),
        translate_formula(body)
      )

    case and(left, right) =>
      FOF.BinaryFormula(FOF.&, translate_formula(left), translate_formula(right))
    case or(left, right) =>
      FOF.BinaryFormula(FOF.|, translate_formula(left), translate_formula(right))
    case impl(left, right) =>
      FOF.BinaryFormula(FOF.Impl, translate_formula(left), translate_formula(right))
    case equiv(left, right) =>
      FOF.BinaryFormula(FOF.<=>, translate_formula(left), translate_formula(right))
    case not(arg) =>
      FOF.UnaryFormula(FOF.~, translate_formula(arg))

    case OMID(f) =>
      FOF.AtomicFormula(f.name.toString, Nil)

    case OMV(x) =>
      FOF.AtomicFormula(x.toString, Nil)

    case ApplySpine(OMID(f), args) =>
      FOF.AtomicFormula(f.name.toString, args.map(translate_term))

  }

  def translate_term(t: Term): FOF.Term = t match { //FIXME: MatchErrors happening here cause of lambdas
    case ApplySpine(OMID(f), args) =>
      // f: GlobalName, args: List[Term]
      FOF.AtomicTerm(f.name.toString, args.map(translate_term))

    case OMID(f) =>
      FOF.AtomicTerm(f.name.toString, Nil)

    //case OMV(x) =>
    //  // x: LocalName
    //  Var(x.name.toString)
    case OMV(x) =>
      // x: LocalName
      FOF.Variable("V_" + x.toString)
  }
}
