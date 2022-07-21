package latin2.tptp

import info.kwarc.mmt.api.{GlobalName, MPath}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.lf.{ApplySpine, Lambda}
import leo.datastructures.TPTP.Comment.{CommentFormat, CommentType}
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

class FOLExporter  extends logicExporter {
  val priority: Int = 1
  val theoryPath: info.kwarc.mmt.api.MPath = lf.DHOL._path
  def tptp_conjecture(conj: info.kwarc.mmt.api.objects.Term) = FOFAnnotated("conjecture", "conjecture", FOF.Logical(translate_formula(conj)), None)

  def translate_theory(theory: Theory)(implicit ctrl: Controller) = {
    theory.getConstants.flatMap(translate_constant)
  }

  def translate_var_decl(vd: VarDecl, ctx: Context)(implicit ctrl: Controller): Option[FOFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandConDefs = true, expandVarDefs = true, fullRecursion = true)

    val newTp = vd.tp.map(ctrl.simplifier(_, simplicationUnit))

    newTp match {
      case Some(ded(formula)) =>
        Some(FOFAnnotated(vd.name.toString, "", FOF.Logical(translate_formula(formula)), None))
      case _ => None
    }
  }

  /*override def translate_constant(c: Constant)(implicit ctrl: Controller) = {
    val ctx = Context(c.path.module)
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = c.tp.map(ctrl.simplifier(_, simplicationUnit))

    newTp match {
      case Some(ded(formula)) =>
        List(FOFAnnotated(c.name.toString, "", FOF.Logical(translate_formula(formula)), None))
      case _ => Nil
    }
  }*/

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

    case default =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default)
      FOF.AtomicTerm("$true", Nil)
  }

  /**
   *
   * @param path
   * @param tp
   * @param df
   * @param ctx
   * @param ctrl
   * @return
   */
  override def translate_decl(path: GlobalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[AnnotatedFormula] = {
    val ctx = Context(path.module)
    val simplicationUnit = SimplificationUnit(ctx, expandConDefs = true, expandVarDefs = true, fullRecursion = true)

    val newTp = tp.map(ctrl.simplifier(_, simplicationUnit))

    newTp match {
      case Some(ded(formula)) =>
        List(FOFAnnotated(path.name.toString, "", FOF.Logical(translate_formula(formula)), None))
      case _ => Nil
    }
  }
}
