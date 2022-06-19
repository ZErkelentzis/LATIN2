package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.frontend.Extension
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.Context.context2list
import info.kwarc.mmt.api.objects.{Term, _}
import info.kwarc.mmt.api.symbols.{Constant, PlainInclude}
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{GlobalName, LocalName, MPath}
import info.kwarc.mmt.lf._
import latin2.sfol.SFOLPatterns.{FuncDecl, PredDecl, TypeDecl}
import leo.datastructures.TPTP.Comment.{CommentFormat, CommentType}
import leo.datastructures.TPTP.THF.FunTyConstructor
import leo.datastructures.TPTP._
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.SFOLEQ.notequal
import lf.SimpleFunctions.{simpapply, simplambda}
import lf.TypedEquality.tequal
import lf.TypedExistentialQuantification.texists
import lf.TypedTerms.tm
import lf.TypedUniversalQuantification.tforall
import lf.{Falsity, InternalPropositions, SimpleFunctionTypes, Truth}

import scala.collection.mutable.ArrayBuffer
import ExporterUtil._

object DHOLExporter {
  var comments = Map[String, Seq[Comment]]() //TODO: use this instead of returning comments, don't forget to clear after each run
  var currentFormulaComments = Seq[Comment]()

 def export_theory(theory: Theory)(implicit ctrl: Controller): Problem = {
    val formulas = translate_theory(theory).map(x => if (x.role == "") {
      x.copy(role = "axiom")
    } else x)
    val ret = Problem(Nil, formulas, comments)
    // clear global variable before the exporter is called on the next theory
    comments = Map()
    ret
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[THFAnnotated] = {
    // TODO: typecheck while translating
    theory.getConstants.flatMap { c => translate_decl(c.path, c.tp, c.df, Context(c.path.module))}
  }

  def funty_builder(in: List[THF.Formula], out: THF.Formula) = in.foldRight(out)((g, arg) => THF.BinaryFormula(FunTyConstructor, g, arg))

  def translate_decl(path: GlobalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = tp.map(ctrl.simplifier(_, simplicationUnit))

    val name = path.name

    newTp match {
      case Some(lf.Types.tp.term) | Some(Univ(1)) | Some(TypeDecl(Nil)) => // declaration of new simple type
        List(
          THFAnnotated("type_" + name.toString, "type", THF.Typing(translated_type_name(name), THFType), None)
          // Should we also generate typing predicate for simple types?
        )
      case Some(piTp@Pi(_, _, _)) => unapplyPi(piTp) match {
        case Some((dependentArgs, bdy)) if bdy == Univ(1) || bdy == lf.Types.tp.term => { // a dependent type declaration
          val tpDecl = THFAnnotated("type_" + name.toString, "type",
            THF.Typing(translated_type_name(name), THFType), None)
          val translated_args = dependentArgs.map(_.toTerm) :+translated_type_path(path)
          val predTp = funty_builder(translated_args map translate_term, THFBool)
          val tpPred = THFAnnotated(name.toString + "_pred", "type",
            THF.Typing(translated_pred_name(name), predTp), None)
          List(tpDecl, tpPred)
        }
        case _ => ??? // impossible
      }
      case Some(depFun@lf.DependentFunctionTypes.depfun(_, _)) => unapplyDepFun(depFun) match {// declaration of function
        case Some((dependentArgs, ret)) => {
          val funDecl = THFAnnotated("type_" + name.toString, "type",
            THF.Typing(translated_fun_name(name), translate_type(Pi(dependentArgs, ret))), None)
          val retPred = typing_pred(Pi(dependentArgs, ret))
          val tpAx = THFAnnotated(name.toString + "_ax", "axiom",
            THF.Logical(retPred(translated_fun_path(path))), None)
          List(funDecl, tpAx)
        }
        case _ => ??? // shouldn't happen either
      }
      case Some(ftp@ApplyGeneral(OMS(p), args)) => { // declaration of constant
        val constDecl = THFAnnotated("type_" + name.toString, "type",
          THF.Typing(translated_fun_name(name), translate_type(ftp)), None)
        val retPred = typing_pred(OMS(p))
        val tpAx = THFAnnotated(name.toString + "_ax", "axiom",
          THF.Logical(retPred(translated_fun_path(path))), None)
        List(constDecl, tpAx)
      }
      case Some(lf.Proofs.ded(ax)) => List(THFAnnotated(name + "_ax", "axiom",
        THF.Logical(translate_term(ax)), None))
      case _ => ??? // should be impossible
    }
  }

  // Needs to be added after each Annotated construction involving `translate_formula`
  def add_formula_comment(name: String) = {
    if (currentFormulaComments.nonEmpty) {
      comments += (name -> currentFormulaComments)
      currentFormulaComments = Seq()
    }
  }

  def translate_term(t: Term): THF.Formula = t match {
    case Lambda(v, ty, body) => THF.QuantifiedFormula(THF.^, Seq((translate_var(v), translate_term(ty))), translate_term(body))
    case simplambda(_, _, f) => translate_term(f)
    case simpapply(_, _, f, x) => translate_term(ApplySpine(f, x))

    case SimpleFunctionTypes.simpfun(a, b) => funty_builder(List(translate_term(a)), translate_term(b))
    case InternalPropositions.bool.term => THFBool
    //TODO: Add term -> $i
    // TODO: product types, etc. still needed

    case tforall((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.!,
        Seq(
          (translate_var(v), translate_term(ty))
        ),
        THF.BinaryFormula(THF.Impl, typing_pred(ty)(OMV(v)), translate_term(body))
      )
    case texists((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.?,
        Seq(
          (translate_var(v), translate_term(ty))
        ),
        THF.BinaryFormula(THF.Impl, typing_pred(ty)(OMV(v)), translate_term(body))
      )
    case tforall(ty, body) =>
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
      translate_term(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case texists(ty, body) =>
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
      translate_term(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case and(left, right) =>
      THF.BinaryFormula(THF.&, translate_term(left), translate_term(right))
    case or(left, right) =>
      THF.BinaryFormula(THF.|, translate_term(left), translate_term(right))
    case impl(left, right) =>
      THF.BinaryFormula(THF.Impl, translate_term(left), translate_term(right))
    case equiv(left, right) =>
      THF.BinaryFormula(THF.<=>, translate_term(left), translate_term(right))
    case tequal(ty, left, right) => {
      THF.BinaryFormula(THF.Eq, translate_term(left), translate_term(right))
    }
    case notequal(ty, left, right) => {
      THF.BinaryFormula(THF.Neq, translate_term(left), translate_term(right))
    }
    case not(arg) =>
      THF.UnaryFormula(THF.~, translate_term(arg))

    case Truth._true(()) =>
      THF.FunctionTerm("$true", Nil)

    case Falsity._false(()) =>
      THF.FunctionTerm("$false", Nil)

    case OMID(f) =>
      THF.FunctionTerm("t_" + f.name.toString, Nil)

    case OMV(x) =>
      THF.Variable("V_" + x.toString)

    case ApplySpine(f, args) => args.map(translate_term).foldLeft(translate_term(f))((g, arg) => THF.BinaryFormula(THF.App, g, arg))

    case default =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default)
      THF.FunctionTerm("$true", Nil)
    //return (
    //  THF.FunctionTerm("$true", Nil),
    //  List(Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default))
    //) //FIXME: exception when unknown term or op, example "0" instead of "zero" or "=" instead of "=ͭ"
  }

  def translate_type(t: Term): THF.Formula = t match {
    case depFun@lf.DependentFunctionTypes.depfun(_, _) => {
      val Some((depArgs, bdy)) = unapplyDepFun(depFun)
      translate_type(Pi(depArgs, bdy))
    }
    case Pi(n, tp, ret) => funty_builder(List(translate_type(tp)), translate_type(ret))
    case ApplySpine(tp, _) => translate_type(tp)
    case OMS(gn) => THF.FunctionTerm(translated_type_path(gn).path.name.toString, Nil)
  }

  def typing_pred(t:Term): Term => THF.Formula = {
    {x:Term =>
      t match {
        case lf.Booleans.bool(()) => ???
        case OMS(p) => translate_term(Truth._true()) // ignoring trivial typing predicates of simple types
        // THF.BinaryFormula(THF.App, THFOMS(translated_pred_path(p)), translate_term(x))
        case Pi(n, tp, ret) => THF.BinaryFormula(THF.App, typing_pred(tp)(OMV(n)), typing_pred(ret)(x))
        case ApplySpine(OMS(a), args) => translate_term(ApplySpine(OMS(translated_pred_path(a)), args:+x:_*))
        case _ => ???
      }
    }
  }
}

object ExporterUtil {
  def unapplyPi(tm: Term) : Option[(Context, Term)] = tm match {
    case Pi(n, tp, x) => unapplyPi(x) match {
      case Some((ctx, body)) => Some(OMV(n) % tp::ctx, body)
      case None => Some(OMV(n) % tp, x)
    }
    case _ => None
  }

  def unapplyDepFun(tm: Term) : Option[(Context, Term)] = tm match {
    case lf.DependentFunctionTypes.depfun(tp, Lambda(n, lf.TypedTerms.tm(tp2), x)) if tp == tp2 => unapplyDepFun(x) match {
      case Some((ctx, body)) => Some(OMV(n) % tp::ctx, body)
      case None => Some(OMV(n) % tp, x)
    }
    case _ => None
  }
  val THFType = THF.FunctionTerm("$tType", Nil)
  val THFBool = THF.FunctionTerm("$o", Nil)
  def THFOMS(p:GlobalName) = THF.FunctionTerm(p.name.toString, Nil)

  def translated_type_name(name:LocalName) = "t_" + name
  def translated_type_path(path:GlobalName) = OMS(path.module ? translated_type_name(path.name))

  def translated_fun_name(name:LocalName) = "t_" + name
  def translated_fun_path(path:GlobalName) = OMS(path.module ? translated_fun_name(path.name))

  def translated_pred_name(name:LocalName) = name.toString + "_pred"
  def translated_pred_path(path:GlobalName) = path.module ? translated_pred_name(path.name)

  def translate_var(n:LocalName) = "V_" + n
}