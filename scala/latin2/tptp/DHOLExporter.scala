package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.frontend.Extension
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.Context.context2list
import info.kwarc.mmt.api.objects.{Term, _}
import info.kwarc.mmt.api.symbols.{Constant, PlainInclude}
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{ContentPath, GlobalName, LocalName, MPath}
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
import lf.TypedUniversalQuantification.tforall
import lf.{Falsity, InternalPropositions, SimpleFunctionTypes, Truth}

import info.kwarc.mmt.api
import latin2.tptp.ExporterUtil._

object DHOLExporter {
  var comments = Map[String, Seq[Comment]]() //TODO: use this instead of returning comments, don't forget to clear after each run
  var currentFormulaComments = Seq[Comment]()
  var pathMap: List[(GlobalName, String)] = Nil

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
    // We need to remember the constants and what kind of constants they are in order to work out the correct
    // paths in the translation and in order to define the typing predicate for booleans using case distinctions
    val decls = theory.getConstants
    var predDecls: List[(Constant, VarDecl)] = Nil

    decls flatMap { c =>
      val simplicationUnit = SimplificationUnit(Context(c.path.module), expandDefinitions = true, fullRecursion = true)
      val simplifiedTp = c.tp.map(ctrl.simplifier(_, simplicationUnit))

      val path = c.path
      val name = path.name

      val declTranslated = simplifiedTp match {
        case Some(lf.Types.tp.term) | Some(Univ(1)) | Some(TypeDecl(Nil)) =>
          pathMap ::= (path, translated_type_name(name))
          List(THFAnnotated("type_" + name.toString, "type", THF.Typing(translated_type_name(name), THFType), None))
        case Some(piTp@Pi(_, _, _)) => unapplyPi(piTp) match {
          case Some((dependentArgs, bdy)) if (bdy == Univ(1) || bdy == lf.Types.tp.term) =>
            pathMap ::= (path, translated_type_name(name))
            pathMap ::= (type_pred_path(path), type_pred_name(name))
            val tpDecl = THFAnnotated("type_" + name.toString, "type",
              THF.Typing(translated_type_name(name), THFType), None)
            val translated_args = dependentArgs.map(_.tp.get) :+ OMS(path)
            val predTp = funty_builder(translated_args map translate_type, THFBool)
            val tpPred = THFAnnotated(name.toString + "_pred", "type",
              THF.Typing(type_pred_name(name), predTp), None)
            List(tpDecl, tpPred)
          case _ => ??? // should be impossible
        }
        case Some(depFun@lf.DependentFunctionTypes.depfun(_, _)) => unapplyDepFun(depFun) match { // declaration of function
          case Some((dependentArgs, ret)) =>
            pathMap ::= (path, translated_fun_name(name))
            ret match {
              case lf.Booleans.bool(()) => predDecls ::= (c, dependentArgs.last)
              case _ => ()
            }
            val funDecl = THFAnnotated("type_" + name.toString, "type",
              THF.Typing(translated_fun_name(name), translate_type(Pi(dependentArgs, ret))), None)
            val retPred = typing_pred(Pi(dependentArgs, ret), ApplyGeneral(OMS(path), dependentArgs.map(_.toTerm)))
            lazy val tpAx = THFAnnotated(name.toString + "_ax", "axiom",
              THF.Logical(retPred), None)
            // no need to produce trivial axioms
            if (retPred != THFTrue) List(funDecl, tpAx) else List(funDecl)
        }
        case Some(ftp@ApplyGeneral(OMS(p), args)) =>
          pathMap ::= (path, translated_fun_name(name))
          val constDecl = THFAnnotated("type_" + name.toString, "type",
            THF.Typing(translated_fun_name(name), translate_type(ftp)), None)
          val retPred = typing_pred(OMS(p), OMS(path))
          val tpAx = THFAnnotated(name.toString + "_ax", "axiom",
            THF.Logical(retPred), None)
          List(constDecl, tpAx)
        case Some(lf.Proofs.ded(ax)) =>
          val tax = translate_term(ax)
          List(THFAnnotated(name + "_ax", "axiom", THF.Logical(tax), None))
        case Some(OMBINDC(binder, context, List(scopes))) if binder.toStr(true) == "unknown" => // this case shouldn't be necessary
          scopes match {
            case lf.Proofs.ded(ax) =>
              println(ax.toStr(true))
              val tax = translate_term(ax)
              List(THFAnnotated(name + "_ax", "axiom", THF.Logical(tax), None))
            case _ => ???
          }
        case _ => ??? // should be impossible
      }
      add_formula_comment(name.toString)
      declTranslated
    }
  }

  def funty_builder(in: List[THF.Formula], out: THF.Formula) = in.foldRight(out)((g, arg) => THF.BinaryFormula(FunTyConstructor, g, arg))

  // Needs to be added after each Annotated construction involving `translate_formula`
  def add_formula_comment(name: String) = {
    if (currentFormulaComments.nonEmpty) {
      comments += (name -> currentFormulaComments)
      currentFormulaComments = Seq()
    }
  }

  def translate_term(t: Term)(implicit predDecls: List[(Constant, VarDecl)] = Nil): THF.Formula = t match {
    case Lambda(v, ty, body) => THF.QuantifiedFormula(THF.^, Seq((translate_var(v), translate_term(ty))), translate_term(body))
    case simplambda(_, _, f) => translate_term(f)
    case simpapply(_, _, f, x) => translate_term(ApplySpine(f, x))

    case SimpleFunctionTypes.simpfun(a, b) => funty_builder(List(translate_type(a)), translate_type(b))
    case InternalPropositions.bool.term => THFBool
    //TODO: Add term -> $i
    // TODO: product types, etc. still needed

    case tforall((ty, Lambda(v, _, body))) =>
      val ass = typing_pred(ty, OMV(v))
      val concl = translate_term(body)
      THF.QuantifiedFormula(
        THF.!,
        Seq(
          (translate_var(v), translate_term(ty))
        ),
        ImplIfNonTriv(ass, concl)
      )
    case texists((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.?,
        Seq(
          (translate_var(v), translate_term(ty))
        ),
        ImplIfNonTriv(typing_pred(ty, OMV(v)), translate_term(body))
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
      THFTrue

    case Falsity._false(()) =>
      THFFalse

    case OMID(f) => THFTerm(api.utils.listmap(pathMap, f).getOrElse(default_name(f)))

    case OMV(x) =>
      THF.Variable(translate_var(x))

    case ApplySpine(f, args) => args.map(translate_term).foldLeft(translate_term(f))((g, arg) => THF.BinaryFormula(THF.App, g, arg))

    case OMA(OMV(i), args) if i.toString.startsWith("I/") && i.toString.stripPrefix("I/").toCharArray.forall(_.isDigit) =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Cannot resolve imlicit argument: " + t)
      THFTrue

    case default =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default)
      THFTrue
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
    case lf.TypedTerms.tm(tp) => translate_type(tp)
    case ApplySpine(tp, _) => translate_type(tp)
    case OMS(gn) => THFOMS(translated_type_path(gn).path)
  }

  def typing_pred(t:Term, x:Term)(implicit predDecls: List[(Constant, VarDecl)] = Nil): THF.Formula = {
    t match {
      /*
      bool? t :=
      forall x:a.a? r1 ... rn => a? y   if t == forall x:a r1 ... rn.F
      a? t1 && a? t2                    if t == t1 eq t2
      p a && p b                        if t == a => b
      a? x                              if t == p y and p:a -> bool in the theory
      true                              if t == b? r1 ... rn y for any dep. type b and arguments r1, ..., rn, y
       */
      case lf.Booleans.bool(()) => x match {
        case lf.TypedEquality.tequal(tp, r, s) => THF.BinaryFormula(THF.&, typing_pred(tp, r), typing_pred(tp, s))
        case lf.Implication.impl(r, s) => THF.BinaryFormula(THF.&, typing_pred(t, r), typing_pred(t, s))
        case tforall((ty, Lambda(v, _, body))) =>
          val ass = typing_pred(ty, OMV(v))
          val tpconcl = typing_pred(lf.Booleans.bool, body)
          THF.QuantifiedFormula(THF.!, Seq((translate_var(v), translate_term(ty))), ImplIfNonTriv(ass, tpconcl))
        case ApplySpine(OMS(p), args) => predDecls.find(_._1.path == p) match {
          case Some((c, arg)) => typing_pred(arg.tp.get(), arg.toTerm)
          case None => THFTrue // in this case p must be a typing predicate and there is nothing we have to check
        }
      }
      case OMS(p) => THFTrue // ignoring trivial typing predicates of simple types
      case Pi(n, tp, ret) =>
        def binder(t:THF.Formula): THF.Formula = THF.QuantifiedFormula(THF.?, Seq((translate_var(n), translate_term(tp))), t)
        // we can ignore trivial assumptions
        binder(ImplIfNonTriv(typing_pred(tp, OMV(n)), typing_pred(ret, x)))
      case ApplySpine(OMS(a), args) => (args:+x).map(translate_term)
        .foldLeft[THF.Formula](type_pred(a))((g, arg) =>
          THF.BinaryFormula(THF.App, g, arg))
      case _ => ??? // shouldn't happen
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
  def THFTerm(n:String) = THF.FunctionTerm(n, Nil)
  val THFType = THFTerm("$tType")
  val THFBool = THFTerm("$o")
  val THFTrue = THFTerm("$true")
  val THFFalse = THFTerm("$false")
  def THFOMS(p:ContentPath) = THF.FunctionTerm(p.name.toString, Nil)
  def ImplIfNonTriv(ass: THF.Formula, concl: THF.Formula) =
    if (ass == THFTrue) concl else THF.BinaryFormula(THF.Impl, ass, concl)

  def translated_type_name(name:LocalName) = "t_" + name
  def translated_type_path(path:GlobalName) = OMS(path.module ? translated_type_name(path.name))

  def translated_fun_name(name:LocalName) = "t_" + name
  def translated_fun_path(path:GlobalName) = OMS(path.module ? translated_fun_name(path.name))
  def translated_fun(path:GlobalName) = THFOMS(translated_fun_path(path).path)

  def type_pred_name(name:LocalName) = name.toString + "_pred"
  def type_pred_path(path:GlobalName) = path.module ? type_pred_name(path.name)
  def type_pred(path:GlobalName) = THFOMS(type_pred_path(path))

  def translate_var(n:LocalName) = "V_" + n
  def default_name(p: ContentPath) = "t_" + p.name.toString
}