package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.Context.{context2list, makeFresh}
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{ContentPath, GeneralError, GlobalName, ImplementationError, LocalName, MPath}
import info.kwarc.mmt.lf._
import latin2.sfol.SFOLPatterns.TypeDecl
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
import lf.TypedEquality.tequal
import lf.TypedExistentialQuantification.texists
import lf.TypedUniversalQuantification.tforall
import lf.{DependentConjunction, DependentFunctionTypes, DependentFunctions, DependentImplication, Falsity, InternalPropositions, SimpleFunctionTypes, Truth, TypedEquality, TypedTerms}
import info.kwarc.mmt.api
import info.kwarc.mmt.api.checking.{History, Solver, TypeBasedEqualityRule}
import info.kwarc.mmt.api.objects.Conversions.localName2OMV
import latin2.tptp.DHOLExporterUtil._
import latin2.tptp.THFExporterUtil._

class DHOLExporter extends logicExporter {
  val priority: Int = 4
  val theoryPath: info.kwarc.mmt.api.MPath = lf.DHOL._path
  def tptp_conjecture(conj: info.kwarc.mmt.api.objects.Term) =
    THFAnnotated("conjecture", "conjecture", THF.Logical(translate_term(conj)), None)

  var pathMap: List[(GlobalName, String)] = Nil
  var predDecls: List[(GlobalName, VarDecl)] = Nil

  /**
   *
   * @param path the path of the declaration
   * @param tp the type of the declaration
   * @param df the definien of the declaration
   * @param ctx the context of the declaration
   * @param ctrl the controller
   * @precondition We need to call this method on the declaration in the theory in the order in which they appear in it
   * @return the translation of the declaration
   */
  def translate_decl(path: GlobalName, tpO: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val Some(tp) = tpO
    val simplicationUnit = SimplificationUnit(Context(path.module), expandConDefs = true, expandVarDefs = true, fullRecursion = true)
    val simplifiedTp = try {
      ctrl.simplifier(tp, simplicationUnit)
    } catch {
      // this shouldn't happen, but it makes more sense to continue anyways, as simplifying is not really necessary
      // TODO: add some error handling
      case e: GeneralError => tp
    }

    val name = path.name

    val declTranslated = simplifiedTp match {
      case lf.Types.tp.term | Univ(1) | TypeDecl(Nil) =>
        pathMap ::= (path, translated_type_name(name))
        pathMap ::= (path, translated_type_name(name))
        val tpDecl = THFAnnotated(type_decl_name(name), "type", THF.Typing(translated_type_name(name), THFType), None)
        val predTp = THF.BinaryFormula(FunTyConstructor, translate_type(OMS(path)), THFBool)
        val tpPred = THFAnnotated(type_pred_decl_name(name), "type",
          THF.Typing(type_pred_name(name), predTp), None)
        List(tpDecl, tpPred)
      case FunType(args, bdy) if (bdy == Univ(1) || bdy == lf.Types.tp.term) && args.nonEmpty =>
        val dependentArgs = argContext(args)
        pathMap ::= (path, translated_type_name(name))
        pathMap ::= (type_pred_path(path), type_pred_name(name))
        val tpDecl = THFAnnotated(type_decl_name(name), "type",
          THF.Typing(translated_type_name(name), THFType), None)
        val translated_args = dependentArgs.map(_.tp.get) :+ OMS(path)
        val predTp = THFArrow(translated_args map translate_type, THFBool)
        val tpPred = THFAnnotated(type_pred_decl_name(name), "type",
          THF.Typing(type_pred_name(name), predTp), None)
        List(tpDecl, tpPred)
      case TypedTerms.tm(DependentFunctionTypes.depfun(s, t)) => unapplyDepFun(DependentFunctionTypes.depfun(s, t)) match { // declaration of function
        case Some((dependentArgs, ret)) =>
          pathMap ::= (path, translated_fun_name(name))
          ret match {
            case lf.Booleans.bool(()) => predDecls ::= (path, dependentArgs.last)
            case _ => ()
          }
          val funDecl = THFAnnotated(type_decl_name(name), "type",
            THF.Typing(translated_fun_name(name), translate_type(Pi(dependentArgs, ret))), None)
          val retPred = typing_pred(Pi(dependentArgs, ret), ApplyGeneral(OMS(path), dependentArgs.map(_.toTerm)))
          lazy val tpAx = THFAnnotated(tp_ax_decl_name(name), "axiom",
            THF.Logical(retPred), None)
          List(funDecl, tpAx)
      }
      case ftp@ApplyGeneral(OMS(p), args) if pathMap.exists(_._1 == p) =>
        pathMap ::= (path, translated_fun_name(name))
        val constDecl = THFAnnotated(type_decl_name(name), "type",
          THF.Typing(translated_fun_name(name), translate_type(ftp)), None)
        val retPred = typing_pred(OMS(p), OMS(path))
        val tpAx = THFAnnotated(tp_ax_decl_name(name), "axiom",
          THF.Logical(retPred), None)
        List(constDecl, tpAx)
      case lf.Proofs.ded(ax) =>
        val tax = translate_term(ax)
        List(THFAnnotated(ax_decl_name(name), "axiom", THF.Logical(tax), None))
      case OMBINDC(binder, context, List(scopes)) if binder.toStr(true) == "unknown" => // this case shouldn't be necessary
        scopes match {
          case lf.Proofs.ded(ax) =>
            val tax = translate_term(ax)
            List(THFAnnotated(ax_decl_name(name), "axiom", THF.Logical(tax), None))
          case _ => ???
        }
      case _ => ??? // should be impossible
    }
    add_formula_comment(name.toString)
    declTranslated
  }

  /**
   * translate a context element (variable or assumption) by translating variable types, relativizing them and translating assumptions
   * @param thy_path
   * @param vd the variable declaration to translate
   * @param ctx the context so far
   * @param ctrl the controller
   * @return
   */
  override def translate_var_decl(thy_path: MPath, vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[AnnotatedFormula] = vd match {
    case VarDecl(v, None, None, Some(df), _) =>
      Nil
    //UNSUPPORTED("Untyped but defined context variables are unsupported by the DHOL exporter.")
    case VarDecl(v, None, None, dfO, _) =>
      Nil
      //UNSUPPORTED("Untyped context variables are unsupported by the DHOL exporter.")
    case VarDecl(name, None, Some(ded(formula)), _, _) =>
      List(THFAnnotated(vd.name.toString, "", THF.Logical(translate_term(formula)), None))
    case VarDecl(v, None, Some(TypedTerms.tm(df@DependentFunctionTypes.depfun(s, t))), _, _) => unapplyDepFun(df) match {
      case Some((dependentArgs, ret)) =>
        val funDecl = THFAnnotated(type_decl_name(v), "type",
          THF.Typing(translate_var(v), translate_type(Pi(dependentArgs, ret))), None)
        val retPred = typing_pred(Pi(dependentArgs, ret), OMS(thy_path ? translate_var(v)))
        lazy val tpAx = THFAnnotated(tp_ax_decl_name(v), "axiom",
          THF.Logical(retPred), None)
        List(funDecl, tpAx)
    }
    case VarDecl(v, None, Some(ftp@ApplyGeneral(OMS(p), args)), _, _) =>
      val constDecl = THFAnnotated(type_decl_name(v), "type",
      THF.Typing(translate_var(v), translate_type(ftp)), None)
      val retPred = typing_pred(OMS(p), OMV(v))
      val tpAx = THFAnnotated(tp_ax_decl_name(LocalName(translate_var(v))), "axiom",
        THF.Logical(retPred), None)
      List(constDecl, tpAx)
    case VarDecl(v, None, Some(t), _, _) => UNSUPPORTED("Unsupported context variable type for variable" + v + " of type "+ ctrl.presenter.asString(t) +". ")
    case VarDecl(name, Some("include"), tp, _, _) => Nil
    case VarDecl(name, Some(f), tp, _, _) => ???
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[THFAnnotated] = {
    // TODO: typecheck while translating
    // We need to remember the constants and what kind of constants they are in order to work out the correct
    // paths in the translation and in order to define the typing predicate for booleans using case distinctions
    val decls = theory.getConstants
    predDecls = Nil
    pathMap = Nil

    decls .map (c => (c.path, c.tp, c.df)) flatMap { case (p, tp, df) => translate_decl(p, tp, df, Context(p.module))}
  }

  def translate_term(t: Term): THF.Formula = t match {
    case Lambda(v, ty, body) => THF.QuantifiedFormula(THF.^, Seq((translate_var(v), translate_term(ty))), translate_term(body))
    case DependentFunctions.deplambda(_, _, f) => translate_term(f)
    case DependentFunctions.depapply(_, _, f, x) => translate_term(ApplySpine(f, x))
    case lf.SimpleFunctions.simplambda(_, _, f) => translate_term(f)
    case lf.SimpleFunctions.simpapply(_, _, f, x) => translate_term(ApplySpine(f, x))

    // possible since we remove tm @ _ from terms
    case DependentFunctionTypes.depfun(f, arg) => translate_term(ApplySpine(f, arg))

    case InternalPropositions.bool.term => THFBool
    //TODO: Add term -> $i
    // TODO: product types, etc. still needed

    case tforall((ty, Lambda(v, _, body))) =>
      val ass = typing_pred(ty, OMV(v))
      val concl = translate_term(body)
      THF.QuantifiedFormula(
        THF.!,
        Seq(
          (translate_var(v), translate_type(ty))
        ),
        THF.BinaryFormula(THF.Impl, ass, concl)
      )
    case texists((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.?,
        Seq(
          (translate_var(v), translate_type(ty))
        ),
        THF.BinaryFormula(THF.Impl, typing_pred(ty, OMV(v)), translate_term(body))
      )
    case TypedTerms.tm(tm) => translate_term(tm)
    case tforall(ty, body) =>
      val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
      translate_term(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case texists(ty, body) =>
      val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
      translate_term(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case and(left, right) =>
      THFAnd(translate_term(left), translate_term(right))
    case DependentConjunction.dand(left, right) =>
      THFAnd(translate_term(left), translate_term(right))
    case or(left, right) =>
      THF.BinaryFormula(THF.|, translate_term(left), translate_term(right))
    case impl(left, right) =>
      THF.BinaryFormula(THF.Impl, translate_term(left), translate_term(right))
    case DependentImplication.dimpl(left, right) =>
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

    case OMV(x) => THF.Variable(translate_var(x))

    // after dependency-erasure dependent application becomes ordinary application
    case ApplyGeneral(DependentFunctions.depapply.term, argTp::funTp::fun::arg::args) =>
      translate_term(ApplyGeneral(fun, arg::args))

    case ApplySpine(f, args) =>
      val fTr = translate_term(f)
      val argsTr = args map translate_term
      fTr match {
        case THF.FunctionTerm(n, xs) => THF.FunctionTerm(n, xs ++ argsTr)
        case _ => args.map(translate_term).foldLeft(translate_term(f))((g, arg) => THFApp(g, arg))
      }

    case OMA(OMV(i), args) if i.toString.startsWith("I/") && i.toString.stripPrefix("I/").toCharArray.forall(_.isDigit) =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Cannot resolve implicit argument: " + t)
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
      translate_type(FunType(depArgs.map(vd => (Some(vd.name), vd.tp.get)), bdy))
    }

    case FunType(args, ret) if args.nonEmpty => THFArrow(argContext(args) map (_.tp.get) map translate_type, translate_type(ret))
    case TypedTerms.tm(tp) => translate_type(tp)
    case ApplySpine(tp, _) => translate_type(tp)
    case OMS(gn) => THFOMS(translated_type_path(gn).path)
  }

  def typing_pred(t:Term, x:Term): THF.Formula = {
    t match {
      /*
      bool? t :=
      forall x:a.a? r1 ... rn => a? y   if t == forall x:a r1 ... rn.F
      a? t1 && a? t2                    if t == t1 eq t2
      p a && p b                        if t == a => b
      a? x                              if t == p y and p:a -> bool in the theory
      T1? r1 && ... && T2? rn           if t == b? r1 ... rn y for b: {x1:T1, ..., xn:Tn} T
      true                              if t == x
      true                              if t == c for a boolean constant (including true and false)
       */
      case lf.Booleans.bool(()) => x match {
        case lf.TypedEquality.tequal(tp, r, s) => THFAnd(typing_pred(tp, r), typing_pred(tp, s))
        case lf.Implication.impl(r, s) => THFAnd(typing_pred(t, r), typing_pred(t, s))
        case tforall((ty, Lambda(v, _, body))) =>
          val ass = typing_pred(ty, OMV(v))
          val tpconcl = typing_pred(lf.Booleans.bool, body)
          THF.QuantifiedFormula(THF.!, Seq((translate_var(v), translate_term(ty))), THF.BinaryFormula(THF.Impl, ass, tpconcl))
        case ApplySpine(OMS(p), args) => predDecls.find(_._1 == p) match {
          case Some((c, arg)) => typing_pred(arg.tp.get(), arg.toTerm)
          case None => THFTrue  // in this case p must be a typing predicate
        }
        case OMV(x) =>
          ???  // can not occur
      }
      case Truth._true(()) | Falsity._false(()) =>
        THFTrue
      // This only makes sense if we have a boolean constant, in that case it can not occur on the right of an =>
      case Pi(n, tp, ret) =>
        def binder(t:THF.Formula): THF.Formula = THF.QuantifiedFormula(THF.!, Seq((translate_var(n), translate_type(tp))), t)
        // we can ignore trivial assumptions
        binder(THF.BinaryFormula(THF.Impl, typing_pred(tp, OMV(n)), typing_pred(ret, x)))
      case ApplyGeneral(OMS(a), args) =>
        val argsTr = (args:+x).map(translate_term)
        val pTr = type_pred_path(a).name.toString
        THF.FunctionTerm(pTr, argsTr)
      case _ =>
        currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Cannot resolve implicit argument to find typing predicate for: " + t)
        THFTrue //IMPOSSIBLE // shouldn't happen
    }
  }
}

object DHOLExporterUtil {
  def argContext(args: List[(Option[LocalName], Term)]): Context = {
    var dependentArgs = Context.empty
    args .zipWithIndex foreach {
      case ((nOpt, t), i) =>
        val ln = Context.pickFresh(dependentArgs, nOpt getOrElse LocalName("X_"+i))._1
        dependentArgs :+= ln % t
    }
    dependentArgs
  }
  def unapplyDepFun(tm: Term) : Option[(Context, Term)] = tm match {
    case lf.DependentFunctionTypes.depfun(tp, Lambda(n, lf.TypedTerms.tm(tp2), x)) if tp == tp2 => unapplyDepFun(x) match {
      case Some((ctx, body)) => Some(OMV(n) % tp::ctx, body)
      case None => Some(OMV(n) % tp, x)
    }
    case _ => None
  }

  def translated_fun_path(path:GlobalName) = OMS(path.module ? translated_fun_name(path.name))
  def translated_fun(path:GlobalName) = THFOMS(translated_fun_path(path).path)

  def ax_decl_name(ln: LocalName) = ln.toString+"_ax"
  def tp_ax_decl_name(ln: LocalName) = ln.toString+"_tp_ax"
  def type_pred_decl_name(ln:LocalName) = ln.toString+"_pred"

  def type_pred_name(name:LocalName) = name.toString + "_pred"
  def type_pred_path(path:GlobalName) = path.module ? type_pred_name(path.name)
  def type_pred(path:GlobalName) = THFOMS(type_pred_path(path))
}

// Should probably be moved to lf
object ProverBasedTypeEquality extends TypeBasedEqualityRule(Nil, lf.Types.tp.path) {
  /**
   * @param solver provides callbacks to the currently solved system of judgments
   * @param tm1    the first term
   * @param tm2    the second term
   * @param tp     their type
   * @param stack  their context
   * @return true iff the judgment holds; None if the solver should proceed with term-based equality checking
   */
  override def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = (tm1, tm2, tp) match {
    // do we want to consider generalizations of this rule (e.g. if f != g but f eq g or maybe f x1 ... xm == g)?
    // also what if the arguments contain unsolved terms
    case (ApplySpine(OMS(fp), xs), ApplySpine(OMS(gp), ys), lf.Types.tp.term) => {
      if (fp != gp) {
        solver.error("different heads")
        return Some(false)
      }
      solver.inferType(OMS(fp)) match {
        case Some(FunType(argTps, _)) =>
          var subs = Substitution()
          val requal = argTps.zip(xs).zip(ys) forall {
            case (((nO, a), x), y) =>
              val xtp = a ^ subs
              nO foreach { n =>
                subs ++= Sub(n, x)
                xtp
              }
              if (x == y) true else {
                val j = Equality(stack, x, y, Some(xtp))
                if (solver.isDirectlySolvable(j) || solver.isDirectlySolvable(j.swap)) {
                  solver.check(j)
                } else {
                  val pO = Pi(stack.context, lf.Proofs.ded(TypedEquality.tequal(xtp, x, y)))
                  solver.addUnknowns(Context(solver.freshUnknown() % pO), None)
                }
              }
          }
          Some(requal)
        case _ => None
      }
    }
    case _ => None
  }

  /**
   * type-based equality reasoning often uses extensionality, which can be inefficient or even lead to cycles.
   * Therefore, these rules are only applied to tm1 = tm2 : tp if tm1 or tm2 satisfies this predicate.
   */
  override def applicableToTerm(solver: Solver, tm: Term): Boolean = true
}