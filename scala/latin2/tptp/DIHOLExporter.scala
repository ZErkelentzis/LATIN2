package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.Context.context2list
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{GeneralError, GlobalName, ImplementationError, LocalName, MPath, checking}
import info.kwarc.mmt.lf._
import latin2.sfol.SFOLPatterns.TypeDecl
import leo.datastructures.TPTP.Comment.{CommentFormat, CommentType}
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
import lf.{Booleans, DependentConjunction, DependentFunctionTypes, DependentFunctions, DependentImplication, Falsity, SimpleFunctionTypes, Truth, TypedEquality, TypedTerms}
import info.kwarc.mmt.api
import info.kwarc.mmt.api.checking.{History, InferenceRule, Solver, TypeBasedEqualityRule}
import info.kwarc.mmt.api.objects.Conversions.localName2OMV
import latin2.sfol.CommonSymbols.prop
import latin2.tptp.DIHOLExporterUtil.DHOLPi.argContext
import latin2.tptp.DIHOLExporterUtil._
import latin2.tptp.THFExporterUtil._



trait dependentLogicExporter extends logicExporter {
  var pathMap: List[(GlobalName, String)] = Nil
  var numNewVars = 0

  def translate_term(t: Term)(implicit usedVars: List[String]): THF.Formula = {
    t match {
      case Lambda(v, ty, body) =>
        val (name, vn) = translate_var_name(v)
        THF.QuantifiedFormula(THF.^, Seq((name, translate_type(ty))), translate_term(body)(vn::usedVars))

      case DependentFunctions.deplambda(_, _, f) => translate_term(f)
      case DependentFunctions.depapply(_, _, f, x) =>
        THFApp(translate_term(f), translate_term(x))
      case lf.SimpleFunctions.simplambda(_, _, f) => translate_term(f)
      case lf.SimpleFunctions.simpapply(_, _, f, x) => THFApp(translate_term(f), translate_term(x))
      // TODO: This case shouldn't be necessary
      case ft@FunType(args, _) if args.nonEmpty => translate_type(ft)

      case Booleans.bool.term => THFBool
      //TODO: Add term -> $i
      // TODO: product types, etc. still needed

      case tforall((ty, Lambda(v, _, body))) =>
        val (name, vn) = translate_var_name(v)
        val tpCond = typing_pred(ty, OMV(v))
        THFUniv(name, translate_type(ty), THFImpl(tpCond, translate_term(body)(vn::usedVars)))
      case texists((ty, Lambda(v, _, body))) =>
        val (name, vn) = translate_var_name(v)
        val tpCond = typing_pred(ty, OMV(v))
        THFExist(name, translate_type(ty), THFAnd(tpCond, translate_term(body)(vn::usedVars)))
      case tforall(ty, body) =>
        val varname = LocalName(generate_fresh_var_name_ctx(Some("x_"++numNewVars.toString))(usedVars, body.freeVars))
        numNewVars += 1
        translate_term(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
      case texists(ty, body) =>
        val varname = LocalName(generate_fresh_var_name_ctx(Some("x_"++numNewVars.toString))(usedVars, body.freeVars))
        numNewVars += 1
        translate_term(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
      case and(left, right) =>
        THFAnd(translate_term(left), translate_term(right))
      case DependentConjunction.dand(left, right) =>
        THFAnd(translate_term(left), translate_term(right))
      case or(left, right) =>
        THFOr(translate_term(left), translate_term(right))
      case impl(left, right) =>
        THFImpl(translate_term(left), translate_term(right))
      case DependentImplication.dimpl(left, Lambda(_, _, right)) =>
        THFImpl(translate_term(left), translate_term(right))
      case equiv(left, right) =>
        THFEquiv(translate_term(left), translate_term(right))
      case tequal(ty, left, right) => translate_equality(ty, left, right)
      case notequal(_, left, right) =>
        THFNeq(translate_term(left), translate_term(right))
      case not(arg) =>
        THFNeg(translate_term(arg))

      case Truth._true(()) =>
        THFTrue

      case Falsity._false(()) =>
        THFFalse

      case OMID(f) => THFTerm(api.utils.listmap(pathMap, f).getOrElse(default_name(f)))

      case OMV(x) => THF.Variable(translate_var_name(x)._1)

      // after dependency-erasure dependent application becomes ordinary application
      case ApplyGeneral(DependentFunctions.depapply.term, argTp :: funTp :: fun :: arg :: args) =>
        translate_term(ApplyGeneral(fun, arg :: args))

      case ApplySpine(f, args) =>
        val argsTr = args map translate_term
        THFAppl(translate_term(f), argsTr)

      case OMA(OMV(i), args) if (i.toString.startsWith("/I/")) && i.toString.stripPrefix("/I/").toCharArray.forall(_.isDigit) =>
        println("Cannot resolve implicit argument: " + controller.presenter.asString(t))
        currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Cannot resolve implicit argument: " + t)
        ???

      case _@OMBINDC(binder, context, List(scope)) if binder.toStr(true) == "unknown" => // this case shouldn't be necessary
        //println("Cannot resolve unknown: " + controller.presenter.asString(unknown))
        translate_term(scope)
      case default =>
        println("Unsupported term: " + controller.presenter.asString(default))
        currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default)
        ???
      //return (
      //  THFTrue,
      //  List(Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default))
      //) //FIXME: exception when unknown term or op, example "0" instead of "zero" or "=" instead of "=ͭ"
    }
  }

  /**
   *
   * @param path the path of the declaration
   * @param tpO  (optional) the type of the declaration
   * @param dfO  (optional) the definien of the declaration
   * @param ctx  the context of the declaration
   * @param ctrl (implicit) the controller
   * @precondition We need to call this method on the declaration in the theory in the order in which they appear in it
   * @return the translation of the declaration
   */
  def translate_decl(path: GlobalName, tpO: Option[Term], dfO: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val name = path.name
    implicit var usedVars: List[String] = List.empty
    val declTranslated = parseDHOLDeclaration(path, tpO, dfO, ctx, replacer) match {
      case DHOLAbbreviation(path, definien) =>
        definitionSubstituents ::= (path, definien)
        pathMap ::= (path, translated_defn_name(name))
        definition_builder(None, path, name, definien, ctx)
        /* val translatedDefinien = definition_builder(LocalName(translated_defn_name(name)), tpO, definien)
        val defDecl = THFAnnotated(defn_decl_name(name), "definition",
          THF.Logical(translatedDefinien), None)
        List(defDecl) */
      case DHOLTypeDeclaration(ctxTp) =>
        pathMap ::= (path, translated_type_name(name))
        pathMap ::= (type_pred_path(path), type_pred_name(name))
        translateTypeDecl(path, ctxTp)
      case DHOLTermDeclaration(ctxTp, ctxTm, ret) =>
        // ignore the difference to allow using LF Pis instead of depfun
        val ctx = ctxTp ++ ctxTm
        usedVars ++= ctx.variables.map(_.name.toString)
        pathMap ::= (path, translated_fun_name(name))
        val funDecl = THFAnnotated(type_decl_name(name), "type",
          THF.Typing(translated_fun_name(name), translate_type(PiOrEmpty(ctx, ret))), None)
        val retPred = typing_pred(PiOrEmpty(ctx, ret), OMS(path))
        lazy val tpAx = THFAnnotated(tp_ax_decl_name(name), "axiom",
          THF.Logical(retPred), None)
        List(funDecl, tpAx)
      case DHOLAxiom(ctxTp, claim) =>
        pathMap ::= (path, ax_decl_name(name))
        usedVars ++= ctxTp.variables.map(_.name.toString)
        val translatedVarNames = ctxTp.variables.map(vd => (translate_var_name(vd.name), vd.tp)).toList
        val ax_body = translate_term(claim)(usedVars++translatedVarNames.map(_._1._2))
        val tax = translatedVarNames.foldRight(ax_body)((varNameT, bdy) =>
          THFUniv(varNameT._1._1, translate_type(varNameT._2.get), bdy))
        List(THFAnnotated(ax_decl_name(name), "axiom", THF.Logical(tax), None))
    }
    add_formula_comment(name.toString)
    declTranslated
  }

  /**
   * translate a context element (variable or assumption) by translating variable types, relativizing them and translating assumptions
   *
   * @param thy_path
   * @param vd   the variable declaration to translate
   * @param ctx  the context so far
   * @param ctrl the controller
   * @return
   */
  override def translate_var_decl(thy_path: MPath, vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[AnnotatedFormula] = {
    implicit var usedVars : List[String] = List.empty
    vd match {
      case VarDecl(v, None, None, Some(df), _) =>
        Nil
      //UNSUPPORTED("Untyped but defined context variables are unsupported by the DHOL exporter.")
      case VarDecl(v, None, None, dfO, _) =>
        Nil
      //UNSUPPORTED("Untyped context variables are unsupported by the DHOL exporter.")
      case vd@VarDecl(OMV.anonymous, None, tp, df, _) =>
        val assNames = assSubstitution.l.map(_.name).map(translate_var_decl_name)
        val namesUsed = (pathMap.map(_._2) ::: assNames) map (LocalName(_))
        val Context(vdNew) = Context.makeFresh(vd.copy(name = LocalName("p")), namesUsed)._1
        translate_var_decl(thy_path, vdNew, ctx)
      case VarDecl(name, None, Some(ded(formula)), _, _) =>
        List(THFAnnotated(vd.name.toString, "axiom", THF.Logical(translate_term(formula)), None))
      case VarDecl(v, None, Some(TypedTerms.tm(df@DependentFunctionTypes.depfun(s, t))), _, _) => unapplyDepFun(s, t) match {
        case (dependentArgs, ret) =>
          val varTr = OMS(thy_path ? v)
          assSubstitution ::= v / varTr
          val translatedName = translate_var_decl_name(v)
          // To ensure that the typing axiom references the correct term
          pathMap ::= (thy_path ? v, translatedName)
          val funDecl = THFAnnotated(type_decl_name(v), "type",
            THF.Typing(translatedName, translate_type(PiOrEmpty(dependentArgs, ret))), None)
          val retPred = typing_pred(PiOrEmpty(dependentArgs, ret), varTr)
          lazy val tpAx = THFAnnotated(tp_ax_decl_name(v), "axiom",
            THF.Logical(retPred), None)
          List(funDecl, tpAx)
      }
      case VarDecl(v, None, Some(TypedTerms.tm(ftp@ApplyGeneral(OMS(p), args))), _, _) =>
        val varTr = OMS(thy_path ? v)
        assSubstitution ::= v / varTr
        val constDecl = THFAnnotated(type_decl_name(v), "type",
          THF.Typing(translate_var_decl_name(v), translate_type(ftp)), None)
        val retPred = typing_pred(OMS(p), varTr)
        val tpAx = THFAnnotated(tp_ax_decl_name(LocalName(translate_var_decl_name(v))), "axiom",
          THF.Logical(retPred), None)
        List(constDecl, tpAx)
      case VarDecl(v, None, Some(t), _, _) => UNSUPPORTED("Unsupported context variable type for variable" + v + " of type " + ctrl.presenter.asString(t) + ". ")
      case VarDecl(name, Some("include"), tp, _, _) => Nil
      case VarDecl(name, Some(f), tp, _, _) => ???
    }
  }
  def translate_type(t: Term): THF.Formula

  /**
   * Used to relativize quantifier and variable declarations, may use a typing predicate or relation internally
   * @param t the type to generate the relativization for
   * @param x the term to relativize
   * @return
   */
  def typing_pred(t:Term, x:Term)(implicit usedVars: List[String]): THF.Formula

  def tptp_conjecture(conj: info.kwarc.mmt.api.objects.Term, conjName: Option[String]) = {
    val conjNm = conjName getOrElse "conjecture"
    THFAnnotated(conjNm, "conjecture", THF.Logical(translate_term(conj)(List.empty)), None)
  }

  def translateTypeDecl(path: GlobalName, dependentArgs: Context)(implicit ctrl: Controller): List[THFAnnotated]
  def translate_equality(tp: Term, left: Term, right: Term)(implicit usedVars: List[String]): THF.Formula
  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[THFAnnotated] = {
    // TODO: typecheck while translating
    // We need to remember the constants and what kind of constants they are in order to work out the correct
    // paths in the translation and in order to define the typing predicate for booleans using case distinctions
    val decls = theory.getConstants
    pathMap = Nil

    decls.map(c => (c.path, c.tp, c.df)) flatMap { case (p, tp, df) => translate_decl(p, tp, df, Context(p.module)) }
  }

  def inferTp(tm: Term)(implicit ctx:Context): Term = {
    val TypeInferrenceError = ImplementationError("Cannot infer type of term: "++controller.presenter.asString(tm))
    tm match {
      case DHOLLambda(argCtx, bdy) =>
        PiOrEmpty(argCtx, inferTp(bdy)(ctx++argCtx))
      case DHOLApply(fun, args) => inferTp(fun) match {
        case DHOLPi(argCtx, ret) =>
          def dropArgCtx(argTps: List[VarDecl], args: List[Term]): List[VarDecl] = (argTps, args) match {
            case (Nil, Nil) => Nil
            case (argTps, Nil) => argTps
            case (_::argTps, _::args) => dropArgCtx(argTps, args)
            case _ => throw TypeInferrenceError
          }
          println ("Inferring type of function application of function "++controller.presenter.asString(fun)++" with argument types "++argCtx.variables.toList.toString()++" to the arguments "++args.toString())
          PiOrEmpty(dropArgCtx(argCtx.variables.toList, args), ret)
      }
      case Truth._true(()) | Falsity._false(()) => Booleans.bool.term
      case tforall((_, _)) | texists((_, _)) | tforall(_, _) | texists(_, _) | and(_, _)
           | DependentConjunction.dand(_, _) | or(_, _) |  impl(_, _) | DependentImplication.dimpl(_, _)
           | equiv(_, _) | tequal(_, _, _) | notequal(_, _, _) | not(_) => Booleans.bool.term
      case OMV(v) if ctx.variables.exists(_.name == v) => ctx.variables.find(_.name == v).get.tp.get
      case OMS(p) if controller.localLookup.getO(p).isDefined =>
        val tp = controller.library.getConstant(p).tp.get
        println ("Looked up type "++controller.presenter.asString(tp)++" of constant "++p.name.toString++". ")
        tp
      case otherwise => throw TypeInferrenceError
    }
  }
  def definition_builder(tpO: Option[Term], path: GlobalName, name: LocalName, df: Term, ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    println ("Calling definition builder for definition of type "++(if (tpO.isDefined) controller.presenter.asString(tpO.get) else "not given")++" and definien "++controller.presenter.asString(df))
    def THFPi(args: Context, ret: THF.Formula) = THFArrow(args.map(vd => translate_type(vd.tp.get)), ret)
    try {
      val (argCtx, ret): (Context, Term) = tpO match {
        case Some(DHOLPi(ctx, ret)) => (ctx, ret)
        case None => df match {
          case DHOLLambda(ctx, bdy) =>
            println("Inferring (implicit) type of body of lambda in definien: ")
            val ret = inferTp(bdy)(ctx)
            println(controller.presenter.asString(ret))
            (ctx, ret)
        }
      }
      implicit val usedVars = (ctx++argCtx).variables.map(_.name.toString).toList
      val (retT, innerBind) = ret match {
        case prop.term | TypedTerms.tm(Booleans.bool.term) => (THFBool, THFEquiv(_, _))
        case lf.Types.tp.term | Univ(1) | TypeDecl(Nil) | _ => (translate_type(ret), THFEq(_, _))
      }
      val appliedDef = translate_term(ApplyGeneral(OMS(path), argCtx.map(_.toTerm)))
      val (ty, inner): (THF.Formula, Term => THF.Formula) =
        (THFPi(argCtx, retT), (d: Term) => innerBind(appliedDef, translate_term(d)))
      val thfaName = type_decl_name(name)
      val tpD = THFAnnotated(thfaName, "type", THF.Typing(translated_type_name(name), ty), None)
      add_formula_comment(thfaName)

      val ax_body = df match {
        case DHOLLambda(_, d) => argCtx.foldRight(inner(d))((vd, bdy) => THFUniv(translate_var_name(vd.name)._1, translate_type(vd.tp.get), bdy))
      }
      val dfD = List(THFAnnotated(ax_decl_name(name / "def"), "definition", THF.Logical(ax_body), None))
      tpD :: dfD
    } catch {
      case typeInfError: ImplementationError => return List.empty
    }
  }
}

class DIHOLExporter extends dependentLogicExporter {
  val priority: Int = 4
  val theoryPath: info.kwarc.mmt.api.MPath = lf.DIHOL._path

  // to get correct behaviour for the classical translation which extends this class, switch this to true
  implicit val allowBoolValuedQuantification = true

  def translateTypeDecl(path: GlobalName, dependentArgs: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val name = path.name
    val tpDecl = THFAnnotated(type_decl_name(name), "type",
      THF.Typing(translated_type_name(name), THFType), None)
    val translated_args = dependentArgs.map(_.tp.get) :+ OMS(path)
    val predTp = THFArrow(translated_args map translate_type, THFBool)
    val tpPred = THFAnnotated(type_pred_decl_name(name), "type",
      THF.Typing(type_pred_name(name), predTp), None)
    List(tpDecl, tpPred)
  }
  override def translate_equality(tp: Term, left: Term, right: Term)(implicit usedVars: List[String]): THF.Formula = tp match {
    case Pi (n, a, b) =>
      val eqAppls = tequal (b, ApplySpine (left, n), ApplySpine (right, n) )
      val tpCond = typing_pred(a, OMV(n))
      val (name, vn) = translate_var_name(n)
      THFUniv(name, translate_type(a), THFImpl(tpCond, translate_term(eqAppls)(vn::usedVars)))
    case FunType (args, body) if args.length > 0 =>
      val argsCon = argContext (args)
      translate_term (tequal (Pi (argsCon, body), left, right) )
    case _ =>
      val typingL = typing_pred (tp, left)
      val typingR = typing_pred (tp, right)
      val transEq = THFEq (translate_term (left), translate_term (right) )
      THFAnd (transEq, THFAnd (typingL, typingR) )
  }
  def translate_type(t: Term): THF.Formula = t match {
    case lf.Booleans.bool(()) | lf.Propositions.prop(()) => THFBool
    case depFun@lf.DependentFunctionTypes.depfun(tp, lam) => {
      val (depArgs, bdy) = unapplyDepFun(tp, lam)
      translate_type(FunType(depArgs.map(vd => (Some(vd.name), vd.tp.get)), bdy))
    }
    case FunType(args, ret) if args.nonEmpty =>
      THFArrow(argContext(args) map (_.tp.get) map translate_type, translate_type(ret))
    case TypedTerms.tm(tp) => translate_type(tp)
    case ApplySpine(tp, _) => translate_type(tp)
    case OMS(gn) => THFOMS(translated_type_path(gn).path)
    case OMA(f, Nil) => translate_type(f)
    // TODO: Should we support this?
    case OMV(n) => THF.Variable(translate_var_name(n)._1)
    case _ =>
      println("unexpected type to translate: "+t.toNode.toString())
      throw  UNSUPPORTED("unexpected type to translate: "+controller.presenter.asString(t))
  }

  def typing_pred(t:Term, x:Term)(implicit usedVars: List[String]): THF.Formula = {
    t match {
      /*
      bool? t :=
      forall x:a.a? r1 ... rn => a? y   if t == forall x:a r1 ... rn.F
      a? t1 && a? t2                    if t == t1 eq t2
      p a && (a => p b)                        if t == a => b
      a? x                              if t == p y and p:a -> bool in the theory
      T1? r1 && ... && T2? rn           if t == b? r1 ... rn y for b: {x1:T1, ..., xn:Tn} T // not actually possible
      x == true || x == false           if t == x
      true                              if t == c for a boolean constant (including true and false)
       */
      case lf.Booleans.bool(()) => x match {
        case lf.TypedEquality.tequal(tp, r, s) => THFAnd(typing_pred(tp, r), typing_pred(tp, s))
        case lf.Implication.impl(r, s) => THFAnd(typing_pred(t, r), THFImpl(translate_term(r), typing_pred(t, s)))
        case tforall((ty, Lambda(v, _, body))) =>
          val ass = typing_pred(ty, OMV(v))
          val tpconcl = typing_pred(lf.Booleans.bool, body)
          THFUniv(translate_var_name(v)._1, translate_type(ty), THFImpl(ass, tpconcl))
        case texists((ty, Lambda(v, _, body))) =>
          val ass = typing_pred(ty, OMV(v))
          val tpconcl = typing_pred(lf.Booleans.bool, body)
          THFExist(translate_var_name(v)._1, translate_type(ty), THFAnd(ass, tpconcl))
        case ApplySpine(OMS(a), args) =>
          val argsTr = (args:+x).map(translate_term)
          val pTr = type_pred_path(a).name.toString
          THFAppl(THFTerm(pTr), argsTr)
        case OMV(x) => THFTrue
          //THFOr(THFEq(THF.Variable(translate_var_name(x)), THFTrue), THFEq(THF.Variable(translate_var_name(x)), THFFalse))
      }
      case TypedTerms.tm(tp) => typing_pred(tp, x)
      case Pi(n, tp, ret) =>
        val tpCond = typing_pred(tp, OMV(n))
        THFUniv(translate_var_name(n)._1, translate_type(tp), THFImpl(tpCond, typing_pred(ret, x)))
      case ApplyGeneral(OMS(a), args) =>
        val argsTr = (args:+x).map(translate_term)
        val pTr = type_pred_path(a).name.toString
        THFAppl(THFTerm(pTr), argsTr)
      case _ =>
        currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Cannot resolve implicit argument to find typing predicate for: " + t)
        ??? //IMPOSSIBLE // shouldn't happen
    }
  }
}

sealed abstract class DHOLAbbreviationOrDeclaration
case class DHOLAbbreviation(path: GlobalName, definien: Term) extends DHOLAbbreviationOrDeclaration
sealed abstract class DHOLDeclaration(ctxTp: Context) extends DHOLAbbreviationOrDeclaration
case class DHOLTypeDeclaration(ctxTp: Context) extends DHOLDeclaration(ctxTp)
case class DHOLTermDeclaration(ctxTp: Context, ctxTm: Context, ret: Term) extends DHOLDeclaration(ctxTp)
case class DHOLAxiom(ctxTp: Context, claim: Term) extends DHOLDeclaration(ctxTp)

object DIHOLExporterUtil {
  /**
   * Parse a DHOL AbbreviationOrDeclaration
   * @param path
   * @param tpO
   * @param dfO
   * @param ctx
   * @param replacer
   * @param ctrl
   * @return
   */
  def parseDHOLDeclaration(path: GlobalName, tpO: Option[Term], dfO: Option[Term], ctx: Context, replacer: OMSReplacer)(implicit ctrl: Controller): DHOLAbbreviationOrDeclaration = {
    (tpO, dfO) match {
      case (_, Some(df)) if (! df.toString.contains("http://cds.omdoc.org/mmt?Errors?prove")) =>
          // in case of nested abbreviations
          val replacedDf = replacer.toTranslator().apply(ctx, df)
          val defStr = ctrl.presenter.asString(replacedDf)
          //println ("Adding " + path.name.toString + " as a abbreviation for the definien: \n" + defStr)
          DHOLAbbreviation(path, replacedDf)
        case (Some(tp), _) =>
          val translatedTp = replacer.toTranslator().applyType(ctx, tp)
          val simplicationUnit = SimplificationUnit(Context(path.module), expandConDefs = true, expandVarDefs = true, fullRecursion = true)
          val simplifiedTp = try {
            ctrl.simplifier(translatedTp, simplicationUnit)
          } catch {
            // this shouldn't happen, but it makes more sense to continue anyways, as simplifying is not really necessary
            // TODO: add some error handling
            case e: GeneralError => translatedTp
          }
          unapplyPis(simplifiedTp)
    }
  }

  /**
   * Unapply (potentially nested) type and termlevel Pis of a DHOLDeclaration given by its type
   *
   * @param tp the type of the declaration
   * @return a DHOLDeclaration containing a list of Pi-bound types,
   *         (for TermDeclarations) a list of Pi-bound terms,
   *         (for TermDeclarations) a return type, (for Axioms a claim)
   */
  private def unapplyPis(tp: Term): DHOLDeclaration = tp match {
    case FunType(args, bdy) if args.nonEmpty =>
      val dependentArgs = argContext(args)

      unapplyPis(bdy) match {
        case DHOLTypeDeclaration(ctxTp) => DHOLTypeDeclaration(dependentArgs ++ ctxTp)
        case DHOLTermDeclaration(ctxTp, ctxTm, ret) => DHOLTermDeclaration(dependentArgs ++ ctxTp, ctxTm, ret)
        case DHOLAxiom(ctxTp, claim) => DHOLAxiom(dependentArgs ++ ctxTp, claim)
      }
    case TypedTerms.tm(df@DependentFunctionTypes.depfun(s, t)) => unapplyDepFun(s, t) match { // declaration of function
      case (dependentArgs, bdy) =>
        unapplyPis(TypedTerms.tm(bdy)) match {
          case DHOLTermDeclaration(ctxTp, ctxTm, ret) => DHOLTermDeclaration(ctxTp, dependentArgs ++ ctxTm, ret)
        }
    }
    case TypedTerms.tm(a@ApplyGeneral(_, _)) =>
      DHOLTermDeclaration(Context.empty, Context.empty, a)
    // case of top-level predicate subtypes or other top-level type production in the grammar (e.g. quotients)
    case TypedTerms.tm(otherTp) =>
      DHOLTermDeclaration(Context.empty, Context.empty, otherTp)
    case lf.Types.tp.term | Univ(1) | TypeDecl(Nil) =>
      DHOLTypeDeclaration(Context.empty)
    case conj@lf.Proofs.ded(ax) =>
      DHOLAxiom(Context.empty, ax)
    case OMBINDC(binder, context, List(scopes)) if binder.toStr(true) == "unknown" => // this case shouldn't be necessary
      unapplyPis(lf.Proofs.ded(scopes))
    // case of a dependent type with no (further) arguments
    case depType@ApplyGeneral(fun, args) =>
      DHOLTermDeclaration(Context.empty, Context.empty, depType)
    case default =>
      println ("Unexpected type in declaration: "+default.toStr(true))
      DHOLTermDeclaration(Context.empty, Context.empty, default)
  }


  object DHOLLambda {
    def apply(name: LocalName, tp: Term, body: Term): Term = Lambda(name, tp, body)
    def apply(argCtx: Context, scope: Term): Term = argCtx.variables.foldRight(scope)((vd, bd) => apply(vd.name, vd.tp.get, bd))
    def unapply(tm: Term): Option[(Context, Term)] = tm match {
      case Lambda(v, ty, body) => Some (Context (v % ty), body)
      case DependentFunctions.deplambda(_, _, f) => unapply(f)
      case lf.SimpleFunctions.simplambda(_, _, f) => unapply(f)
      case _ => None
    }
  }
  object DHOLPi {
    def apply(name: LocalName, tp: Term, body: Term) = Pi (name, tp, body)
    def apply(ctx: Context, body: Term) = if (ctx.isEmpty) body else Pi(ctx, body)
    def unapply(tm: Term): Option[(Context, Term)] = tm match {
      case DependentFunctionTypes.depfun(s, t) =>
        val (ctx, bdy) = unapplyDepFun(s, t)
        unapply(bdy) match {
          case Some ((ctx2, inner)) => Some (ctx++ctx2, inner)
          case None => Some (ctx, bdy)
        }
      case SimpleFunctionTypes.simpfun(dom, codom) =>
        val (ctx, ret) = unapply(codom) match {
          case Some ((ctx, ret)) => (ctx, ret)
          case None => (Context.empty, codom)
        }
        val n = generate_fresh_var_name_ctx(None, false)(Nil, ctx.variables.map(_.name).toList)
        val ln = LocalName(n)
        println ("Found simple function type. ")
        Some ( (OMV(ln) % dom :: ctx), ret)
      case FunType(args, bdy) if args.nonEmpty =>
        val ctx = argContext(args)
        unapply(bdy) match {
          case Some ((ctx2, inner)) => Some (ctx++ctx2, inner)
          case None => Some (ctx, bdy)
        }
      case TypedTerms.tm(tp) => unapply(tp)
      case e =>
        Some (Context.empty, tm)
    }

    def is_bool_valued(ty: Term): Boolean = ty match {
      case depFun@lf.DependentFunctionTypes.depfun(tp, lam) => {
        val (depArgs, bdy) = unapplyDepFun(tp, lam)
        is_bool_valued(bdy)
      }
      case FunType(args, bdy) => is_bool_valued(bdy)
      case Booleans.bool.term => true
      case _ => false
    }
    def argContext(args: List[(Option[LocalName], Term)]): Context = {
      var dependentArgs = Context.empty
      args .zipWithIndex foreach {
        case ((nOpt, t), i) =>
          val nameSuggestionO = nOpt
          val ln = Context.pickFresh(dependentArgs, nameSuggestionO getOrElse LocalName("X_funArg_"+i))._1
          dependentArgs :+= ln % t
      }
      dependentArgs
    }
    def PiOrEmpty(ctx: Context, tm: Term) = if (ctx.isEmpty) tm else Pi(ctx, tm)
    def unapplyDepFun(tp: Term, lam: Term)(implicit ctx: Context = Context.empty) : (Context, Term) = lam match {
      case Lambda(n, lf.TypedTerms.tm(tp2), x) => x match {
        case DependentFunctionTypes.depfun(ty, fun) =>
          val (ctx2, body) = unapplyDepFun(ty, fun)
          val ln = Context.pickFresh(ctx2, n)._1
          (OMV(ln) % tp :: ctx2, body)
        case _ => (OMV(n) % tp, x)
      }
      case _ => throw GeneralError("Ill-formed dependent function type. Expected lambda as second argument, but found "+lam.toStr(true))
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

  object DHOLApply {
    def apply(fun: Term, args: List[Term]) = ApplyGeneral(fun, args)
    def unapply(tm: Term): Option[(Term, List[Term])] = tm match {
      case DependentFunctions.depapply(_, _, f, x) =>
        unapply (f) match {
          case Some ((fun,initArgs)) => Some (fun, initArgs:::List(x))
          case None => Some (f, List (x))
        }
      case lf.SimpleFunctions.simpapply(_, _, f, x) =>
        unapply (f) match {
          case Some ((fun,initArgs)) => Some (fun, initArgs:::List(x))
          case None => Some (f, List (x))
        }
      // after dependency-erasure dependent application becomes ordinary application
      case ApplyGeneral(DependentFunctions.depapply.term, argTp :: funTp :: fun :: arg :: args) =>
        unapply (ApplyGeneral(fun, arg :: args))
      case ApplySpine(f, args) =>
        unapply (f) match {
          case Some ((fun,initArgs)) => Some (fun, initArgs:::args)
          case None => Some (f, args)
        }
      case _ => None
    }
  }

  def is_bool_valued(ty: Term): Boolean = ty match {
    case depFun@lf.DependentFunctionTypes.depfun(tp, lam) => {
      val (depArgs, bdy) = unapplyDepFun(tp, lam)
      is_bool_valued(bdy)
    }
    case FunType(args, bdy) => is_bool_valued(bdy)
    case Booleans.bool.term => true
    case _ => false
  }
  def PiOrEmpty(ctx: Context, tm: Term) = if (ctx.isEmpty) tm else Pi(ctx, tm)
  def unapplyDepFun(tp: Term, lam: Term)(implicit ctx: Context = Context.empty) : (Context, Term) = lam match {
    case Lambda(n, lf.TypedTerms.tm(tp2), x) => x match {
      case DependentFunctionTypes.depfun(ty, fun) =>
        val (ctx2, body) = unapplyDepFun(ty, fun)
        val ln = Context.pickFresh(ctx2, n)._1
        (OMV(ln) % tp :: ctx2, body)
      case _ => (OMV(n) % tp, x)
    }
    case _ => throw GeneralError("Ill-formed dependent function type. Expected lambda as second argument, but found "+lam.toStr(true))
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
      if ((xs++ys).exists(_.toStr(true).contains("unknown"))) {
        println("Calling prover-based type equality for terms with unknowns: "+tm1.toStr(true)+" = "+ tm2.toStr(true))
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

abstract class ConnectiveTypingRule(path: GlobalName) extends InferenceRule(path, info.kwarc.mmt.lf.OfType.path) {
  def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): (Option[Term]) = tm match {
    case ApplyGeneral(OMID(this.path), a :: b :: Nil) =>
      if (!covered) {
        val aTyped = solver.check(Typing(stack, a, lf.Booleans.bool))(history + "Checking first argument of dependent implication.")
        if (aTyped) {
          solver.check(Typing(stack ++ OMV.anonymous % lf.Proofs.ded(a), b, Booleans.bool))(history + "Checking second argument of dependent implication.")
        }
      }
      Some(Booleans.bool)
  }
}

object DependentImplicationInferenceRule extends ConnectiveTypingRule(lf.Implication.impl.path)
object DependentConjunctionInferenceRule extends ConnectiveTypingRule(lf.Conjunction.and.path)

object PiApplicationSimplificationRule extends TypeBasedEqualityRule(Nil, TypedTerms.tm.path) {
  /**
   * @param check   provides callbacks to the currently solved system of judgments
   * @param tm1     the first term
   * @param tm2     the second term
   * @param tp      their type if known
   * @param stack   their context
   * @param history the history so far
   * @return Some(areEqual) indicating whether the terms are to be considered equal
   *         None if this rule is not applicable
   */
  override def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
    (tm1, tm2) match {
      case (TypedTerms.tm(_), TypedTerms.tm(ApplySpine(funTp, args))) => apply(solver)(tm2, tm1, tp)
      case (TypedTerms.tm(ApplySpine(funTp, args)), TypedTerms.tm(y)) =>
        val simplified = solver.simplify(funTp)(stack, history) match {
          case const@OMS(p) => try {
            solver.controller.getConstant(p).df.getOrElse(const)
          } catch {
            case _: Error => const
          }
          case default => default
        }

        val tm1Simplified: Term = simplified match {
          case FunType(funArgs, ret) =>
            val (appliedArgs, unappliedArgs) = funArgs.splitAt(args.length)
            var subs = Substitution.empty
            appliedArgs.zip(args) foreach {
              case ((Some(x), xTp), tm) => subs ::= x / tm
              case ((None, _), _) =>
            }
            FunType(unappliedArgs, ret ^ subs)
          case default => default
        }

        val requal = if (tm1Simplified == y) true else {
          val j = Equality(stack, tm1Simplified, y, Some(tp))
          if (solver.isDirectlySolvable(j) || solver.isDirectlySolvable(j.swap)) {
            solver.check(j)
          } else {
            val pO = Pi(stack.context, lf.Proofs.ded(TypedEquality.tequal(tp, tm1Simplified, y)))
            solver.addUnknowns(Context(solver.freshUnknown() % pO), None)
          }
        }

        Some(requal)
    }
  }
  // rule doesn't really seem to work anyways
  override def applicableToTerm(solver: Solver, tm: Term): Boolean = false
}
