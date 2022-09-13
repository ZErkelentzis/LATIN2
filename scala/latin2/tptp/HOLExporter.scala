package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{ContentPath, GlobalName, ImplementationError, LocalName}
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
import latin2.tptp.THFExporterUtil._

class HOLExporter extends logicExporter {
  val priority: Int = 3
  val theoryPath: info.kwarc.mmt.api.MPath = lf.DHOL._path
  def tptp_conjecture(conj: info.kwarc.mmt.api.objects.Term) = THFAnnotated("conjecture", "conjecture", THF.Logical(translate_formula(conj)), None)

  def translate_theory(theory: Theory)(implicit ctrl: Controller) = {
    theory.getConstants.flatMap(translate_constant)
  }

  def translate_decl(path: GlobalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandConDefs = true, expandVarDefs = true, fullRecursion = true)

    val newTp = tp.map(ctrl.simplifier(_, simplicationUnit))

    val name = path.name

    newTp match {
      case Some(FunType(args, ded(formula))) => //axiom schemata, beweis vorhanden -> definiton kann ignoriert werden
        /*val c = args.foldRight(formula){case ((name,ty),accu) => (name, ty) match {
          case (Some(n), tm(a)) => tforall(a, Lambda(n, tm(a), accu))
          case (None, ded(f)) => impl(f, accu)
        }}*/
        var c = formula
        for ((name, ty) <- args.reverse) {
          (name, ty) match {
            case (Some(n), tm(a)) => c = tforall(a, Lambda(n, tm(a), c))
            case (None, ded(f)) => c = impl(f, c)
            case default => {
              val name = path.toString
              comments += (name -> Seq(Comment(CommentFormat.LINE, CommentType.NORMAL, "Unsupported Argument(s) for Deduction: " + default)))
              return List(THFAnnotated(path.toString, "axiom", THF.Logical(THFTrue), None))
            }
          }
        }
        val nameString = name.toString
        val ret = List(THFAnnotated(nameString, "axiom", THF.Logical(translate_formula(c)), None))
        add_formula_comment(nameString)
        ret
      case Some(TypeDecl(Nil)) =>
        List(THFAnnotated(type_decl_name(name), "type", THF.Typing("t_" + name.toString, THFType), None)) //is optional
      case newTp => definition_builder(newTp, path, name, df, ctx)
    }
  }

  def definition_builder(newTp: Option[Term], path: GlobalName, name: LocalName, df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val (ty, inner) = newTp match {
      case Some(PredDecl(in)) =>
        (THFArrow(in.map(translate_formula), THFTerm("$o")),
          (args: List[(LocalName, Term)], d: Term) => equiv(ApplyGeneral(OMS(path), args.map(x => OMV(x._1))), d))
      case Some(FuncDecl(in, out)) =>
        (THFArrow(in.map(translate_formula), translate_formula(out)),
          (args: List[(LocalName, Term)], d: Term) => tequal(out, ApplyGeneral(OMS(path), args.map(x => OMV(x._1))), d))
      case _ => //No known definition -> Comment
        return Nil //return THFAnnotated("")
    }
    val thfaName = type_decl_name(name)
    val tpD = THFAnnotated(thfaName, "type", THF.Typing(translated_type_name(name), ty), None)
    add_formula_comment(thfaName)
    val dfT = df match {
      case Some(FunTerm(args, d)) => //FIXME
        val argssome = args.map(x => (Some(x._1), x._2))
        Some(FunType(argssome, ded(inner(args, d))))
      case _ => None
    }
    var dfD = translate_decl(path / "def", dfT, None, ctx)
    assert(dfD.length <= 1)
    dfD = dfD.map(x => x.copy(role = "definition"))

    tpD :: dfD
  }

  def translate_formula(t: Term): THF.Formula = t match {
    case Lambda(v, ty, body) => THF.QuantifiedFormula(THF.^, Seq((translate_var(v), translate_formula(ty))), translate_formula(body))
    case simplambda(_, _, f) => translate_formula(f)
    case simpapply(_, _, f, x) => translate_formula(ApplySpine(f, x))

    case SimpleFunctionTypes.simpfun(a, b) => THFArrow(List(translate_formula(a)), translate_formula(b))
    case InternalPropositions.bool.term => THFBool
    //TODO: Add term -> $i
    // TODO: product types, etc. still needed

    case tforall((ty, Lambda(v, _, body))) => THFUniv(translate_var(v), translate_formula(ty), translate_formula(body))
    case texists((ty, Lambda(v, _, body))) => THFExist(translate_var(v), translate_formula(ty), translate_formula(body))
    case tforall(ty, body) =>
      val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
      translate_formula(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case texists(ty, body) =>
      val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
      translate_formula(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case and(left, right) =>
      THFAnd(translate_formula(left), translate_formula(right))
    case or(left, right) =>
      THFOr(translate_formula(left), translate_formula(right))
    case impl(left, right) =>
      THFImpl(translate_formula(left), translate_formula(right))
    case equiv(left, right) =>
      THFEquiv(translate_formula(left), translate_formula(right))
    case tequal(ty, left, right) => {
      THFEq(translate_formula(left), translate_formula(right))
    }
    case notequal(ty, left, right) => {
      THFNeq(translate_formula(left), translate_formula(right))
    }
    case not(arg) =>
      THFNeg(translate_formula(arg))

    case Truth._true(()) =>
      THFTrue

    case Falsity._false(()) =>
      THFFalse

    case OMID(f) =>
      THFOMS(f)

    case OMV(x) =>
      THF.Variable(translate_var(x))

    case ApplySpine(f, args) => args.map(translate_formula).foldLeft(translate_formula(f))((g, arg) => THF.BinaryFormula(THF.App, g, arg))

    case default =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default)
      THFTrue
    //return (
    //  THFTrue,
    //  List(Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default))
    //) //FIXME: exception when unknown term or op, example "0" instead of "zero" or "=" instead of "=ͭ"
  }
}


object THFExporterUtil {
  def THFTerm(n:String) = THF.FunctionTerm(n, Nil)
  val THFType = THFTerm("$tType")
  val THFBool = THFTerm("$o")
  val THFTrue = THFTerm("$true")
  val THFFalse = THFTerm("$false")
  def THFOMS(p:ContentPath) = THF.FunctionTerm(p.name.toString, Nil)
  def THFArrow(in: List[THF.Formula], out: THF.Formula) = in.foldRight(out)((g, arg) => THF.BinaryFormula(FunTyConstructor, g, arg))
  def THFAnd(con1: THF.Formula, con2: THF.Formula): THF.Formula = THF.BinaryFormula(THF.&, con1, con2)
  def THFOr(disj1: THF.Formula, disj2: THF.Formula): THF.Formula = THF.BinaryFormula(THF.|, disj1, disj2)
  def THFApp(con1: THF.Formula, con2: THF.Formula): THF.Formula = THF.BinaryFormula(THF.App, con1, con2)
  def THFImpl(ass: THF.Formula, concl: THF.Formula): THF.Formula = THF.BinaryFormula(THF.Impl, ass, concl)
  def THFEq(form1: THF.Formula, form2: THF.Formula): THF.Formula = THF.BinaryFormula(THF.Eq, form1, form2)
  def THFNeg(form: THF.Formula): THF.Formula = THF.UnaryFormula(THF.~, form)
  def THFEquiv(a: THF.Formula, b: THF.Formula): THF.Formula = THF.BinaryFormula(THF.<=>, a, b)
  def THFNeq(form1: THF.Formula, form2: THF.Formula): THF.Formula = THF.BinaryFormula(THF.Neq, form1, form2)
  def THFUniv(name: String, tp: THF.Formula, body: THF.Formula) = THF.QuantifiedFormula(THF.!, Seq((name, tp)), body)
  def THFExist(name: String, tp: THF.Formula, body: THF.Formula) = THF.QuantifiedFormula(THF.?, Seq((name, tp)), body)

  def translated_type_name(name:LocalName) = translate_var_decl_name(name)
  def translated_type_path(path:GlobalName) = OMS(path.module ? translated_type_name(path.name))

  def translated_fun_name(name:LocalName) = translate_var_decl_name(name)
  def translated_fun_path(path:GlobalName) = OMS(path.module ? translated_fun_name(path.name))
  def translated_fun(path:GlobalName) = THFOMS(translated_fun_path(path).path)

  def type_decl_name(ln: LocalName) = ln.toString+"_type"

  def translate_var(n:LocalName) = "V_" + n.toString.toUpperCase
  def translate_var_decl_name(n:LocalName) = "t_" + n.toString
  def default_name(p: ContentPath) = translate_var_decl_name(p.name)
  def IMPOSSIBLE = throw ImplementationError("This case should be impossible.")
  def UNSUPPORTED(s:String) = throw ImplementationError("This feature is unsupported: " + s)
}