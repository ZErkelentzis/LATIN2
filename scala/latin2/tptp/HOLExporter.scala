package latin2.tptp

import info.kwarc.mmt.api.{GlobalName, LocalName, MPath}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.symbols.{Constant, Declaration, HasType, PlainInclude}
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.lf.{ApplyGeneral, ApplySpine, FunTerm, FunType, Lambda}
import latin2.sfol.SFOLPatterns.{FuncDecl, PredDecl, TypeDecl}
import leo.datastructures.TPTP.Comment.{CommentFormat, CommentType}
import leo.datastructures.TPTP.THF.{FunTyConstructor, FunctionTerm}
import leo.datastructures.TPTP.{AnnotatedFormula, Comment, Include, Problem, THF, THFAnnotated}
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.TypedExistentialQuantification.texists
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.SFOLEQ.notequal
import lf.{InternalPropositions, SimpleFunctionTypes}
import lf.SimpleFunctions.{simpapply, simplambda}
import lf.TypedEquality.tequal
import lf.TypedTerms.tm
import lf.TypedUniversalQuantification.tforall

import scala.collection.mutable.ArrayBuffer

object HOLExporter {
  def combineStubs(p: GlobalName, ctx: Context, t: Term)(implicit ctrl: Controller): Problem = {
    var includes = ArrayBuffer[MPath]()
    var formulas = ArrayBuffer[AnnotatedFormula]()
    for (x <- ctrl.getTheory(p.module).getDeclarations.takeWhile(_.path != p)) {
      x match
      {
        case PlainInclude(t) => includes += t._1
        case c: Constant => formulas ++= translate_constant(c)
      }
    }
    val axioms = ctx.mapVarDecls {
      case (ctx, vd: VarDecl) =>
        translate_var_decl(p.module, vd, ctx)(ctrl)
    }.flatten.distinct

    formulas ++= axioms
    formulas += THFAnnotated("conjecture", "conjecture",  THF.Logical(translate_formula(t)), None)

    val tptp_exporter = ctrl.extman.get(classOf[TPTPExporter]).head

    Problem(includes.map(i => tptp_exporter.translate_include(p.module, i)).toSeq, formulas.toSeq, Map())
  }

  def exportStub(theory: Theory)(implicit ctrl: Controller): Problem = {
    export_theory(theory, Nil)
  }

  def export_theory_flattened(theory: Theory)(implicit ctrl: Controller): Problem = {
    val axioms = translate_theory_flattened(theory).distinct.map(x => if (x.role == "") { x.copy(role = "axiom") } else x)
    Problem(List(), axioms, Map())
  }

  def translate_theory_flattened(theory: Theory)(implicit ctrl: Controller): List[THFAnnotated] = {
    theory.getIncludesWithoutMeta.flatMap(include => translate_theory_flattened(ctrl.getTheory(include))) ++ theory.getConstants.flatMap(translate_constant)
  }

  def export_theory(theory: Theory, includes: Seq[Include])(implicit ctrl: Controller): Problem = {
    val axioms = translate_theory(theory).map(x => if (x.role == "") { x.copy(role = "axiom") } else x)
    Problem(includes, axioms, Map())
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[THFAnnotated] = {
    theory.getConstants.flatMap(translate_constant)
  }

  def funty_builder(in: List[THF.Formula], out: THF.Formula) = in.foldRight(out)((g, arg) => THF.BinaryFormula(FunTyConstructor, g, arg))

  def translate_decl(path: GlobalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = tp.map(ctrl.simplifier(_, simplicationUnit))

    val name = path.name

    newTp match {
      case Some(FunType(args, ded(formula))) => //axiom schemata, beweis vorhanden -> definiton kann ignoriert werden
        /*val c = args.foldRight(formula){case ((name,ty),accu) => (name, ty) match {
          case (Some(n), tm(a)) => tforall(a, Lambda(n, tm(a), accu))
          case (None, ded(f)) => impl(f, accu)
        }}*/
        var c = formula
        for((name, ty) <- args.reverse) {
          (name, ty) match {
            case (Some(n), tm(a)) => c = tforall(a, Lambda(n, tm(a), c))
            case (None, ded(f)) => c = impl(f, c)
            case _ => return List(THFAnnotated(path.toString, "axiom", THF.Logical(THF.FunctionTerm("$true", Nil)), None)) //TODO: Comment(CommentFormat.LINE, CommentType.NORMAL, "Unsupported:") comments map in implicit argument
          }
        }
        List(THFAnnotated(name.toString, "axiom", THF.Logical(translate_formula(c)), None))
      case Some(TypeDecl(Nil))  =>
        List(THFAnnotated("type_" + name.toString, "type", THF.Typing("t_" + name.toString, THF.FunctionTerm("$tType", Nil)), None)) //is optional
      case newTp => definition_builder(newTp, path, name, df, ctx)
    }
  }

  def definition_builder(newTp: Option[Term], path: GlobalName, name: LocalName, df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val (ty, inner) = newTp match {
      case Some(PredDecl(in)) =>
        (funty_builder(in.map(translate_formula), THF.FunctionTerm("$o", Nil)),
        (args: List[(LocalName, Term)], d: Term) => equiv(ApplyGeneral(OMS(path), args.map(x => OMV(x._1))), d))
      case Some(FuncDecl(in, out)) =>
        (funty_builder(in.map(translate_formula), translate_formula(out)),
        (args: List[(LocalName, Term)], d: Term) => tequal(out, ApplyGeneral(OMS(path), args.map(x => OMV(x._1))), d))
      case _ => //No known definition -> Comment
        return Nil//return THFAnnotated("")
    }
    val tpD = THFAnnotated("type_" + name.toString, "type", THF.Typing("t_" + name.toString, ty), None)
    val dfT = df match {
      case FunTerm(args, d) =>
        val argssome = args.map(x => (Some(x._1),x._2))
        Some(FunType(argssome, ded(inner(args, d))))
      case _ => None
    }
    var dfD = translate_decl(path / "def", dfT, None, ctx)
    assert(dfD.length <= 1)
    dfD = dfD.map(x => x.copy(role = "definition"))

    tpD :: dfD
  }

  def translate_var_decl(thy_path: MPath, vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] =
    translate_decl(thy_path ? vd.name, vd.tp, vd.df, ctx)

  def translate_constant(c: Constant)(implicit ctrl: Controller): List[THFAnnotated] =
    translate_decl(c.path, c.tp, c.df, Context(c.path.module))

  def translate_formula(t: Term): THF.Formula = t match {
    case Lambda(v, ty, body) => THF.QuantifiedFormula(THF.^, Seq(("V_" + v.toPath, translate_formula(ty))), translate_formula(body))
    case simplambda(_, _, f) => translate_formula(f)
    case simpapply(_, _, f, x) => translate_formula(ApplySpine(f, x))

    case SimpleFunctionTypes.simpfun(a, b) => funty_builder(List(translate_formula(a)), translate_formula(b))
    case InternalPropositions.bool.term => THF.FunctionTerm("$o", Nil)
    //TODO: Add term -> $i
    // TODO: product types, etc. still needed

    case tforall((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.!,
        Seq(
          ("V_" + v.toPath, translate_formula(ty))
        ),
        translate_formula(body)
      )
    case texists((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.?,
        Seq(
          ("V_" + v.toPath, translate_formula(ty))
        ),
        translate_formula(body)
      )
    case tforall(ty, body) =>
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
      translate_formula(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case texists(ty, body) =>
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
      translate_formula(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case and(left, right) =>
      THF.BinaryFormula(THF.&, translate_formula(left), translate_formula(right))
    case or(left, right) =>
      THF.BinaryFormula(THF.|, translate_formula(left), translate_formula(right))
    case impl(left, right) =>
      THF.BinaryFormula(THF.Impl, translate_formula(left), translate_formula(right))
    case equiv(left, right) =>
      THF.BinaryFormula(THF.<=>, translate_formula(left), translate_formula(right))
    case tequal(ty, left, right) => {
      THF.BinaryFormula(THF.Eq, translate_formula(left), translate_formula(right))
    }
    case notequal(ty, left, right) => {
      THF.BinaryFormula(THF.Neq, translate_formula(left), translate_formula(right))
    }
    case not(arg) =>
      THF.UnaryFormula(THF.~, translate_formula(arg))

    case OMID(f) =>
      THF.FunctionTerm("t_" + f.name.toString, Nil)

    case OMV(x) =>
      THF.FunctionTerm("V_" + x.toString, Nil)

    case ApplySpine(f, args) => args.map(translate_formula).foldLeft(translate_formula(f))((g, arg) => THF.BinaryFormula(THF.App, g, arg))

    case default => println(default)
      ???
  }
}
