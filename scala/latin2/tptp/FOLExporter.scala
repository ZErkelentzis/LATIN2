package latin2.tptp

import info.kwarc.mmt.api.archives.BuildTask
import info.kwarc.mmt.api.{CPath, StructuralElement, documents}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.{Context, IncludeVarDecl, OMID, OMV, Obj, Term, VarDecl}
import info.kwarc.mmt.api.presentation.{ObjectPresenter, RenderingHandler, StructurePresenter}
import info.kwarc.mmt.api.symbols.Constant
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.lf.{ApplySpine, Lambda}
import latin2.sfol.CommonSymbols.DedList
import leo.datastructures.TPTP.{FOF, FOFAnnotated, Problem}
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.ExistentialQuantification.exists
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.UniversalQuantification.forall

class FOLExporter extends StructurePresenter {
  override def apply(e : StructuralElement, standalone: Boolean = false)(implicit rh : RenderingHandler): Unit = {}

  /** a string identifying this build target, used for parsing commands, logging, error messages */
  override def key: _root_.scala.Predef.String = "tptp"

  override def exportTheory(thy : Theory, bf: BuildTask): Unit = {
    val vars = bf.getClass.getDeclaredFields
    for(v <- vars){
      v.setAccessible(true)
      println("Field: " + v.getName() + " => " + v.get(this))
    }
  }

  def exportTPTP(ctx: Context, what: List[Term])(implicit ctrl: Controller): Problem = {
    // walk through ctx, collect all axioms
    // especially, upon IncludeVarDecls, recurse into referenced theory
    val axioms = ctx.mapVarDecls {
      case (_, vd@IncludeVarDecl(_, _, _)) =>
        val path = vd.tp.get.toMPath
        translate_theory(ctrl.getTheory(path))
      case (ctx, vd: VarDecl) =>
        translate_var_decl(vd, ctx)(ctrl).toList
    }.flatten.distinct.map(x => x.copy(role = "axiom"))

    val conjectures = what match {
      case DedList(formulas) => formulas.map(f => FOFAnnotated("Conjecture", "conjecture",  FOF.Logical(translate_formula(f)), None))
    }

    Problem(List(), (axioms++conjectures))
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[FOFAnnotated] = {
    theory.getIncludesWithoutMeta.flatMap(include => translate_theory(ctrl.getTheory(include))) ++ theory.getConstants.flatMap(translate_constant)
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

  def translate_formula(t: Term): FOF.Formula = t match {
    case forall(Lambda(v, _, body)) =>
      FOF.QuantifiedFormula(
        FOF.!,
        Seq(
          v.toPath
        ),
        translate_formula(body)
      )
    case exists(Lambda(v, _, body)) =>
      FOF.QuantifiedFormula(
        FOF.?,
        Seq(
          v.toPath
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

  def translate_term(t: Term): FOF.Term = t match {
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
      FOF.Variable(x.toString)
  }
}
