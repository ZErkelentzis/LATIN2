package latin2.sequents

import info.kwarc.mmt.api._
import checking._
import objects._
import uom._
import utils._
import Conversions._
import info.kwarc.mmt.LFX.patterns.PatternRule
import info.kwarc.mmt.lf._
import latin2.sequents.Ctx.ctx2ls

object Sequent {
  val baseURI = DPath(utils.URI(Some("latin"), None, abs=true))
  val path = Sequent.baseURI ? "Contexts" ? "context"
}

object InContext {
  val path = Sequent.baseURI ? "InContext" ? "in_context"
  val term = OMS(path)
  val proof = Sequent.baseURI ? "InContext" ? "in_context_proof"

  val empty = Sequent.baseURI ? "Contexts" ? "empty_ctx"

}

object ContextExt {
  val path = Sequent.baseURI ? "Contexts" ? "context_extension"
  val term = OMS(path)
  def apply(ctx : Term,a : Term) = ApplySpine(this.term,ctx,a)
  def unapply(tm : Term) = tm match {
    case ApplySpine(this.term,List(ctx,a)) => Some((ctx,a))
    case _ => None
  }
}

object ContextConc {
  val path = Sequent.baseURI ? "Contexts" ? "context_concat"
  val term = OMS(path)
  def apply(ctx : Term,a : Term) = ApplySpine(this.term,ctx,a)
  def unapply(tm : Term) = tm match {
    case ApplySpine(this.term,List(ctx,a)) => Some((ctx,a))
    case _ => None
  }
}

object ContextMap {
  val path = Sequent.baseURI ? "ContextMap" ? "map"
  val term = OMS(path)
  def apply(ctx : Term,f : Term) = ApplySpine(this.term,ctx,f)
  def unapply(tm : Term) = tm match {
    case ApplySpine(this.term,List(ctx,f)) => Some((ctx,f))
    case _ => None
  }
}

object ContextFold {
  val path = Sequent.baseURI ? "ContextFold" ? "fold"
  val term = OMS(path)
  def apply(ctx : Term, base : Term, f : Term) = ApplySpine(this.term,ctx,base,f)
  def unapply(tm : Term) = tm match {
    case ApplySpine(this.term,List(ctx,base,f)) => Some((ctx,base,f))
    case _ => None
  }
}

case class Ctx(ls : List[ContextElem]) {
  def toTerm = toTermI(ls,None)
  private def toTermI(ls : List[ContextElem], head : Option[Term] = None) : Term = {
    if (ls.isEmpty) head.getOrElse(OMS(InContext.empty)) else
      (ls.head, head) match {
        case (Opaque(tm), None) =>
          toTermI(ls.tail, Some(tm))
        case (Elem(tm), None) =>
          toTermI(ls.tail, Some(ContextExt(OMS(InContext.empty), tm)))
        case (Elem(tm), Some(h)) =>
          toTermI(ls.tail, Some(ContextExt(h, tm)))
        case (Opaque(tm: Term), Some(h)) =>
          toTermI(ls.tail, Some(ContextConc(h, tm)))
      }
  }
  def dropE(a : ContextElem) : Option[Ctx] = ls.lastIndexOf(a) match {
    case -1 => None
    case i => Some(Ctx(ls.take(i) ::: ls.drop(i+1)))
  }
  def dropE(tm : Term) : Option[Ctx] = dropE(Elem(tm))

  lazy val isComplete = ls.forall(_.isInstanceOf[Elem])
}

object Ctx {
  implicit def ls2ctx(ls : List[ContextElem]) : Ctx = Ctx(ls)
  implicit def ctx2ls(ctx : Ctx) : List[ContextElem] = ctx.ls

  def apply(tm : Term) : Ctx = tm match {
    case ContextExt(ctx,a) =>
      apply(ctx) ::: List(Elem(a))
    case ContextConc(la,lb) =>
      apply(la) ::: apply(lb)
    case ContextMap(ctx,f) =>
      apply(ctx).map {
        case Elem(a) => Elem(Apply(f,a))
        case Opaque(tm) => Opaque(ContextMap(tm,f))
      }
    case OMS(InContext.empty) =>
      Nil
    case _ =>
      List(Opaque(tm))
  }
}

sealed trait ContextElem
case class Elem(tm : Term) extends ContextElem
case class Opaque(tm : Term) extends ContextElem


object InContextProofType extends TypingRule(InContext.path) {
  override def applicable(t: Term): Boolean = t match {
    case ApplySpine(InContext.term,_) =>
      true
    case _ => false
  }

  override def apply(solver: Solver)(tm: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = tm match {
    case OMA(OMS(InContext.proof),List(itp)) =>
      Some(solver.check(Subtyping(stack,itp,tp)))
    case _ =>
      Some(false)
  }
}

object InContextRule extends TypeBasedSolutionRule(List(Apply.path),InContext.path) {
  override def solve(solver: Solver)(tp: Term)(implicit stack: Stack, history: History): Option[Term] = tp match {
    case ApplySpine(InContext.term,List(prop,ctxtm)) =>
      val ctx = Ctx(ctxtm)
      val allRules = solver.rules.filter(_.isInstanceOf[ContextRule]).getAll.toList
      if (allRules.contains(ExchangeEquality) && ctx.contains(prop)) Some(InContext.proof(tp))
      else if (ctx.lastOption.contains(Elem(prop))) Some(InContext.proof(tp))
      else None
    case _ => None
  }
}

object MapCompute extends ComputationRule(ContextMap.path) {
  override def applicable(t: Term): Boolean = t match {
    case ContextMap(_,_) => true
    case _ => false
  }

  override def apply(check: CheckingCallback)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Simplifiability = {
    ctx2ls(Ctx(tm)) match {
      case List(Opaque(_)) =>
        Simplifiability.NoRecurse
      case ls =>
        Simplify(Ctx(ls).toTerm)
    }
  }
}

object MapPattern extends PatternRule {
  override def applicable(tm: Term): Boolean = tm match {
    case ContextMap(_,_) => true
    case _ => false
  }

  override def apply(tm: Term, ctx: Context, pattern: Term, cont: (Term, Term) => Option[List[(LocalName, Term)]])(implicit solver: CheckingCallback): Option[List[(LocalName, Term)]] = {
    val ContextMap(pctx,f) = pattern
    val ntm = Ctx(tm) map {
      case Elem(Apply(`f`,a)) => Elem(a)
      case Elem(_) => return None
      case Opaque(o) => return None
    }
   cont(Ctx(ntm).toTerm,pctx)
  }
}

object FoldCompute extends ComputationRule(ContextFold.path) {
  override def applicable(t: Term): Boolean = t match {
    case ContextFold(_,_,_) => true
    case _ => false
  }

  override def apply(check: CheckingCallback)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Simplifiability = {
    val ContextFold(ctxtm,base,f) = tm
    val ctx = Ctx(ctxtm)
    if (ctx.isComplete) ctx2ls(ctx) match {
      case Nil => Simplify(base)
      case List(Elem(a)) => Simplify(a)
      case Elem(h) :: tail =>
        Simplify(tail.foldLeft(h){case (tm,Elem(e)) => ApplySpine(f,tm,e)})
    } else Simplifiability.NoRecurse
  }
}

object FoldPattern extends PatternRule {
  override def applicable(tm: Term): Boolean = tm match {
    case ContextFold(_,_,_) => true
    case _ => false
  }

  override def apply(tm: Term, ctx: Context, pattern: Term, cont: (Term, Term) => Option[List[(LocalName, Term)]])(implicit solver: CheckingCallback): Option[List[(LocalName, Term)]] = {
    val ContextFold(pctx,base,f) = pattern
    def deconstruct(itm : Term) : List[Term] = itm match {
      case ApplySpine(`f`,List(a,b)) =>
        deconstruct(a) ::: deconstruct(b)
      case `base` => Nil
      case o => o :: Nil
    }
    val ntm = deconstruct(tm).map(Elem)
    cont(Ctx(ntm).toTerm,pctx)
  }
}

class ContextRule extends TypeBasedEqualityRule(List(Apply.path),InContext.path) {
  override def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = None
  override def applicableToTerm(solver: Solver, tm: Term): Boolean = false
}

object ContextEquality extends TermBasedEqualityRule {
  val head = ContextExt.path
  override def applicable(tm1: Term, tm2: Term): Boolean = applicable(tm1) && applicable(tm2)
  private def applicable(tm : Term) : Boolean = tm match {
    case ContextExt(_,_) => true
    case ContextConc(_,_) => true
    case ContextMap(_,_) => true
    case OMS(InContext.empty) => true
    case _ => false
  }

  override def apply(check: CheckingCallback)(tm1: Term, tm2: Term, tp: Option[Term])(implicit stack: Stack, history: History): Option[Continue[Boolean]] = {
    val ctxA = Ctx(tm1) //.sortBy(_.hashCode())
    val ctxB = Ctx(tm2) //.sortBy((_.hashCode()))
    (ctx2ls(ctxA),ctx2ls(ctxB)) match {
      case (lsA,List(Opaque(ContextMap(nc,f)))) =>
        val ntm = lsA map {
          case Elem(Apply(`f`,a)) => Elem(a)
          case Elem(_) => return None
          case Opaque(o) => return None
        }
        Some(Continue(check.check(Equality(stack,Ctx(ntm).toTerm,nc,tp))))
      case (List(Opaque(ContextMap(nc,f))),lsB) =>
        val ntm = lsB map {
          case Elem(Apply(`f`,a)) => Elem(a)
          case Elem(_) => return None
          case Opaque(o) => return None
        }
        Some(Continue(check.check(Equality(stack,Ctx(ntm).toTerm,nc,tp))))
      case (lA,lB) if lA.length == lB.length =>
        if (lA.zip(lB).forall(p => p._1 == p._2)) Some(Continue(true)) else None
      case _ => None
    }
  }

}

object ExchangeEquality extends TermBasedEqualityRule {
  val head = ContextExt.path
  override def applicable(tm1: Term, tm2: Term): Boolean = ContextEquality.applicable(tm1,tm2)

  override def apply(check: CheckingCallback)(tm1: Term, tm2: Term, tp: Option[Term])(implicit stack: Stack, history: History): Option[Continue[Boolean]] = {
    val ctxA = Ctx(tm1) //.sortBy(_.hashCode())
    val ctxB = Ctx(tm2) //.sortBy((_.hashCode()))
    val restA = Ctx(ctxB.foldLeft(ctxA)((ct,e) => ct.dropE(e).getOrElse(ct)))
    val restB = Ctx(ctxA.foldLeft(ctxB)((ct,e) => ct.dropE(e).getOrElse(ct)))
    if (restA == ctxA && restB == ctxB) None
    else if (restA.nonEmpty || restB.nonEmpty) Some(Continue(check.check(Equality(stack, Ctx(restA).toTerm, Ctx(restB).toTerm, Some(OMS(Sequent.path))))))
    else Some(Continue(true))
  }
}

object ExchangePattern extends PatternRule {
  def applicable(tm: Term): Boolean = tm match {
    case ContextExt(_,_) => true
    case ContextConc(_,_) => true
    case _ => false
  }

  override def apply(tm: Term, ctx: Context, pattern: Term, cont: (Term, Term) => Option[List[(LocalName, Term)]])(implicit solver: CheckingCallback)
  : Option[List[(LocalName, Term)]] = {
    import Ctx._
    val asCtx = Ctx(tm)
    pattern match {
      case ContextExt(c,t) =>
        asCtx.dropE(t) match {
          case Some(ct) =>
            cont(ct.toTerm,c)
          case _ => None // defer to simple matching also in case t is a matching variable, implies dropE returns None anyway
        }
      case ContextConc(ContextExt(ls1,t),ls2) =>
        asCtx.lastIndexOf(t) match {
          case -1 => None
          case i =>
            val lsa = asCtx.take(i)
            val lsb = asCtx.drop(i+1)
            cont(Ctx(lsa).toTerm,ls1) match {
              case Some(nls) =>
                cont(Ctx(lsb).toTerm,ls2).map(nls ::: _)
              case _ => None
            }
        }
      case _ => None
    }
  }
}
object Contraction extends ContextRule
object Weakening extends SubtypingRule {
  override val head: GlobalName = Sequent.baseURI ? "SequentProofs" ? "ded"
  override def applicable(tp1: Term, tp2: Term): Boolean = (tp1,tp2) match {
    case (ApplySpine(`head`,List(_,_)),ApplySpine(`head`,List(_,_))) => true
    case _ => false
  }

  override def apply(solver: Solver)(tp1: Term, tp2: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
    val ApplySpine(`head`,List(ctxAt,pA)) = tp1
    val ApplySpine(`head`,List(ctxBt,pB)) = tp2
    solver.check(Equality(stack,pA,pB,None))
    val ctxA = Ctx(ctxAt)
    val ctxB = Ctx(ctxBt)
    if (ctxB.forall(ctxA.contains)) Some(true) else None
  }
}