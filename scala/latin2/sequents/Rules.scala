package latin2.sequents

import info.kwarc.mmt.api._
import checking._
import objects._
import uom._
import Conversions._
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

sealed trait ContextElem {
  val tm : Term
}
case class Elem(tm : Term) extends ContextElem
case class Opaque(tm : Term) extends ContextElem

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

class ContextRule extends TypeBasedEqualityRule(List(Apply.path),InContext.path) {
  override def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = None
  override def applicableToTerm(solver: Solver, tm: Term): Boolean = false
}

object ContextEquality extends TypeBasedEqualityRule(Nil,Sequent.path) {

  def applicableToTerm(solver : Solver,tm : Term) : Boolean = tm match {
    case ContextExt(_,_) => true
    case ContextConc(_,_) => true
    case ContextMap(_,_) => true
    case OMS(InContext.empty) => true
    case _ => false
  }

  override def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
    val ctxA = Ctx(tm1) //.sortBy(_.hashCode())
    val ctxB = Ctx(tm2) //.sortBy((_.hashCode()))
    (ctx2ls(ctxA),ctx2ls(ctxB)) match {
      case (lsA,List(Opaque(ContextMap(nc,f)))) =>
        val ntm = lsA map {
          case Elem(Apply(`f`,a)) => Elem(a)
          case Elem(_) => return None
          case Opaque(o) => return None
        }
        Some(solver.check(Equality(stack,Ctx(ntm).toTerm,nc,Some(tp))))
      case (List(Opaque(ContextMap(nc,f))),lsB) =>
        val ntm = lsB map {
          case Elem(Apply(`f`,a)) => Elem(a)
          case Elem(_) => return None
          case Opaque(o) => return None
        }
        Some(solver.check(Equality(stack,Ctx(ntm).toTerm,nc,Some(tp))))
      case (lA,lB) if lA.length == lB.length =>
        if (lA.zip(lB).forall(p => p._1 == p._2)) Some(true) else None
      case _ => None
    }
  }
}

object ExchangeEquality extends TypeBasedEqualityRule(Nil,Sequent.path) {
  override def shadowedRules: List[Rule] = List(ContextEquality)
  //val head = ContextExt.path
  //override def applicableToTerm(tm: Term): Boolean = ContextEquality.applicable(tm)
  override def applicableToTerm(solver: Solver, tm: Term): Boolean = ContextEquality.applicableToTerm(solver,tm)

  override def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
    (try {applyI(solver)(tm1,tm2,tp)} catch {
      case DelayJudgment(_) => None
    }) match {
      case Some(a) => Some(a)
      case _ => applyI(solver)(tm2,tm1,tp)
    }
  }

  def applyI(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
    val ctxA = Ctx(tm1) //.sortBy(_.hashCode())
    val ctxB = Ctx(tm2) //.sortBy((_.hashCode()))
    val restA = Ctx(ctxB.foldLeft(ctxA)((ct,e) => ct.dropE(e).getOrElse(ct)))
    val restB = Ctx(ctxA.foldLeft(ctxB)((ct,e) => ct.dropE(e).getOrElse(ct)))
    if (restA.isEmpty && restB.isEmpty) return Some(true)
    if (restA != ctxA || restB != ctxB) return Some(solver.check(Equality(stack, Ctx(restA).toTerm, Ctx(restB).toTerm, Some(tp))))
    if (!ctxB.isComplete)
      throw DelayJudgment("Solution not yet possible")
    if (ctxA.isComplete)
      return None
    // ctxB is a completely known context, and hence all Elems in ctxA are unknowns (or the contexts are *not* equal)
    val opaques = ctxA.collect {case Opaque(tm) => tm}
    val elems = ctxA.collect {case Elem(tm) => Elem(tm)}
    if (elems.isEmpty) {
      opaques match {
        case List(ContextMap(c,f)) => // unapply the map
          unapplyMap(solver,f,ctx2ls(ctxB).map(_.asInstanceOf[Elem].tm)) match {
            case Some(ls) =>
              return Some(solver.check(Equality(stack,c,Ctx(ls.map(Elem)).toTerm,Some(tp))))
            case _ =>
          }
        case _ =>
      }
    }
    if (elems.isEmpty)
      return None
    if (elems.length == ctxB.length && opaques.length == 1) { // opaques is empty context
      solver.check(Equality(stack,opaques.head,OMS(InContext.empty),Some(tp)))
      return Some(solver.check(Equality(stack,Ctx(elems).toTerm,ctxB.toTerm,Some(tp))))
    }
    if (ctxB.distinct.length == 1) { // all elements in ctxA are the same
      val (nctxA,nctxB) = ctxB.foldLeft((ctxA,ctxB)){ case ((iA,iB),Elem(t)) =>
        iA.collectFirst{case e@Elem(_) => e} match {
          case Some(Elem(e)) =>
            solver.check(Equality(stack,e,t,None))
            (iA.dropE(e).get,iB.dropE(t).get)
          case _ => (iA,iB)
        }
      }
      return Some(solver.check(Equality(stack,nctxA.toTerm,nctxB.toTerm,Some(tp))))
    }
    elems.collectFirst {
      case Elem(t) if ctxB.count(e => termmatch(solver,t,e.asInstanceOf[Elem].tm)) == 1 =>
        (t,ctxB.find(e => termmatch(solver,t,e.asInstanceOf[Elem].tm)).get)
    } match {
      case Some((t,e)) =>
        solver.check(Equality(stack,t,e.asInstanceOf[Elem].tm,None))
        Some(solver.check(Equality(stack,ctxA.dropE(t).get.toTerm,ctxB.dropE(e).get.toTerm,Some(tp))))
      case _ =>
        throw DelayJudgment("Solution not yet possible")
    }
  }



  def unapplyMap(solver : Solver,f : Term, ct : List[Term])(implicit stack: Stack, history: History) : Option[List[Term]] = ct match {
    case Nil => Some(Nil)
    case t :: rest =>
      termmatchI(solver,Apply(f,OMV(""/"Ctx"/"match")),t)(stack ++ VarDecl(""/"Ctx"/"match"),history) match {
        case Some(ls) => ls.collectFirst {case (OMV(n),it) if n.toString == "/Ctx/match" => it} match {
          case Some(it) =>
            unapplyMap(solver,f,rest).map(it :: _)
          case _ => None
        }
        case _ => None
      }
  }

  def termmatch(solver : Solver,tm1 : Term,tm2 : Term)(implicit stack: Stack, history: History) =
    termmatchI(solver,tm1,tm2).isDefined

  def termmatchI(solver : Solver,tm1 : Term,tm2 : Term)(implicit stack: Stack, history: History) : Option[List[(Term,Term)]] =
    solver.safeSimplifyUntil(tm1,tm2)((t1,t2) => termmatchII(solver,t1,t2))._3

  def termmatchII(solver : Solver,tm1 : Term,tm2 : Term)(implicit stack: Stack, history: History) : Option[List[(Term,Term)]] = (tm1,tm2) match {
    case (a,b) if a == b => Some(Nil)
    case (OMV(i),t) if solver.getUnsolvedVariables.isDeclared(i) || i.toString == "/Ctx/match" => Some(List((OMV(i),t)))
    case (a@OMA(OMV(i),_),t) if solver.getUnsolvedVariables.isDeclared(i) => Some(List((a,t)))
    case (t,OMV(i)) if solver.getUnsolvedVariables.isDeclared(i) || i.toString == "/Ctx/match" => Some(List((OMV(i),t)))
    case (t,a@OMA(OMV(i),_)) if solver.getUnsolvedVariables.isDeclared(i) => Some(List((a,t)))
    case (OMA(f,args1),OMA(g,args2)) if f == g && args1.length == args2.length =>
      Some(args1.zip(args2).foldLeft(Nil.asInstanceOf[List[(Term,Term)]]){case (ls,(p1,p2)) => termmatchI(solver,p1,p2) match {
        case Some(lsi) => ls ::: lsi
        case _ => return None
      } })
    case _ => None
  }
}

object Contraction extends ContextRule
object Weakening extends SubtypingRule {
  override val head: GlobalName = Sequent.baseURI ? "SequentProofs" ? "ded"
  override def applicable(tp1: Term, tp2: Term): Boolean = (tp1,tp2) match {
    case (ApplySpine(OMS(`head`),List(_,_)),ApplySpine(OMS(`head`),List(_,_))) => true
    case _ => false
  }

  override def apply(solver: Solver)(tp1: Term, tp2: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
    val ApplySpine(OMS(`head`),List(ctxAt,pA)) = tp1
    val ApplySpine(OMS(`head`),List(ctxBt,pB)) = tp2
    val gammaA = Ctx(ctxAt)
    val gammaB = Ctx(ctxBt)
    val deltaA = Ctx(pA)
    val deltaB = Ctx(pB)
    val exchange = solver.rules.getAll.toList.contains(ExchangeEquality)
    if (exchange) applyExchange(gammaA,deltaA,gammaB,deltaB)(solver) else apply(gammaA,deltaA,gammaB,deltaB)(solver)
  }

  def applyExchange(gammaA : Ctx, deltaA : Ctx, gammaB : Ctx, deltaB : Ctx)(solver : Solver)(implicit stack: Stack, history: History): Option[Boolean] = {
    val frees = gammaA.toTerm.freeVars ::: gammaB.toTerm.freeVars ::: deltaA.toTerm.freeVars ::: deltaB.toTerm.freeVars
    val unknowns = frees.filter(n => solver.getUnsolvedVariables.isDeclared(n))
    if (unknowns.nonEmpty)
      return None
    val gamma = gammaA.forall(e1 => gammaB.count(e2 => ExchangeEquality.termmatch(solver, e1.tm, e2.tm)) == 1)
    val delta = deltaA.forall(e1 => deltaB.count(e2 => ExchangeEquality.termmatch(solver, e1.tm, e2.tm)) == 1)
    if (gamma && delta)
      return Some(true)
    None
  }

  def apply(gammaA : Ctx, deltaA : Ctx, gammaB : Ctx, deltaB : Ctx)(solver : Solver)(implicit stack: Stack, history: History): Option[Boolean] = {
    None // TODO
  }
}


/* object ExchangeSolution extends ValueSolutionRule(ContextExt.path) {
  override def applicable(t: Term): Option[Int] = None /* t match {
    case ContextExt(_,_) => Some(2)
    case _ => None
  } */

  override def apply(j: Equality): Option[(Equality, String)] = {
    val ctxA = Ctx(j.tm1)
    val ctxB = Ctx(j.tm2)
    val (restA,restB) = ctxB.foldLeft((ctxA,ctxB)){case ((ctxAn,ctxBn),e) =>
      ctxAn.dropE(e) match {
        case Some(v) => (v,ctxBn.dropE(e).get)
        case _ => (ctxAn,ctxBn)
      }
    }
    if (restA == ctxA) {
      if (ctxB.isComplete && (ctxB.distinct.length == 1)) {
        ctxA.find(_.isInstanceOf[Elem]) match {
          case Some(Elem(t)) =>
            Some(Equality(j.stack,t,ctxB.head.asInstanceOf[Elem].tm,None),"")
          case _ =>
            throw DelayJudgment("Solution not yet possible")
        }
      } else
        throw DelayJudgment("Solution not yet possible")
    } else
      Some((Equality(j.stack,restA.toTerm,restB.toTerm,j.tpOpt),""))
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

 */