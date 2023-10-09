package latin2.substructural

import info.kwarc.mmt.api._
import objects._
import uom._
import checking._

import lf.linear

import info.kwarc.mmt.lf._

object Common {
  // associate and drop neutral elements
  def collectWorlds(t: Term): List[Term] = t match {
    case Worlds.union(v,w) => collectWorlds(v) ::: collectWorlds(w)
    case Worlds.empty() => Nil
    case _ => List(t)
  }

  def makeUnion(ts: List[Term]) = ts match {
    case Nil => Worlds.empty()
    case hd::Nil => hd
    case hd::tl => Worlds.union(hd, makeUnion(tl))
  }
  
  def sort(ts: List[Term]) = ts.sortBy(_.hashCode)

  // commutativity
  def normalize(t: Term) = {
    val w = sort(collectWorlds(t))
    makeUnion(w)
  }

  def isBoundVar(t: Term)(implicit stack: Stack) = t match {
    case OMV(n) => stack.context.isDeclared(n)
    case _ => false
  }
}

import Common._

object NormalizeWorlds extends ComputationRule(Union.path) {
  override def applicable(tm: Term) = tm match {
    case Worlds.union(_) => true
    case _ => false
  }

  def apply(solver: CheckingCallback)(t: Term, covered: Boolean)(implicit stack: Stack, history: History) = {
    val tN = normalize(t)
    if (t hashneq tN) Simplify(tN) else Recurse
  }
}

object EquateWorlds extends TypeBasedEqualityRule(Nil, FOL.term.path) {
  def applicableToTerm(solver: Solver, tm: Term) = true
  
  def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History) = {
    var w1 = collectWorlds(tm1)
    var w2 = collectWorlds(tm2)
    var cancel: List[Term] = Nil // joint factors of w1 and w2
    w1 foreach {v =>
      if (isBoundVar(v) && w2.contains(v)) {
        cancel ::= v
      }
    }
    if (cancel.nonEmpty) {
      w1 = w1 diff cancel
      w2 = w2 diff cancel
    }
    val tm1N = makeUnion(w1)
    val tm2N = makeUnion(w2)
    if (sort(w1) == sort(w2)) {
      history += "worlds equal after normalization"
      Some(true)
    } else if ((w1 forall isBoundVar) && (w2 forall isBoundVar)) {
      solver.error("worlds inequal: " + tm1N + " and " + tm2N)
      Some(false)
    } else if (cancel.nonEmpty) {
      history += ("cancelling worlds " + cancel.mkString(", "))
      val b = solver.check(Equality(stack, tm1N, tm2N, Some(tp)))
      Some(b)
    } else {
      None
    }
  }
}