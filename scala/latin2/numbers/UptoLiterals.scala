package latin2.numbers

import info.kwarc._
import mmt.api._
import checking._
import objects._
import uom._

import lf._

object NatLiterals extends RepresentedRealizedType(Numbers.num.term, StandardNat)

object UptoLiterals extends TypingRule(UptoNatTypes.Upto.path) with mmt.lf.ApplicableUnderUnaryOperator {
  val operator = TypedTerms.tm.path

  def apply(solver: Solver)(tm: Term,tp: Term)(implicit stack: Stack,history: History) = {
    (tm,tp) match {
      case (NatLiterals(i),TypedTerms.tm(UptoNatTypes.Upto(NatLiterals(n)))) =>
        val r = i < n
        if (!r)
          solver.error("literal too big: " + solver.presentObj(tm))
        Some(r)
      case _ => None
    }
  }
}