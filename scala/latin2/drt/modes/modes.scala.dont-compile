package latin2.drt.modes

import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom._
import info.kwarc.mmt.lf.LFConstantScala._
import lf._

object NormalizePunion extends SimplificationRule(DRT.punion.path) {
  def apply(context: Context, tm: Term): Simplifiability = {
    val (unionTerm, closed) = tm match {
      case DRT.punion(_) => (tm,false)
      case DRT.close(m) => (m,true)
      case _ => return Simplifiability.NoRecurse
    }
    val args = DRT.punion.associativeArguments(unionTerm, Some(DRT.empty.term), true)
    var pos: List[Term] = Nil
    var neg: List[Term] = Nil
    var other: List[(Int,Term)] = Nil
    args.zipWithIndex foreach {case (a,i) => a match {
      case DRT.pos(id) => pos ::= id
      case DRT.neg(id) => neg ::= id
      case a => other ::= (i+1,a)
    }}
    neg = neg diff pos
    val (otherPos,otherArgs) = other.unzip
    if (closed && other.isEmpty)
      pos = Nil
    val argsS = pos.reverseMap(i => DRT.pos(i)) ::: neg.reverseMap(i => DRT.neg(i)) ::: otherArgs.reverse
    val tUnion = DRT.punion.assoc(DRT.empty.term, argsS)
    val tClosed = if (closed) {
      if (other.isEmpty)
        tUnion
      else
        DRT.close(tUnion)
    } else
      tUnion
    if (tm != tClosed)
      Simplify(tClosed)
    else
      RecurseOnly(otherPos)
  }
}
