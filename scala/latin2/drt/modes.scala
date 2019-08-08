package drt.modes

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.checking.ComputationRule
import info.kwarc.mmt.lf.BinaryLFConstantScala
import info.kwarc.mmt.lf.NullaryLFConstantScala
import uom._
import checking._
import objects._

import info.kwarc.mmt.lf._
import lf._

object PUnion extends BinaryLFConstantScala(DRT._path, DRT.punion.name)
object Empty extends NullaryLFConstantScala(DRT._path, DRT.empty.name)

object NormalizePunion extends ComputationRule(DRT.punion.path) with ApplicableUnder {
  def under = List(Apply.path)
  def apply(check: CheckingCallback)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Simplifiability = {
    tm match {
      case PUnion(_) =>
      case _ => return Simplifiability.NoRecurse
    }
    val args = PUnion.associativeArguments(tm).distinct
    val args2 = Empty.filter(args)
    var pos: List[Term] = Nil
    var neg: List[Term] = Nil
    var other: List[(Int,Term)] = Nil
    args2.zipWithIndex foreach {case (a,i) => a match {
      case DRT.pos(i) => pos ::= i
      case DRT.neg(i) => neg ::= i
      case a => other ::= (i+1,a)
    }}
    neg = neg diff pos
    val (otherPos,otherArgs) = other.unzip
    val argsS = pos.reverseMap(i => DRT.pos(i)) ::: neg.reverseMap(i => DRT.neg(i)) ::: otherArgs.reverse
    val tS = PUnion.assoc(Empty.term, argsS)
    if (tm != tS)
      Simplify(tS)
    else
      RecurseOnly(otherPos)
  }
}

