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
object Close extends UnaryLFConstantScala(DRT._path, DRT.close.name)

object NormalizePunion extends ComputationRule(DRT.punion.path) with ApplicableUnder {
  override def alternativeHeads = List(DRT.close.path)
  def under = List(Apply.path)
  def apply(check: CheckingCallback)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Simplifiability = {
    val (args, closed) = tm match {
      case PUnion(_) => (PUnion.associativeArguments(tm).distinct, false)
      case Close(m) => (PUnion.associativeArguments(m).distinct, true)
      case _ => return Simplifiability.NoRecurse
    }
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
    if (closed && other.isEmpty)
      pos = Nil
    val argsS = pos.reverseMap(i => DRT.pos(i)) ::: neg.reverseMap(i => DRT.neg(i)) ::: otherArgs.reverse
    val tUnion = PUnion.assoc(Empty.term, argsS)
    val tClosed = if (closed) {
      if (other.isEmpty)
        tUnion
      else
        Close(tUnion)
    } else
      tUnion
    if (tm != tClosed)
      Simplify(tClosed)
    else
      RecurseOnly(otherPos)
  }
}

