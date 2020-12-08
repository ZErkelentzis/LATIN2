package latin2.proving

import info.kwarc.mmt.api.LocalName
import info.kwarc.mmt.api.objects.{Context, OMA, OMBIND, OMV, Term}



/*
abstract class LambdaTree
case class Box(var v : LambdaTree) extends LambdaTree
case class ValueNode(t : Term) extends  LambdaTree
case class HoleNode() extends  LambdaTree
case class OMANode(fun : LambdaTree , args : List[LambdaTree]) extends LambdaTree
case class OMBINDNode(bind : LambdaTree , ctx : Context , bd : LambdaTree) extends  LambdaTree



object LambdaTree{

/*  def boxToTerm(b : Box) : Term = b match {
    case Box(v) => treeToTerm(v)
  }
*/
  def treeToTerm(t : LambdaTree) : Term = t match {
    case HoleNode() => lf.Tactics.lambdahole
    case ValueNode(t) => t
    case OMANode(f , ags) => {
      val tmp = treeToTerm(f )
      val tmp0 = ags.map(x => treeToTerm(x))
      OMA(tmp , tmp0)
    }
    case OMBINDNode(b , c , bd) =>OMBIND(treeToTerm(b) , c , treeToTerm(bd))
    case Box(v) => treeToTerm(v)
  }
}


 */

object LambdaProofTerm {
  val l = LocalName("") / "P" / "1"
  val v : Term = OMV(l)
}