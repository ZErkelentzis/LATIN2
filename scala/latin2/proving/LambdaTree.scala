package latin2.proving

import info.kwarc.mmt.api.objects.{OMA, Term}

case class Box(v : LambdaTree)

abstract class LambdaTree
case class ValueNode(t : Term) extends  LambdaTree
case class HoleNode() extends  LambdaTree
case class OMANode(fun : Box , args : List[Box]) extends LambdaTree



object LambdaTree{

  def boxToTerm(b : Box) : Term =  {

  }

  def treeToTerm(t : LambdaTree) : Term = {

  }
}