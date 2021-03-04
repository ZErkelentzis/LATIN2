package latin2.proving



import info.kwarc.mmt.api._
import info.kwarc.mmt.api.checking.Solver
import info.kwarc.mmt.lf.{Arrow, Pi}
import objects._


object prettyprint {

  def prettyPrintHyps(s : Solver , stk : Stack): String ={
    def loop(vs : List[VarDecl]): List[String] = vs match {
      case Nil => Nil
      case (v :: Nil) => {
        val tmp0 = s.presentObj(v.tp.get)
        (v.name + ": " + tmp0) :: Nil

      }
      case (v::vvs) => {
        val tmp = loop(vvs)
        val tmp0 = s.presentObj(v.tp.get)
        (v.name + ": " + tmp0 ) :: tmp
      }
    }
    val tmp = stk.context.getDeclarations
    loop(tmp).mkString("\n")

  }


  def printHypsRaw(stk : Stack): String ={
    def loop(vs : List[VarDecl]): List[String] = vs match {
      case Nil => Nil
      case (v :: Nil) => {
        v.toString :: Nil

      }
      case (v::vvs) => {
        val tmp = loop(vvs)
        v.toString :: tmp
      }
    }
    val tmp = stk.context.getDeclarations
    loop(tmp).mkString("\n")

  }
}
