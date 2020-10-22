// Auto-generated file for theory latin:/?PLITP
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?PLITP
    along with apply/unapply methods for them */
object PLITP extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("PLITP")
  
  object assume extends ConstantScala {
    val parent: MPath = _path

    val name: String = "assume"
    def apply(x1: OML): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[OML] = t match {
      case OMA(OMID(this.path), (x1: OML) :: Nil) => Some(x1)
      case _ => None
    }
  }
  
  object cases extends ConstantScala {
    val parent: MPath = _path

    val name: String = "cases"
    def apply(xs1: List[Term]): Term = OMA(OMID(this.path), xs1)
    def unapply(t: Term): Option[List[Term]] = t match {
      case OMA(OMID(this.path), (xs1: List[Term])) => Some(xs1)
      case _ => None
    }
  }

}
