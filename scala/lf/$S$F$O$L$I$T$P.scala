// Auto-generated file for theory latin:/?SFOLITP
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?SFOLITP
    along with apply/unapply methods for them */
object SFOLITP extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("SFOLITP")
  
  object fix extends ConstantScala {
    val parent: MPath = _path

    val name: String = "fix"
    def apply(x1: OML): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[OML] = t match {
      case OMA(OMID(this.path), (x1: OML) :: Nil) => Some(x1)
      case _ => None
    }
  }

}
