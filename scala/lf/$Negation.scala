// Auto-generated file for theory latin:/?Negation
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?Negation
    along with apply/unapply methods for them */
object Negation extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("Negation")
  
  object not extends ConstantScala {
    val parent: MPath = _path

    val name: String = "not"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }

}
