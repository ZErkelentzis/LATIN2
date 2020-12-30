// Auto-generated file for theory latin:/?Implication
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?Implication
    along with apply/unapply methods for them */
object Implication extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("Implication")
  
  object impl extends ConstantScala {
    val parent: MPath = _path

    val name: String = "impl"
    def apply(x0: Term,x1: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1))
    def unapply(t: Term): Option[(Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: Nil) => Some((x0, x1))
      case _ => None
    }
  }

}
