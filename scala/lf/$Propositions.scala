// Auto-generated file for theory latin:/?Propositions
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?Propositions
    along with apply/unapply methods for them */
object Propositions extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("Propositions")
  
  object prop extends ConstantScala {
    val parent: MPath = _path

    val name: String = "prop"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }

}
