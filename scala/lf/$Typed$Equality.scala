// Auto-generated file for theory latin:/?TypedEquality
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?TypedEquality
    along with apply/unapply methods for them */
object TypedEquality extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("TypedEquality")
  
  object equal extends ConstantScala {
    val parent: MPath = _path

    val name: String = "equal"
    def apply(x0: Term,x1: Term,x2: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1):::List(x2))
    def unapply(t: Term): Option[(Term, Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: x2 :: Nil) => Some((x0, x1, x2))
      case _ => None
    }
  }

}
