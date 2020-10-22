// Auto-generated file for theory latin:/?Proofs
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?Proofs
    along with apply/unapply methods for them */
object Proofs extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("Proofs")
  
  object ded extends ConstantScala {
    val parent: MPath = _path

    val name: String = "ded"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object inconsistent extends ConstantScala {
    val parent: MPath = _path

    val name: String = "inconsistent"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object inconsistentE extends ConstantScala {
    val parent: MPath = _path

    val name: String = "inconsistentE"
    def apply(x0: Term,x1: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1))
    def unapply(t: Term): Option[(Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: Nil) => Some((x0, x1))
      case _ => None
    }
  }

}
