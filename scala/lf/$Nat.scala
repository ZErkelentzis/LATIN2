// Auto-generated file for theory latin:/?Nat
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?Nat
    along with apply/unapply methods for them */
object Nat extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("Nat")
  
  object nat extends ConstantScala {
    val parent: MPath = _path

    val name: String = "nat"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object Nat extends ConstantScala {
    val parent: MPath = _path

    val name: String = "Nat"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object zero extends ConstantScala {
    val parent: MPath = _path

    val name: String = "zero"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object succ extends ConstantScala {
    val parent: MPath = _path

    val name: String = "succ"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object even extends ConstantScala {
    val parent: MPath = _path

    val name: String = "even"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object uneven extends ConstantScala {
    val parent: MPath = _path

    val name: String = "uneven"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }

}
