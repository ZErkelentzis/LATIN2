// Auto-generated file for theory latin:/?TacticsLF
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?TacticsLF
    along with apply/unapply methods for them */
object TacticsLF extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("TacticsLF")
  
  object assumelfx extends ConstantScala {
    val parent: MPath = _path

    val name: String = "assumelfx"
    def apply(x1: OML): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[OML] = t match {
      case OMA(OMID(this.path), (x1: OML) :: Nil) => Some(x1)
      case _ => None
    }
  }
  
  object theoremLF extends ConstantScala {
    val parent: MPath = _path

    val name: String = "theoremLF"
    def apply(x1: Term,x2: Term): Term = OMA(OMID(this.path), List(x1):::List(x2))
    def unapply(t: Term): Option[(Term, Term)] = t match {
      case OMA(OMID(this.path), (x1: Term) :: (x2: Term) :: Nil) => Some((x1, x2))
      case _ => None
    }
  }
  
  object fixlfx extends ConstantScala {
    val parent: MPath = _path

    val name: String = "fixlfx"
    def apply(x1: OML): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[OML] = t match {
      case OMA(OMID(this.path), (x1: OML) :: Nil) => Some(x1)
      case _ => None
    }
  }
  
  object build extends ConstantScala {
    val parent: MPath = _path

    val name: String = "build"
    def apply(x1: Term): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[Term] = t match {
      case OMA(OMID(this.path), (x1: Term) :: Nil) => Some(x1)
      case _ => None
    }
  }
  
  object leth extends ConstantScala {
    val parent: MPath = _path

    val name: String = "leth"
    def apply(x1: Term,x2: OML): Term = OMA(OMID(this.path), List(x1):::List(x2))
    def unapply(t: Term): Option[(Term, OML)] = t match {
      case OMA(OMID(this.path), (x1: Term) :: (x2: OML) :: Nil) => Some((x1, x2))
      case _ => None
    }
  }

}
