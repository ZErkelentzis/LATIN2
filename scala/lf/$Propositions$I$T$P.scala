// Auto-generated file for theory latin:/?PropositionsITP
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?PropositionsITP
    along with apply/unapply methods for them */
object PropositionsITP extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("PropositionsITP")
  
  object proof extends ConstantScala {
    val parent: MPath = _path

    val name: String = "proof"
    def apply(xs1: List[Term]): Term = OMA(OMID(this.path), xs1)
    def unapply(t: Term): Option[List[Term]] = t match {
      case OMA(OMID(this.path), (xs1: List[Term])) => Some(xs1)
      case _ => None
    }
  }
  
  object hence extends ConstantScala {
    val parent: MPath = _path

    val name: String = "hence"
    def apply(x1: OML,x2: Term): Term = OMA(OMID(this.path), List(x1):::List(x2))
    def unapply(t: Term): Option[(OML, Term)] = t match {
      case OMA(OMID(this.path), (x1: OML) :: (x2: Term) :: Nil) => Some((x1, x2))
      case _ => None
    }
  }
  
  object suffices extends ConstantScala {
    val parent: MPath = _path

    val name: String = "suffices"
    def apply(x1: Term): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[Term] = t match {
      case OMA(OMID(this.path), (x1: Term) :: Nil) => Some(x1)
      case _ => None
    }
  }
  
  object use extends ConstantScala {
    val parent: MPath = _path

    val name: String = "use"
    def apply(x1: Term): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[Term] = t match {
      case OMA(OMID(this.path), (x1: Term) :: Nil) => Some(x1)
      case _ => None
    }
  }

}
