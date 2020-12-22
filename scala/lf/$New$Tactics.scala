// Auto-generated file for theory latin:/?NewTactics
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?NewTactics
    along with apply/unapply methods for them */
object NewTactics extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("NewTactics")
  
  object iproof extends ConstantScala {
    val parent: MPath = _path

    val name: String = "iproof"
    def apply(xs1: List[Term]): Term = OMA(OMID(this.path), xs1)
    def unapply(t: Term): Option[List[Term]] = t match {
      case OMA(OMID(this.path), (xs1: List[Term])) => Some(xs1)
      case _ => None
    }
  }
  
  object assume extends ConstantScala {
    val parent: MPath = _path

    val name: String = "assume"
    def apply(x1: OML): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[OML] = t match {
      case OMA(OMID(this.path), (x1: OML) :: Nil) => Some(x1)
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
  
  object subproof extends ConstantScala {
    val parent: MPath = _path

    val name: String = "subproof"
    def apply(xs1: List[Term]): Term = OMA(OMID(this.path), xs1)
    def unapply(t: Term): Option[List[Term]] = t match {
      case OMA(OMID(this.path), (xs1: List[Term])) => Some(xs1)
      case _ => None
    }
  }
  
  object subgoal extends ConstantScala {
    val parent: MPath = _path

    val name: String = "subgoal"
    def apply(x1: OML,x2: Term): Term = OMA(OMID(this.path), List(x1):::List(x2))
    def unapply(t: Term): Option[(OML, Term)] = t match {
      case OMA(OMID(this.path), (x1: OML) :: (x2: Term) :: Nil) => Some((x1, x2))
      case _ => None
    }
  }
  
  object bwd extends ConstantScala {
    val parent: MPath = _path

    val name: String = "bwd"
    def apply(x1: Term): Term = OMA(OMID(this.path), List(x1))
    def unapply(t: Term): Option[Term] = t match {
      case OMA(OMID(this.path), (x1: Term) :: Nil) => Some(x1)
      case _ => None
    }
  }
  
  object fwd extends ConstantScala {
    val parent: MPath = _path

    val name: String = "fwd"
    def apply(x1: OML,xs2: List[Term]): Term = OMA(OMID(this.path), List(x1):::xs2)
    def unapply(t: Term): Option[(OML, List[Term])] = t match {
      case OMA(OMID(this.path), (x1: OML) :: (xs2: List[Term])) => Some((x1, xs2))
      case _ => None
    }
  }
  
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
