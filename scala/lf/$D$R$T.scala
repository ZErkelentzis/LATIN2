// Auto-generated file for theory latin:/?DRT
package lf
import info.kwarc.mmt.api._
import objects._
import uom._
import ConstantScala._

import info.kwarc.mmt.lf._
/** Convenience functions for the MMT URIs of the declarations in the theory latin:/?DRT
    along with apply/unapply methods for them */
object DRT extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("DRT")
  
  object dr extends ConstantScala {
    val parent: MPath = _path

    val name: String = "dr"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object mode extends ConstantScala {
    val parent: MPath = _path

    val name: String = "mode"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object pos extends ConstantScala {
    val parent: MPath = _path

    val name: String = "pos"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object neg extends ConstantScala {
    val parent: MPath = _path

    val name: String = "neg"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object empty extends ConstantScala {
    val parent: MPath = _path

    val name: String = "empty"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object punion extends ConstantScala {
    val parent: MPath = _path

    val name: String = "punion"
    def apply(x0: Term,x1: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1))
    def unapply(t: Term): Option[(Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: Nil) => Some((x0, x1))
      case _ => None
    }
  }
  
  object mequal extends ConstantScala {
    val parent: MPath = _path

    val name: String = "mequal"
    def apply(x0: Term,x1: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1))
    def unapply(t: Term): Option[(Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: Nil) => Some((x0, x1))
      case _ => None
    }
  }
  
  object refl extends ConstantScala {
    val parent: MPath = _path

    val name: String = "refl"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object capture extends ConstantScala {
    val parent: MPath = _path

    val name: String = "capture"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object close extends ConstantScala {
    val parent: MPath = _path

    val name: String = "close"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object close_underscore_pos extends ConstantScala {
    val parent: MPath = _path

    val name: String = "close_pos"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object close_underscore_neg extends ConstantScala {
    val parent: MPath = _path

    val name: String = "close_neg"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object close_underscore_empty extends ConstantScala {
    val parent: MPath = _path

    val name: String = "close_empty"
    def apply(): Term = OMID(this.path)
    def unapply(t: Term): Option[Unit] = t match {
      case OMID(this.path) => Some(())
      case _ => None
    }
  }
  
  object close_underscore_close extends ConstantScala {
    val parent: MPath = _path

    val name: String = "close_close"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object drs extends ConstantScala {
    val parent: MPath = _path

    val name: String = "drs"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object tm extends ConstantScala {
    val parent: MPath = _path

    val name: String = "tm"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object v extends ConstantScala {
    val parent: MPath = _path

    val name: String = "v"
    def apply(xs1: List[Term]): Term = OMA(OMID(this.path), xs1)
    def unapply(t: Term): Option[List[Term]] = t match {
      case OMA(OMID(this.path), (xs1: List[Term])) => Some(xs1)
      case _ => None
    }
  }
  
  object cond extends ConstantScala {
    val parent: MPath = _path

    val name: String = "cond"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }
  
  object atomic extends ConstantScala {
    val parent: MPath = _path

    val name: String = "atomic"
    def apply(x0: Term,x1: Term,x2: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1):::List(x2))
    def unapply(t: Term): Option[(Term, Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: x2 :: Nil) => Some((x0, x1, x2))
      case _ => None
    }
  }
  
  object merge extends ConstantScala {
    val parent: MPath = _path

    val name: String = "merge"
    def apply(x0: Term,x1: Term,x2: Term,x3: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1):::List(x2):::List(x3))
    def unapply(t: Term): Option[(Term, Term, Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: x2 :: x3 :: Nil) => Some((x0, x1, x2, x3))
      case _ => None
    }
  }
  
  object seqmerge extends ConstantScala {
    val parent: MPath = _path

    val name: String = "seqmerge"
    def apply(x0: Term,x1: Term,x2: Term,x3: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1):::List(x2):::List(x3))
    def unapply(t: Term): Option[(Term, Term, Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: x2 :: x3 :: Nil) => Some((x0, x1, x2, x3))
      case _ => None
    }
  }
  
  object and extends ConstantScala {
    val parent: MPath = _path

    val name: String = "and"
    def apply(x0: Term,x1: Term,x2: Term,x3: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1):::List(x2):::List(x3))
    def unapply(t: Term): Option[(Term, Term, Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: x2 :: x3 :: Nil) => Some((x0, x1, x2, x3))
      case _ => None
    }
  }
  
  object dneg extends ConstantScala {
    val parent: MPath = _path

    val name: String = "dneg"
    def apply(x0: Term,x1: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1))
    def unapply(t: Term): Option[(Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: Nil) => Some((x0, x1))
      case _ => None
    }
  }
  
  object dimpl extends ConstantScala {
    val parent: MPath = _path

    val name: String = "dimpl"
    def apply(x0: Term,x1: Term,x2: Term,x3: Term): Term = ApplyGeneral(OMID(this.path), List(x0):::List(x1):::List(x2):::List(x3))
    def unapply(t: Term): Option[(Term, Term, Term, Term)] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: x1 :: x2 :: x3 :: Nil) => Some((x0, x1, x2, x3))
      case _ => None
    }
  }
  
  object idref extends ConstantScala {
    val parent: MPath = _path

    val name: String = "idref"
    def apply(x0: Term): Term = ApplyGeneral(OMID(this.path), List(x0))
    def unapply(t: Term): Option[Term] = t match {
      case ApplyGeneral(OMID(this.path), x0 :: Nil) => Some(x0)
      case _ => None
    }
  }

}
