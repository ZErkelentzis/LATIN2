package latin2.sfol

import info.kwarc.mmt.api._
import objects._
import modules._
import symbols._
import libraries._
import frontend._
import info.kwarc.mmt.api.uom.RealizedType
import info.kwarc.mmt.lf._
import lf._

object CommonSymbols {
  val tp = Types.tp
  val tm = TypedTerms.tm
  val prop = Propositions.prop
  val ded = Proofs.ded

  /** convenience class for matching tm a1 --> ... --> tm an --> b */
  object TmFunType {
    def apply(ins: List[Term], out: Term) = FunType(ins map {a => (None, tm(a))}, out)
    def unapply(t: Term): Option[(List[Term],Term)] = {
      t match {
        case FunType(ins, out) =>
          val insTp = ins mapPartialStrict {
            case (_,TypedTerms.tm(a)) => Some(a)
            case _ => None
          }
          insTp map (x => (x,out))
        case _ => None
      }
    }
  }
  object DedList {
    def apply(fs: List[Term]) = fs map {a => ded(a)}
    def unapply(ts: List[Term]) = ts mapPartialStrict {
      case Proofs.ded(f) => Some(f)
      case _ => None
    }
  }
}

object SFOLPatterns {
  import CommonSymbols._

  object TypeDecl {
    def apply() = tp.term
    def unapply(t: Term) = t match {
      case tp.term => Some(Nil)
      case _ => None
    }
  }
  object FuncDecl {
    def apply(in: List[Term], out: Term) = {
       TmFunType(in, tm(out))
    }
    def unapply(t: Term) =  t match {
      case TmFunType(in,TypedTerms.tm(o)) =>
        Some((in,o))
      case _ => None
    }
  }
  object PredDecl {
    def apply(in: List[Term], out: Term) = {
      TmFunType(in, prop.term)
    }
    def unapply(t: Term) =  t match {
      case TmFunType(in,prop.term) => Some(in)
      case _ => None
    }
  }
  object AxDecl {
    def apply(params: Context, form: Term) = {
      Pi(params, ded(form))
    }
    def unapply(t: Term) =  t match {
      case FunType(args,Proofs.ded(f)) =>
        Some((FunType.argsAsContext(args),f))
      case _ => None
    }
  }
}

class SFOLTheoryAdapter(controller: Controller, path: MPath) {
  import SFOLPatterns._
  private lazy val init = {
    val theory = controller.globalLookup.getAs(classOf[Theory], path)
    controller.simplifier(theory)
    val constants = Theory.primitiveConstants(path, controller.globalLookup)
    println(constants)
    val typedConstants = constants collect {
      case (p,Some(tp)) => (p, tp)
    }
    (theory,typedConstants)
  }
  lazy val theory: Theory = init._1
  lazy val constants: List[(GlobalName,Term)] = init._2.toList

  // TODO FR: extend to PSFOL (so that CC can use collection types)

  def getTypeSyms = constants filter {case (p,tp) =>
    tp match {
      case TypeDecl(_) => true
      case _ => false
    }
  }
  def getFunSyms = constants filter {case (p,tp) =>
    tp match {
      case FuncDecl(_) => true
      case _ => false
    }
  }
  def getPredSyms = constants filter {case (p,tp) =>
    tp match {
      case PredDecl(_) => true
      case _ => false
    }
  }
  def getLiterals = {
    val rules = RuleSet.collectRules(controller, Context(path))
    rules.get(classOf[RealizedType]) flatMap {rt =>
      rt.synType match {
        case TypedTerms.tm(a) => List((a, rt.semType))
        case _ => Nil
      }
    }
  }
}