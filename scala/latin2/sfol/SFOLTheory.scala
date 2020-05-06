package latin2.sfol

import info.kwarc.mmt.api._
import objects._
import modules._
import symbols._
import libraries._
import frontend._

import info.kwarc.mmt.lf._

import lf._

object CommonSymbols {
  val tp = Types.tp
  val tm = TypedTerms.tm
  val prop = Propositions.prop
  val ded = Proofs.ded

  object TmList {
    def apply(tps: List[Term]) = tps map {a => tm(a)}
    def unapply(tms: List[Term]) = tms mapPartialStrict {
      case TypedTerms.tm(a) => Some(a)
      case _ => None
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
       Arrow(in map {i => tm(i)}, tm(out))
    }
    def unapply(t: Term) =  t match {
      case FunType(TmList(in),TypedTerms.tm(out)) =>
        Some((in,out))
      case _ => None
    }
  }
  object PredDecl {
    def apply(in: List[Term], out: Term) = {
      Arrow(in map {i => tm(i)}, prop.term)
    }
    def unapply(t: Term) =  t match {
      case FunType(TmList(in),prop.term) => Some(in)
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
    var constants : List[Constant] = Nil
    controller.globalLookup.forDeclarationsInScope(OMMOD(path)) {(_,_,d) =>
      d match {
        case c: Constant => constants ::= c
        case _ =>
      }
    }
    (theory,constants.reverse)
  }
  lazy val theory: Theory = init._1
  lazy val declarations: List[Constant] = init._2

  def getTypeSyms: List[Constant] = declarations filter {d =>
    d.tp match {
      case Some(TypeDecl(_)) => true
      case _ => false
    }
  }
  def getFunSyms:  List[Constant] = declarations filter {d =>
    d.tp match {
      case Some(FuncDecl(_)) => true
      case _ => false
    }
  }
  def getPredSyms: List[Constant] = declarations filter {d =>
    d.tp match {
      case Some(PredDecl(_)) => true
      case _ => false
    }
  }
}