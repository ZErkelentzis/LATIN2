package latin2.proving

import info.kwarc.mmt.api.LocalName
import info.kwarc.mmt.api.objects.{OML, Term}
import lf.{Implication, Proofs, TypedUniversalQuantification}

object helperFunctions {

  abstract class NamedOrUnnamedTerm

  case class UnnamedHypothesis(t : Term) extends  NamedOrUnnamedTerm
  case class NamedHypothesis(ln : LocalName, t : Term) extends  NamedOrUnnamedTerm


  def deconstructImps(t : Term) : List[NamedOrUnnamedTerm] = t match {
    case Implication.impl(h ,tl) => {
      val tmp = deconstructImps(tl )
      UnnamedHypothesis(h) :: tmp
    }
    case TypedUniversalQuantification.forall(OML(nn, None, None, _, _), tl) => {
      val tmp = deconstructImps(tl)
      NamedHypothesis(nn , tl) :: tmp
    }
    case h => List()
  }

  def getHyps(t : Term) : List[NamedOrUnnamedTerm] = t match {
    case Proofs.ded(trm) => {
      deconstructImps(trm)
    }
  }


  def getNamedTerms(xs : List[Term]) : Option[List[NamedOrUnnamedTerm]] = xs match{
    case OML(nn , None , _ , _ , _) :: OML(_,_,_,_,_) :: zs => None
    case OML(nn , None , _ , _ , _) :: trm :: zs => {
      val tmp = getNamedTerms(zs)
      tmp match {
        case Some(res) => {
          Some(NamedHypothesis(nn, trm) :: res)
        }
        case None => None
      }
    }
  }



  def getConclusion(t : Term) : Term = {

    def loop(tt : Term) : Term = tt match {
      case Implication.impl(_ , c) => {
        loop(c)
      }
      case trm => trm
    }

    t match {
      case Proofs.ded(thm) => {
        loop(thm)
      }
      case trm => loop(trm)
    }
  }



}
