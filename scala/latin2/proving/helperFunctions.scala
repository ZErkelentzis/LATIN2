package latin2.proving

import info.kwarc.mmt.api.LocalName
import info.kwarc.mmt.api.objects.{OMA, OMAorAny, OMID, OML, OMV, Substitution, Term}
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
/*
  def containsHole(t : Term): Boolean = t match{
    case OMID(holeBuild.path) => true
    case OMA(s , ls) =>{
      containsHole(s) || ls.foldRight(false)((x,y) => y || containsHole(x))
    }
    case _ => false
  }
*/

  def removeDed(t : Term) : Term = t match {
    case Proofs.ded(trm) => trm
    case _ => t
  }


  def simpleSubstitution (l : LocalName ,orig  : Term  , rep : Term) : Term  = orig match {
    case OMV(n) => if (n == l) {rep} else orig
    case OML(n , _ , _ , _ , _) => {
      if (n == l) {
        rep
      } else {
        orig
      }
    }
    case OMA(f , ags ) => {
      OMA(simpleSubstitution(l , f , rep) , ags.map(x => simpleSubstitution(l , x , rep)) )
    }
    case OMID(p) => {
      if (p.name == l ) {rep} else orig
    }
    case OMAorAny(f , ags ) => {
      OMA(simpleSubstitution(l , f , rep) , ags.map(x => simpleSubstitution(l , x , rep)) )
    }
    case _ => orig
  }

  def simpleSubstituteRw(orig : Term , l : Term , r : Term) : Term = (orig == l) match {
    case true => r
    case false => orig match {
      case OMA(f , ags) => OMA(simpleSubstituteRw(f , l , r) , ags.map(x => simpleSubstituteRw(x , l , r)))
      case _ => orig
    }
  }


  def isNumberTerm(t : Term) : Boolean = t match {
    case OMV(n) => n.toString.forall(c => c.isDigit)
    case OML(n , None , None , None , None) => n.toString.forall(c => c.isDigit)
    case _ => false
  }

}
