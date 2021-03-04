package proving.AutoTools.GenericPresburger

import info.kwarc.mmt.api.objects.Term

class GenericPresburger(val zeroT : Term , val oneT : Term , var hyps : List[Term] , var goal : Term) {

  abstract class InternalRep
  case class zero() extends  InternalRep
  case class one() extends  InternalRep

}
