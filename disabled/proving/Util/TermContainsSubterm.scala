package proving.Util

import info.kwarc.mmt.api.checking.{History, Solver}
import info.kwarc.mmt.api.objects.{Context, Equality, OMA, OML, OMV, Stack, Term, Traverser}


object TermContainsSubterm {

  def stepInside(t : Term ,  subt : Term ,solver : Solver , s : Stack , h : History) : Boolean = t match {
    case OMV(h) => false
    case OML(a,b,c,d,e) =>{

    }
    case OMA(f, args) => {
      contains(f , subt , solver, s , h) && args.map(x => contains(x, subt, solver, s, h)).forall(curr => curr)
    }
    case
  }

  def contains(t : Term , subt : Term, solver : Solver, s : Stack , h : History) : Boolean = solver.check(Equality(s , t , subt , None)) {
    case true => {
      true
    }
    case false => {
      stepInside(t , subt , solver , s , h )
    }
  }


}
