package proving.Rewriting

import info.kwarc.mmt.api.checking.Solver
import info.kwarc.mmt.api.objects.{Context, OMA, OMV, PlainSubstitutionApplier, Term, Traverser}
import info.kwarc.mmt.lf.{Lambda, Pi}
import latin2.proving.{ImperativeProver, ProofGoal, SimpleProofStepRule}
import lf.TacticsLF


case class ComplexSubstitution(original : Term , replacement : Term)






object LFRewriteEngine {
  def rewrite(t : Term , cs : ComplexSubstitution, ctx : Context): Term = {
    if (cs.original == t){
      cs.replacement
    }else {
      t match {
        case Lambda(vn , tp , body) => {
          val (newname , subst) = Context.pickFresh(ctx, vn)
          val newcs = ComplexSubstitution(cs.original.substitute(subst)(PlainSubstitutionApplier) , cs.replacement)
          rewrite(body , newcs , ctx)
        }
        case Pi(vn , tp , body) => {
          val (newname , subst) = Context.pickFresh(ctx, vn)
          val newcs = ComplexSubstitution(cs.original.substitute(subst)(PlainSubstitutionApplier) , cs.replacement)
          rewrite(body , newcs , ctx)
        }
        case OMA(f , args) => {
          cs.original match {
            case OMA(f0, args0) =>if (OMA(f , args.take(args0.length)) == cs.original) { OMA(cs.replacement , args.drop(args0.length))   } else { OMA( rewrite(f , cs, ctx) , args.map(x => rewrite(x, cs, ctx)) )  }
            case _ =>t
          }
        }
      }
    }
  }
}


object RewriteTactic extends SimpleProofStepRule(TacticsLF.rewrite.path){
  override def apply(t: Term, g:  ProofGoal , lgl : OMV , lterm : Term , ip: ImperativeProver): Option[(scala.List[ProofGoal], Term, scala.List[OMV])] = {
    
  }
}
