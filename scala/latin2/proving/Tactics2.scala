package latin2.proving
/*
import info.kwarc.mmt.api.LocalName
import info.kwarc.mmt.api.objects.{Context, Equality, OMID, OML, OMS, OMV, PlainSubstitutionApplier, Sub, Substitution, Term, Typing}
import info.kwarc.mmt.lf.{Apply, Lambda, Typed}
import lf.{Implication, ImplicationNDI, Proofs, Tactics, Tactics2, TypedTerms, TypedUniversalQuantification, Types}

*/
/*
object AssumeTactic extends SimpleProofStepRule(Tactics2.assume.path) {
  def apply( step: Term ,  goal: ProofGoal, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case Tactics2.assume(OML(nm , None , None , _  , _ )) => {
        goal.tp match {
          case Proofs.ded(Implication.impl(f,g)) =>{
            val df = Proofs.ded(f)
            val pg = ProofGoal(goal.stack ++ OMV(nm) % df, Proofs.ded(g), goal.history + "assume")

            //new

            val newFVar = Context.pickFresh(prover.solver.checkingUnit.context ++ goal.stack.context, LocalName("??"))
            val newLam =  ImplicationNDI.impI(df, g , Lambda(nm , df , OMV(newFVar._1)))
            Some(List(pg) , newLam , List(OMV(newFVar._1)))
          }
        }
      }
      case _ => prover.solver.error("assume has not the right form")(goal.history) ; None
    }
  }
}

*/
/*
object AssumeTactic extends ProofStepRule(Tactics2.assume.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    step match {
      case Tactics2.assume(OML(nm , None , None , _  , _ )) => {
        goal.tp match {
          case Proofs.ded(Implication.impl(f,g)) =>{
            val df = Proofs.ded(f)
            val pg = ProofGoal(goal.stack ++ OMV(nm) % df, Proofs.ded(g), goal.history + "assume")

            //new

            val lg = prover.lambdaGoals.head
            val tmplgs = prover.lambdaGoals.tail
            val newFVar = Context.pickFresh(prover.solver.checkingUnit.context ++ goal.stack.context, LocalName("??"))
            val sb : Substitution =  (Substitution( Sub(lg.name , ImplicationNDI.impI(df, g , Lambda(nm , df , OMV(newFVar._1))))))
            val newlam = PlainSubstitutionApplier(prover.lambdaProofTerm , sb)
            prover.lambdaProofTerm = newlam
            prover.lambdaGoals = OMV(newFVar._1) :: tmplgs
/*           val newHole = Box(HoleNode())
            val lambdat : LambdaTree = OMBINDNode(ValueNode (Lambda.term) , OMV(nm) % df , newHole )
            val tmp = OMANode(ValueNode(OMID(ImplicationNDI.impI.path)), List(ValueNode(df) , ValueNode(g) , lambdat ) )
            prover.lambdaGoalsHistory = prover.lambdaGoals :: prover.lambdaGoalsHistory
            prover.calcLambdaGoalsHistory = List(0)  :: prover.calcLambdaGoalsHistory
            prover.lambdaGoals = newHole :: tmplgs
            lg.v = tmp
*/
            //new

            Some(List(pg))
          }
        }
      }
      case _ => prover.solver.error("assume has not the right form")(goal.history) ; None
    }
  }
}



object UseTactic extends ProofStepRule(Tactics2.use.path) {
  def apply(prover: ImperativeProver, step: Term) = {
    val Tactics2.use(p) = step
    val pC = prover.clean(goal.stack, p)
    prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term")

    //new
/*    prover.lambdaGoalsHistory = prover.lambdaGoals :: prover.lambdaGoalsHistory
    prover.calcLambdaGoalsHistory = List(0)  :: prover.calcLambdaGoalsHistory
    val lg = prover.lambdaGoals.head
    prover.lambdaGoals = prover.lambdaGoals.tail
    lg.v  = ValueNode(pC)
*/


    //new
    Some(Nil)
  }
}
*/
/*
object FixTactic extends ProofStepRule(Tactics2.fix.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = step match {
    case Tactics2.fix(OML(n, None, None, _, _)) => {
      goal.tp match {
        case Proofs.ded(TypedUniversalQuantification.forall(tp, body)) => {
          val ntp = TypedTerms.tm(tp)
          val stackN = goal.stack ++ OMV(n) % ntp
          val bodyN = prover.solver.simplify(Apply(body, OMV(n)))(stackN, goal.history)
        }
      }
      case _ => prover.solver.error("fix has not the right form: " + step.toString())(goal.history); None
*/
      /*   val Tactics2.fix(OML(n,tO,_,_,_)) = step
    goal.tp match {
      case Proofs.ded(TypedUniversalQuantification.forall(tp, body)) =>
        val ntp = TypedTerms.tm(tp)
        val stackN = goal.stack ++ OMV(n) % ntp
        val bodyN = prover.solver.simplify(Apply(body, OMV(n)))(stackN, goal.history)
        tO.foreach {t =>
          val tC = prover.clean(goal.stack, t)
          prover.solver.check(Equality(goal.stack, tC, tp, Some(Types.tp.term)))(goal.history + "fix must equal quantification domain")
        }
        val pg = ProofGoal(stackN, Proofs.ded(bodyN), goal.history + "fix")
        Some(List(pg))
      case tp =>
        prover.solver.error("only applicable to universally quantified goal: found " + prover.solver.presentObj(tp))(goal.history)
        None
    }
  }


    }
  }
}

*/
