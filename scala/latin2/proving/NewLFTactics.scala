package latin2.proving

import info.kwarc.mmt.api.checking.{History, InferenceAndTypingRule, Solver}
import info.kwarc.mmt.api.objects.{Context, Equality, OML, OMV, SmartSubstitutionApplier, Stack, Sub, Substitution, Term, Typing}
import info.kwarc.mmt.lf.{Apply, ApplySpine, Arrow, Lambda, OfType, Pi}
import lf.{NewTactics, Proofs, PropositionsITP, TacticsLF, TypedTerms, TypedUniversalQuantification, TypedUniversalQuantificationND}


object AssumelfxTactic extends SimpleProofStepRule(TacticsLF.assumelfx.path) {
  def apply( step: Term ,  goal: ProofGoal, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case TacticsLF.assumelfx(OML(nm , None , None , _  , _ )) => {
        goal.tp match {
          case Arrow(df,g) =>{
            val freenm = helperFunctions.genFresh(nm , goal.stack.context ++ prover.solver.checkingUnit.context ++ prover.lambdaGoalsToContext )
            val pg = ProofGoal(goal.stack ++ OMV(freenm) % df, g, goal.history + "assumelfx")
            val newFVar = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context ++ prover.lambdaGoalsToContext)
            //  val newLam =  Lambda(freenm , df , OMV(newFVar))
            val newLam =  Lambda(pg.stack.context , ApplySpine( OMV(newFVar) , pg.stack.context.variables.map(x => x.toTerm) : _*))
            Some(List(pg) , newLam , List(OMV(newFVar)))
          }
        }
      }
      case _ => prover.solver.error("assume has not the right form")(goal.history) ; None
    }
  }
}



object FixlfxTactic extends SimpleProofStepRule(TacticsLF.fixlfx.path) {
  def apply(step: Term , goal: ProofGoal ,  prover: ImperativeProver) = step match {
    case TacticsLF.fixlfx(OML(n, None, None, _, _)) => {
      goal.tp match {
        case Pi(nm , tp, body) => {
          val stackN = goal.stack ++ OMV(n) % tp
          // val bodyN = prover.solver.simplify(Apply(body, OMV(n)))(stackN, goal.history)
          val bodyN = body.substitute(Substitution(Sub(nm , OMV(n))))(SmartSubstitutionApplier)
          val pg = ProofGoal(stackN, bodyN, goal.history + "fixlfx")
          // lambda


          val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
          val newG = helperFunctions.genHoleName(ctx)
          val lam = Lambda(pg.stack.context ,  ApplySpine( OMV(newG) , pg.stack.context.variables.map(x => x.toTerm) : _*))

          //lambda

          Some(List(pg) , lam , List(OMV(newG)))
        }
      }
    }
    case _ => prover.solver.error("fixlfx has not the right form: " + step.toString())(goal.history); None
  }
}

object theoremLFTactic extends InferenceAndTypingRule(TacticsLF.theoremLF.path, OfType.path) {
  def apply(solver: Solver, tm: Term , tpD : Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term] , Option[Boolean])= {
    val TacticsLF.theoremLF(typN, prf) = tm
    val  PropositionsITP.proof(steps) = prf
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val interp = new InteractiveLFProver(solver , rules , ProofGoal(Stack(Context()) , typN, history + "starting lf prover"))
    interp.executeInteractiveProof(steps)
    tpD match {
      case None =>
      case Some(tptp) => {
        val tmp = solver.check(Typing(stack, interp.prover.lambdaProofTerm, tptp))
        tmp
      }
    }
    val tmp = solver.presentObj(interp.prover.lambdaProofTerm)
    solver.check(Typing(stack, interp.prover.lambdaProofTerm, typN)) match {
      case true => (Some(typN) , Some(true))
      case false  => (None , None)
    }

  }
}


object LethTactic extends SimpleProofStepRule(TacticsLF.leth.path){
  def apply(step : Term, goal : ProofGoal ,   prover : ImperativeProver ): Option[(List[ProofGoal], Term , List[OMV])] = {
    val TacticsLF.leth(trm, nn) = step
    if (goal.stack.context.variables.exists(p => p.name == nn.name)) {return None }
    val trm0 = prover.clean(goal.stack  , trm)
    val tp = prover.solver.inferType(trm0 , false)(goal.stack , goal.history)
    val gls = (ProofGoal(goal.stack ++ OMV(nn.name) % tp.get  , goal.tp , goal.history + ("leth: added hypothesis :" + prover.solver.presentObj(OMV(nn.name) % tp.get))))
    //lambdaterm

    val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
    val newG = helperFunctions.genHoleName(ctx)
    val lam = Lambda(gls.stack.context  , ApplySpine( OMV(newG) , gls.stack.context.variables.map(x => x.toTerm) : _*))

    //lambdaterm
    Some((List(gls), lam , List(OMV(newG)) ))
  }
}



object BuildTactic extends SimpleProofStepRule(TacticsLF.build.path) {
  def apply( step: Term ,  goal: ProofGoal, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case TacticsLF.build(t) => {
        val tp = prover.solver.inferType(t , false)(goal.stack , goal.history).getOrElse(return None)
        prover.solver.check(Equality(goal.stack, goal.tp , tp , None))(goal.history) match {
          case false => None
          case true => Some(List() , t , List())
        }
      }
      case _ => prover.solver.error("build has not the right form " + step.toString)(goal.history) ; None
    }
  }
}

