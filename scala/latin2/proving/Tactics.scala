package latin2.proving

import latin2.proving._
import lf.{Implication, Negation, Proofs, PropositionsITP, Tactics, TypedEquality, TypedUniversalQuantification, Types}
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.checking.{History, InferenceAndTypingRule, InferenceRule, Solver, TypingRule}
import info.kwarc.mmt.api.symbols.FinalConstant
import info.kwarc.mmt.api.uom.ConstantScala
import info.kwarc.mmt.lf.{Apply, Arrow, OfType, Pi, Typed}

// import latin2.proving.helperFunctions.{NamedHypothesis, NamedOrUnnamedTerm, UnnamedHypothesis}
import lf.Tactics.{cntra, theoremLF}
import objects._
import prettyprint._
import objects.OMV

/*
object VoidTactic extends ProofStepRule(Tactics.void.path){
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term) = {
    step match {
      case Tactics.void(ls) => {
        Some(List(goal))
      }
    }
  }
}

/*
object PrintProofStateTactic extends  ProofStepRule(Tactics.pps.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    prover.solver.report("proofstate" , ">>>>>>>>>>>> PROVING: " + prover.solver.checkingUnit.component.toString + " <<<<<<<<<<<<<")
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  prettyPrintHyps(prover.solver ,goal.stack))
    prover.solver.report("proofstate" , "GOAL---------------GOAL---------------GOAL")
    prover.solver.report("proofstate" ,  prover.solver.presentObj(goal.tp))
    prover.solver.report("proofstate" , "-----------END----------")
    Some(Nil)
  }
}
*/
object PrintProofStateRawTactic extends  ProofStepRule(Tactics.ppsr.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    prover.solver.report("proofstate" , ">>>>>>>>>>>> PROVING: " + prover.solver.checkingUnit.component.toString + " <<<<<<<<<<<<<")
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  printHypsRaw(goal.stack))
    prover.solver.report("proofstate" , "GOAL---------------GOAL---------------GOAL")
    prover.solver.report("proofstate" ,  goal.tp.toString)
    prover.solver.report("proofstate" , "-----------END----------")
    Some(List(goal))
  }
}


/*
object PrintProofStateVoidTactic extends  ProofStepRule(Tactics.ppsv.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    prover.solver.report("proofstate" , ">>>>>>>>>>>> PROVING: " + prover.solver.checkingUnit.component.toString + " <<<<<<<<<<<<<")
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  prettyPrintHyps(prover.solver ,goal.stack))
    prover.solver.report("proofstate" , "GOAL---------------GOAL---------------GOAL")
    prover.solver.report("proofstate" ,  prover.solver.presentObj(goal.tp))
    prover.solver.report("proofstate" , "-----------END----------")
    Some(List(goal))
  }
}
*/


object PrintProofStateTactic extends  ProofStepRule(Tactics.pps.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    prover.solver.report("proofstate" , ">>>>>>>>>>>> PROVING: " + prover.solver.checkingUnit.component.toString + " <<<<<<<<<<<<<")
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  prettyPrintHyps(prover.solver ,goal.stack))
    prover.solver.report("proofstate" , "GOAL---------------GOAL---------------GOAL")
    prover.solver.report("proofstate" ,  prover.solver.presentObj(goal.tp))
    prover.solver.report("proofstate" , "-----------END----------")
    Some(List(goal))
  }
}



// do a BackWarD step (i.e. apply an implication to a goal)

object BwdTactic extends ProofStepRule(Tactics.bwd.path){


  def getHead(tm : Term) : (List[Term] , Term) = {
    def getHeadL(tm: Term): (List[Term], Term) = tm match {
      case Implication.impl(h, t) => {
        val (ls, hd) = getHeadL(t)
        (h :: ls, hd)
      }
      case _ => (Nil, tm)
    }

    tm match {
      case Proofs.ded(v) => getHeadL(v)
    }

  }
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term) = {
    step match {
  /*    case Tactics.bwd(OMID(pt)) => {
        val pat = pt.toMPath
        val pat0 = pat.toGlobalName
        val tmp = try {
          prover.solver.inferType(OMS(pat0), true)(goal.stack, goal.history)
        } catch {
          case e => None
        }
        tmp match {
          case None => {
            prover.solver.error("the used term has no type")(goal.history)
            None
          }
          case Some(tptp) => {
            val (t, h) = getHead(tptp)
            val Proofs.ded(v) = goal.tp
            prover.solver.check(Equality(goal.stack, h, v, Some(Types.tp.term)))(goal.history + "the conclusion of the backward step has to be equal to the goal")
            val newGoals = t.map(x => ProofGoal(goal.stack, Proofs.ded(x), goal.history))
            Some(newGoals)
          }
        }
      } */
      case Tactics.bwd(trm) => {
        val trmC = prover.clean(goal.stack , trm)
        val tmp = prover.solver.inferType(trmC, false)(goal.stack, goal.history)
        tmp match {
          case None => {
            prover.solver.error("the used term has no type")(goal.history)
            None
          }
          case Some(tptp) => {
            val (t, h) = getHead(tptp)
            val Proofs.ded(v) = goal.tp
 //           val h0 = prover.clean(goal.stack , h)
            prover.solver.check(Equality(goal.stack, h, v, Some(Types.tp.term)))(goal.history + "the conclusion of the backward step has to be equal to the goal")
            val newGoals = t.map(x => ProofGoal(goal.stack, Proofs.ded(x), goal.history + ("applied bwd with " + prover.solver.presentObj(trm)) ))
            Some(newGoals)
          }
        }
      }
    }
  }
}

object IgnoreTactic extends  ProofStepRule(Tactics.ignore.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    Some(Nil)
  }
}


object IgnoreAllTactic extends  ProofStepRule(Tactics.ignoreall.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    prover.setGoals(List(goal))
    Some(Nil)
  }
}

/*
object BuildTactic extends  ProofStepRule(Tactics.build.path){



  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    val Tactics.build(trm) = step
    val trmC = prover.clean(goal.stack  ,trm)

  }
}
*/
object HoleIaT extends  InferenceAndTypingRule(Tactics.lambdahole.path , OfType.path) {
  def apply(solver: Solver, tm: Term, tpO: Option[Term], covered : Boolean)(implicit stack: Stack, history: History):  (Option[Term] , Option[Boolean]) = {
    solver.report("holestate", "hole has type "  + tpO.toString)
    (tpO , Some(true ))
  }


}


object FwdTactic extends  ProofStepRule(Tactics.fwd.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    val Tactics.fwd(OML(h, None, None, _, _), hs) = step
    val tmp = try {
      goal.stack.context(h)
    } catch {
      case e => return None
    }

    def loop(t: Term, ls: List[Term]): Option[Term] = (t, ls) match {
      case (Proofs.ded(thm), Nil) => Some(Proofs.ded(thm))
      case (Proofs.ded(thm), ls) => loop(thm, ls)
      case (Implication.impl(hd, tl), x :: xs) => {
        val xC = prover.clean(goal.stack, helperFunctions.removeDed( x))
        val tp = helperFunctions.removeDed(prover.solver.inferType(xC, false)(goal.stack, goal.history).getOrElse(return None))
        prover.solver.check(Equality(goal.stack, tp, hd, Some(Types.tp.term)))(goal.history + "fwd implication") match {
          case true => {
            loop(tl, xs)
          }
          case false => None
        }
      }
      case (TypedUniversalQuantification.forall(v, bd), x :: xs) => {
        val xC = prover.clean(goal.stack, helperFunctions.removeDed( x))
        // currently the following line is not useful since TypedUniversalQunatification.forall can't take a a prop/type as quantified variable
        val tp = helperFunctions.removeDed(prover.solver.inferType(xC, false)(goal.stack, goal.history).getOrElse(return None))
        // forall doesn't take a tm T (where T can be replaced by any other type f.ex. tm X) but just a T
        val vtm = lf.TypedTerms.tm(v)
        prover.solver.check(Equality(goal.stack, tp, vtm, Some(Types.tp.term)))(goal.history + "fwd forall") match {
          case true => {
        //    val stackN = goal.stack ++ Context(xC)
            val bodyN = prover.solver.simplify(Apply(bd, xC))(goal.stack, goal.history)
            loop(bodyN, xs)
          }
          case false => None
        }
      }
      case (trm, _) => Some(Proofs.ded(trm))
    }

    val tmp0 = loop(tmp.tp.getOrElse(return None), hs)
    tmp0 match {
      case None => None
      case Some(a) => {
        val tmp2 = goal.stack.context.variables.filter(p => p.name != h)
        val newCtx = Stack(Context(tmp2: _*)) ++ OMV(h) % a
 //       Some(List(ProofGoal(newCtx, goal.tp, goal.history + "fwd step done")))
  //      val newCtx = Stack(goal.stack.context ++ OMV(h) % a)
        Some(List(ProofGoal(newCtx, goal.tp, goal.history + "fwd step done")))
      }
    }
  }
}

/*
object FwdTactic extends  ProofStepRule(Tactics.fwd.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    val Tactics.fwd(OML(h , None , None , _ , _) , hs) = step
    val tmp = try {goal.stack.context(h)} catch {case e  => return None}

    def loop(t : Term , ls : List[Term]) : Option[Term] = (t,ls) match{
      case (Proofs.ded(thm), Nil) => Some(Proofs.ded(thm))
      case (Proofs.ded(thm) , ls) => loop(thm , ls)
      case (Implication.impl(hd,t) , x::xs ) => {
        val tp = prover.solver.inferType(x , false)(goal.stack , goal.history).getOrElse(return None)
        val tC = prover.clean(goal.stack, tp)
        prover.solver.check(Equality(goal.stack, tC, hd, Some(Types.tp.term)))(goal.history + "fwd implication") match {
          case true => {
            loop(t , xs)
          }
          case false => None
        }
      }
      case (TypedUniversalQuantification.forall(typ, bd) , x::xs) => {
        val tpp = TypedTerms.tm(typ)
        val tC = prover.clean(goal.stack, x)
        val tp = prover.solver.inferType(tC , false)(goal.stack , goal.history).getOrElse(return None)
        prover.solver.check(Equality(goal.stack, tp , tpp , Some(Types.tp.term)))(goal.history + "fwd forall") match {
          case true => {
            val bdn = prover.solver.simplify(Apply(bd, x))(goal.stack, goal.history)
            loop(bdn , xs)
          }
          case false => None
        }
      }
      case (trm , _) => Some(Proofs.ded(trm))
    }

    val tmp0 = loop(tmp .tp.getOrElse(return None), hs)
    tmp0 match {
      case None => None
      case Some(a) => {
        val tmp2 = goal.stack.context.variables.filter(p => p.name != h)
        val newCtx = Stack(Context(tmp2 :_*))    ++ OMV(h) % a
        Some(List(ProofGoal(newCtx , goal.tp , goal.history + "fwd step done")))
      }
    }
  }

*/

/*    val hyps = helperFunctions.getHyps(tmp.tp.getOrElse(return None))
    val tmp0 = hyps.map { case NamedHypothesis(ln, t) => t; case UnnamedHypothesis(t) => t }






    def loop(xs : List[Term] , ys : List[Term]) : Option[List[Term]] = (xs , ys) match{
      case (Nil , _) => Some(Nil)
      case (l :: ls , v :: vs ) => if (l == prover.solver.inferType(v , false)(goal.stack, goal.history).getOrElse(return None) ) {loop(ls , vs)} else {return None}
      case (ls , Nil) => Some(ls)
    }

  //  val tmp0 = helperFunctions.getNamedTerms(hs)
  //  val tmp1 =
    val conc = helperFunctions.getConclusion(tmp.tp.get)
    val tmp1 = loop(tmp0 , hs)
    tmp1 match {
      case None => None
      case Some(a) => {
        val tmp2 = goal.stack.context.variables.filter(p => p.name != h)
        val newCxt = Stack(Context(tmp2 :_*))    ++ OMV(h) % conc
        ProofGoal()
      }
    }
  }
}
*/
object printType {

}

object printDefinition {

}

object printLocation {

}

object RemoveHypsTactic extends ProofStepRule(Tactics.rmh.path) {
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term) = {
    step match {
      case Tactics.rmh(xs) => {
        val xsC = xs.map(x => x.name)
        val newCtx = goal.stack.context.variables.filter(p => {
          !xsC.contains(p.name)
        })
        Some(List(ProofGoal(Stack(Context(newCtx: _*)), goal.tp, goal.history + ("removed hyps " + xsC.toString()))))
      }
    }
  }
}


object SubgoalTactic extends ProofStepRule(Tactics.subgoal.path) {
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term) = {
    val Tactics.subgoal(OML(h, None , None , _ , _) , trm) = step
    val trmC = prover.clean(goal.stack ,  trm )
    val newg = ProofGoal(goal.stack ++  OMV(h) % trmC , goal.tp , goal.history + ("added hypothesis " + h.toString + ": " + prover.solver.presentObj(trm)))
    val subg = ProofGoal(goal.stack , trmC , goal.history + ("added new subgoal " + prover.solver.presentObj(trm)))
    Some(List( subg  ,  newg))
  }
}

//print the proof state (all branches)
object ppsa {

}

// add hypothesiss to proof context
object AddhTactic extends ProofStepRule(Tactics.addh.path){
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term): Option[List[ProofGoal]] = {
    val Tactics.addh(trm, nn) = step
    if (goal.stack.context.variables.exists(p => p.name == nn.name)) {return None }
    val trm0 = prover.clean(goal.stack  , trm)
    val tp = prover.solver.inferType(trm0 , false)(goal.stack , goal.history)
    Some(List(ProofGoal(goal.stack ++ OMV(nn.name) % tp.get  , goal.tp , goal.history + ("addh: added hypothesis :" + prover.solver.presentObj(OMV(nn.name) % tp.get)))))
  }
}

object ContradictionTactic extends ProofStepRule(Tactics.cntra.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {

    step match {
      case cntra(List(h, nh)) => {
        val hc = prover.clean(goal.stack ,  h)
        val nhc = prover.clean(goal.stack , nh)
        val v = prover.solver.inferType(hc, false)(goal.stack, goal.history)
        val nv = prover.solver.inferType(nhc, false)(goal.stack, goal.history)
        (v, nv) match {
          case (Some(Proofs.ded(thm)), Some(Proofs.ded(Negation.not(nthm)))) => {
            if (prover.solver.check(Equality(goal.stack, thm, nthm, None))(goal.history)){return Some(Nil)}else {return None}
          }
          case _ => {
            return None
          }
        }
        None
      }
      case cntra(List(h)) => {
        val hc = prover.clean(goal.stack , h)
        val v = prover.solver.inferType(hc, false)(goal.stack, goal.history)
        v match {
          case Some(Proofs.ded(t)) =>{
            t match {
              case (lf.Falsity._false(v)) => {
                Some(Nil)
              }
              case _ => {
                None
              }
            }
          }
        }
      }
      case _ => None
    }
  }
}



object SwitchGoalTactic extends ProofStepRule(Tactics.switchgoal.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    val Tactics.switchgoal(OML(ln , _ , _ , _ , _)) = step
    val n = ln.toString.toInt
    val gls = prover.getGoals
    (gls.length < n || n <= 0) match {
      case true => None
      case false => {
        val gl = gls(n - 1)
        val gls0 = gl :: gls.take(n - 1) ++ gls.drop(n)
        prover.setGoals(gls0)
        Some(List(gl))
      }
    }
  }
}

object next {

}




/** starts an [[ImperativeProver]] when checking a term of the form proof(steps) */
object CheckProofLF extends TypingRule(Tactics.proofLF.path) {
  def apply(solver: Solver) (tm: Term, tp0 : Term )(implicit stack: Stack, history: History): ( Option[Boolean]) = {
    val Tactics.proofLF(tp , steps) = tm
    var goal = ProofGoal(stack, tp, history + "starting proverLF")
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val prover = new ImperativeProver(solver, rules, goal)
    //   Solver.breakAfter(350)
    steps.foreach {step =>
      // history += step.head.name
      val r = prover.makeStep(step)
      if (!r) {
        solver.error("proof step application failed (LF): " + solver.presentObj(step))(prover.currentHistory)
        return ( Some(false))
      }
    }
    if (prover.isSolved)
    {
      solver.report("proofstate" , "proof succeeded: " + solver.checkingUnit.component.toString ) ; ( Some(true))
    } else
    {
      solver.report("proofstate" , "proof failed: " +  solver.checkingUnit.component.toString)  ; (None)
    }
  }
}



object theoremLFTactic extends InferenceAndTypingRule(Tactics.theoremLF.path, OfType.path) {
  def apply(solver: Solver, tm: Term , tpD : Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term] , Option[Boolean])= {
    val Tactics.theoremLF(typN , prf) = tm
    val typ = solver.inferType(typN , true).getOrElse(return (None , None))
  //  solver.substituteSolution( )
    val tmp = prf match {
      case PropositionsITP.proof(args) => {
        Tactics.proofLF(typ , args)
      }
    }
    CheckProofLF(solver)(tmp, typ) match {
      case Some(true)  => (Some(typ), Some(true))
      case Some(false) | None => (None , Some(false))
    }
  }
}


object FixLFTactic extends ProofStepRule(Tactics.fixLF.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.fixLF(OML(n,tO,_,_,_)) = step
    goal.tp match {
      case Pi(nm , typ , bd) =>
        val stackN = goal.stack ++ OMV(n) %  typ
        val bodyN = prover.solver.simplify(Apply(bd, OMV(n)))(stackN, goal.history)
        tO.foreach {t =>
          val tC = prover.clean(goal.stack, t)
          prover.solver.check(Equality(goal.stack, tC, typ, Some(Types.tp.term)))(goal.history + "fixLF must equal quantification domain")
        }
        val pg = ProofGoal(stackN, bodyN, goal.history + "fixLF")
        Some(List(pg))
      case tp =>
        prover.solver.error("(fixLF) only applicable to pi quantified goal: found " + prover.solver.presentObj(tp))(goal.history)
        None
    }
  }
}

object AssumeLFXTactic extends ProofStepRule(Tactics.assumeLFX.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.assumeLFX(OML(n,tO,_,_,_)) = step

    goal.tp match {
      case Arrow(hd,tl) =>
        tO.foreach {t =>
          val tC = prover.clean(goal.stack, t)
          prover.solver.check(Equality(goal.stack, tC, hd , Some(OMS(Typed.ktype))))(goal.history + "assumption (lfx) must equal implicant")
        }
        val pg = ProofGoal(goal.stack ++ OMV(n) % hd, tl , goal.history + "assumeLFX")
        Some(List(pg))
      case tp =>
        prover.solver.error("(lfx) only applicable to implication goal, found " + prover.solver.presentObj(tp))(goal.history)
        None
    }
  }
}




// unfold definition
object ExpandTactic extends ProofStepRule(Tactics.exp.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.exp(OMID(p)) = step
    val dfn = prover.solver.controller.get(p).asInstanceOf[FinalConstant].df
    dfn match {
      case None => None
      case Some(dff) => {
        val tmpg = helperFunctions.simpleSubstitution(p.name , goal.tp , dff)
        Some(List(ProofGoal(goal.stack , tmpg , goal.history)))
      }
    }
  }
}





// existential quantifier destruction
/*
object exe extends ProofStepRule(Tactics.exe.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.exe(h) = step
    val hc = prover.clean(goal.stack  , h )

  }
}
*/
// existential quantifier intro
object exi {

}


object generalize {

}


// apply several tactics to multiple subgoals
object ApptoTactic extends ProofStepRule(Tactics.appto.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.appto(Tactics.argl(ls), Tactics.arg(l0)) = step
    val targets = ls.map {  x => helperFunctions.termToInt(x).get }
    val gls = prover.getGoals
    prover.clearGoals
    val tmp = gls.zip(Stream.from(1))
    val cgoals = tmp.filter(p => targets.contains(p._2)).map(_._1)
    val ncgoals = tmp.filter(p => ! targets.contains(p._2)).map(_._1)
    val newgoals = cgoals.map(gg => helperFunctions.applyTacticsToGoal(prover , gg , l0))
    val tmpgs = newgoals.foldLeft[Option[List[ProofGoal]]](Some(Nil))((res, curr) => (res , curr)  match {
      case (None , _) => None
      case (_ , None) => None
      case (Some(ls) , Some(ls0) ) => Some(ls ++ ls0)
    })
    tmpgs match{
      case None => None
      case Some(ls) => {
        prover.setGoals(ls ++ ncgoals)
        Some(List())
      }
    }
  }
}


object PrintAllProofGoalsTactic extends ProofStepRule(Tactics.papg.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val gls = prover.getGoals
    prover.solver.report("proofstate" , ">>>>>>>>>>>> PROVING: " + prover.solver.checkingUnit.component.toString + " <<<<<<<<<<<<<")
    gls.foldLeft(1)((i , g) =>  {
      prover.solver.report("proofstate" , "Goal " + i.toString + " :" + prover.solver.presentObj(g.tp))
  //    prover.solver.report("proofstate" ,  prover.solver.presentObj(g.tp))
      i + 1
    })
    prover.solver.report("proofstate" , "-----------END----------")
    Some(List(goal))
  }
}

object RewriteTactic extends ProofStepRule(Tactics.rw.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) : Option[List[ProofGoal]] = {
    val Tactics.rw(e) = step
    val tmpeq =  e match {
      case OML(n, _, _, _, _)  =>{
        goal.stack.context(n).tp.getOrElse(return None)
      }
      case OMID(n) => {
        prover.solver.inferType(OMID(n) , true)(goal.stack , goal.history)
      }
      case _ => return None
    }
    tmpeq match {
      case Proofs.ded(TypedEquality.equal(tp , a, b )) => {
        val newG = helperFunctions.simpleSubstituteRw(goal.tp , a , b)
        Some(List(ProofGoal(goal.stack , newG , goal.history + "rw")))
      }
      case _ => None
    }
  }
}
/*
object InductTactic extends ProofStepRule(Tactics.induct.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) : Option[List[ProofGoal]] = step match  {
    case Tactics.induct(h , v) => {

      def dings(t : Term) : List[OMV] = t match {
        case OMA(OMV(n) , ags) => n.toString match {
          case "p" => List(OMV(n))
          case _ => Nil
        }

      }

      helperFunctions.unify(h , v , dings)
      Some(Nil)
    }
  }
}

*/
object cases {

}

// doesnt work with refl as name because there is another rule that has this name ... but this shouldnt actually matter because the other rule is not a tactic
object RefltTactic extends ProofStepRule(Tactics.reflt.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) : Option[List[ProofGoal]] = helperFunctions.getConclusion(goal.tp) match {
    case TypedEquality.equal(_ , a , b) =>{
      prover.solver.check(Equality(goal.stack , a , b, None ))(goal.history) match  {
        case true => Some (Nil)
        case false => None
      }
    }
    case _ => None
  }
}


//view between different tactics

// splits conjunction in goal
object split {

}

// for or statement
object left {

}


// for or statement
object right {

}

// possibly the same as cases
object destruct {

}

/*
object proofaltTactic extends ProofStepRule(Tactics.proofalt.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) : Option[List[ProofGoal]] = helperFunctions.getConclusion(goal.tp) match {
    case Tactics.proofalt(stps) = step
  }
}
*/


object apRule {

}


// {P} (P 0) -> (P n -> P (n +1)) -> P n

//mmt-api algebra
//lf simplificationrulegenerator  , proving

/*
Key proof steps:

backwards steps
special case induction
relevant existing code: BackwardsPiElimination
equality steps
special case algebraic simplification
relevant existing code: SimplificationRuleGenerator, uom.Algebra

 */
//  |a -> b   bulid ([a] _)

object interactive {

}


object SubproofTactic extends ProofStepRule(Tactics.subproof.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) : Option[List[ProofGoal]] =  {
    val Tactics.subproof(stps) = step
    prover.executeSteps(stps) match {
      case true => Some(prover.getGoals)
      case false => None
    }
  }
}


object repeat {

}

 */