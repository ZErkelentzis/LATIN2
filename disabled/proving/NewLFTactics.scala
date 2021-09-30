package latin2.proving

import info.kwarc.mmt.api.LocalName
import info.kwarc.mmt.api.checking.{History, InferenceAndTypingRule, Solver}
import info.kwarc.mmt.api.objects.{Context, Equality, Free, OML, OMV, SmartSubstitutionApplier, Stack, Sub, Substitution, Term, Typing, VarDecl}
import info.kwarc.mmt.lf.{Apply, ApplySpine, Arrow, Lambda, OfType, Pi}
import lf.{Implication, Proofs, PropositionsITP, TacticsLF, TypedTerms, TypedUniversalQuantification, TypedUniversalQuantificationND, Types}

import scala.collection.mutable.ListBuffer



object AssumelfTactic extends SimpleProofStepRule(TacticsLF.assume.path) {
  def apply( step: Term ,  goal: ProofGoal ,lgl : OMV , ltm : Term, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case TacticsLF.assume(OML(nm , None , None , _  , _ )) => {
        goal.tp match {
          case Arrow(df,g) =>{
            val freenm = helperFunctions.genFresh(nm , goal.stack.context ++ prover.solver.checkingUnit.context ++ prover.lambdaGoalsToContext)
            val pg = ProofGoal(goal.stack ++ OMV(freenm) % df, g, goal.history + "assumelfx")
            val newFVar = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context ++ prover.lambdaGoalsToContext , prover)
            //  val newLam =  Lambda(freenm , df , OMV(newFVar))
        //    val newLam =  Lambda(pg.stack.context , ApplySpine( OMV(newFVar) , pg.stack.context.variables.map(x => x.toTerm) : _*))

       //     prover.solver.substituteSolution(newLam)
      //      prover.solver.simplify(newLam)(pg.stack, pg.history)
            val newLam = Lambda(freenm , df , prover.solver.Unknown(newFVar  , pg.stack.context.variables.map(x => x.toTerm).toList))
//new
       //     prover.solver.substituteSolution(newLam)
        //    prover.solver.simplify(newLam)(pg.stack ++ Context(OMV(newFVar) % pg.tp) , pg.history)
      ////      prover.solver.substituteSolution(newLam)
            // prover.solver.solveTyping(Typing(pg.stack  , OMV(nm) , df ))(goal.history)
            val lgl = prover.lambdaGoals.head
            val ltm = prover.lambdaProofTerm
            val sb = Sub(lgl.name , Free(goal.stack.context , newLam))
            val tmp = new prover.solver.SubstituteUnknowns(sb)
            //   prover.solver.solve(prover.lambdaGoals.head.name , TacticsLF.stub)(goal.history)
            prover.solver.addUnknowns(Context(VarDecl(newFVar)) , None)
       //     prover.solver.check(Typing(goal.stack , newLam,  goal.tp , None))(goal.history)
 //           prover.solver.check(Equality(goal.stack ,  lgl , newLam, None))(goal.history)
            val newLam0 = tmp.traverse(ltm)(pg.stack.context, ())
            prover.solver.solve(lgl.name , Free(goal.stack.context, newLam) )(goal.history)
     //       prover.solver.check(Equality(goal.stack ,  lgl , newLam, None))(goal.history)
//new
            Some(List(pg) , newLam0 , List(OMV(newFVar)))
          }
        }
      }
      case _ => prover.solver.error("assume has not the right form")(goal.history) ; None
    }
  }
}



object FixlfTactic extends SimpleProofStepRule(TacticsLF.fix.path) {
  def apply(step: Term , goal: ProofGoal ,lgl : OMV, ltm : Term ,  prover: ImperativeProver) = step match {
    case TacticsLF.fix(OML(n, None, None, _, _)) => {
      goal.tp match {
        case Pi(nm , tp, body) => {
          val stackN = goal.stack ++ OMV(n) % tp
          // val bodyN = prover.solver.simplify(Apply(body, OMV(n)))(stackN, goal.history)
          val bodyN = body.substitute(Substitution(Sub(nm , OMV(n))))(SmartSubstitutionApplier)
          val pg = ProofGoal(stackN, bodyN, goal.history + "fixlfx")
          // lambda


          val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
          val newG = helperFunctions.genHoleName(ctx , prover)
    //      val lam = Lambda(pg.stack.context ,  ApplySpine( OMV(newG) , pg.stack.context.variables.map(x => x.toTerm) : _*))
    //      val lam =  ApplySpine( OMV(newG) , pg.stack.context.variables.map(x => x.toTerm) : _*)
          //lambda

          //check to solve omitted types

          prover.solver.check(Typing(pg.stack  , OMV(n) , tp ))(goal.history)

          //end check
          val lam = Lambda(n , tp  ,prover.solver.Unknown(newG  , pg.stack.context.variables.map(x => x.toTerm).toList))
    //      prover.solver.check(Typing(pg.stack  , lam , pg.tp ))(goal.history)

          val lgl = prover.lambdaGoals.head
          val ltm = prover.lambdaProofTerm
          val sb = Sub(lgl.name , Free(goal.stack.context,lam))
          val tmp = new prover.solver.SubstituteUnknowns(sb)
       //   prover.solver.solve(prover.lambdaGoals.head.name , TacticsLF.stub)(goal.history)
          prover.solver.addUnknowns(Context(VarDecl(newG)) , None)
         // prover.solver.check(Typing(goal.stack , lam , goal.tp , None))(goal.history)
     //     prover.solver.check(Equality(Stack(Context()) ,  lgl , lam, None))(goal.history)
          val newLam = tmp.traverse(ltm)(pg.stack.context, ())
          prover.solver.solve(lgl.name , TacticsLF.stub /*lam*/)(goal.history)
     //     val newLam = ltm
          Some(List(pg) , newLam , List(OMV(newG)))
        }
      }
    }
    case _ => prover.solver.error("fixlfx has not the right form: " + step.toString())(goal.history); None
  }
}

object theoremTactic extends InferenceAndTypingRule(TacticsLF.theorem.path, OfType.path) {

  def lfdefinitionCheckPreparer(ctx : Context ,  ls : List[Term], tp : Term): (List[VarDecl] , List[Term], Term) ={
    val tmp = ctx.toList
    def loop(ctxls: List[VarDecl]  , stps : List[Term] , tp : Term ): (List[VarDecl], List[Term] , Term) = (ctxls , stps, tp) match {
      case (List() , rest , _) => (List() , rest, tp)
      case (x::xs , TacticsLF.assume(h)::ys, Arrow(hd,tl) ) => {
        val name  = h.name
        val (vds , stps , tpnew) = loop(xs , ys, tl)
        val VarDecl(a,b,c,d,e) = x
        (VarDecl(name  , b, c, d, e) ::vds  , stps, tpnew)
      }
      case (x::xs , TacticsLF.fix(h)::ys , Pi(nm , tptp , body)) => {
        val name  = h.name
        val bodyN = body.substitute(Substitution(Sub(nm , OMV(h.name))))(SmartSubstitutionApplier)
        val (vds , stps , tpnew) = loop(xs , ys, bodyN)
        val VarDecl(a,b,c,d,e) = x
        (VarDecl(name  , b, c, d, e) ::vds  , stps, tpnew)
      }
    }
    loop(tmp, ls, tp)
  }

  def apply(solver: Solver, tm: Term , tpD : Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term] , Option[Boolean])= {
    val TacticsLF.theorem(typPre, prf) = tm
    prf match {
      case PropositionsITP.proof(_) =>
      case _ => solver.error("a proof has to start with the \"proof\" keyword. theoremLF (...) (PROOF ...)") ;  return (None , None)
    }
    val  PropositionsITP.proof(steps) = prf

    //hack to deal with LambdaHirarchy rule

    val (vds , stps, typN) = lfdefinitionCheckPreparer(stack.context , steps, typPre)

    //end of hack

    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val interp = new InteractiveLFProver(solver , rules , ProofGoal(Stack(Context(vds : _ * /* hack */)) , typN, history + "starting lf prover"))
    interp.executeInteractiveProof(stps /* hack */)
    tpD match {
      case None =>
      case Some(tptp) => {
        val tmp = solver.check(Typing(stack, interp.prover.lambdaProofTerm, tptp))
        tmp
      }
    }
    val tmp = solver.presentObj(interp.prover.lambdaProofTerm)
  //  solver.check(Typing(stack, interp.prover.lambdaProofTerm, typN)) match {
  //    case true => (Some(typN) , Some(true))
  //    case false  => (None , None)
  // }
    (Some(typN) , Some(true))
  }
}


object LetTactic extends SimpleProofStepRule(TacticsLF.let.path){
  def apply(step : Term, goal : ProofGoal , lgl : OMV , ltm : Term,  prover : ImperativeProver ): Option[(List[ProofGoal], Term , List[OMV])] = {
    val TacticsLF.let(trm, nn) = step
    if (goal.stack.context.variables.exists(p => p.name == nn.name)) {return None }
    val trm0 = prover.clean(goal.stack  , trm)
    val tp = prover.solver.inferType(trm0 , false)(goal.stack , goal.history)
    val gls = (ProofGoal(goal.stack ++ OMV(nn.name) % tp.get  , goal.tp , goal.history + ("leth: added hypothesis :" + prover.solver.presentObj(OMV(nn.name) % tp.get))))
    //lambdaterm

    val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
    val newG = helperFunctions.genHoleName(ctx , prover)
 //   val lam = Apply(Lambda(Context(OMV(nn.name) % tp.get) ++ goal.stack.context  , ApplySpine( OMV(newG) , gls.stack.context.variables.map(x => x.toTerm) : _*)) , trm0)
    val lam = Apply(Lambda(nn.name , tp.get , prover.solver.Unknown(newG  , gls.stack.context.variables.map(x => x.toTerm).toList) ), trm)
//new
    val lgl = prover.lambdaGoals.head
    val ltm = prover.lambdaProofTerm
    val sb = Sub(lgl.name , Free(goal.stack.context,lam))
    val tmp = new prover.solver.SubstituteUnknowns(sb)
    //   prover.solver.solve(prover.lambdaGoals.head.name , TacticsLF.stub)(goal.history)
    prover.solver.addUnknowns(Context(VarDecl(newG)) , None)
    // prover.solver.check(Typing(goal.stack , lam , goal.tp , None))(goal.history)
    //   prover.solver.check(Equality(Stack(Context()) ,  lgl , lam, None))(goal.history)
    val newLam = tmp.traverse(ltm)(gls.stack.context, ())
    prover.solver.solve(lgl.name , TacticsLF.stub /*lam*/)(goal.history)
    //new

    Some((List(gls), newLam , List(OMV(newG)) ))
  }
}



object BuildTactic extends SimpleProofStepRule(TacticsLF.build.path) {
  def apply( step: Term ,  goal: ProofGoal,lgl : OMV, lpt : Term, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case TacticsLF.build(t) => {
        val tp = prover.solver.inferType(t , false)(goal.stack , goal.history).getOrElse(return None)
        prover.solver.check(Equality(goal.stack, goal.tp , tp , None))(goal.history) match {
          case false => None
          case true =>{


            val sb = Sub(lgl.name , Free(goal.stack.context , t))
            val tmp = new prover.solver.SubstituteUnknowns(sb)
            val newLam = tmp.traverse(lpt)(goal.stack.context, ())
            prover.solver.solve(lgl.name , TacticsLF.stub )(goal.history)

            prover.solver.check(Equality(goal.stack , prover.lambdaGoals.head, t , None))(goal.history) ; Some(List() , newLam , List())
          }
        }
      }
      case _ => prover.solver.error("build has not the right form " + step.toString)(goal.history) ; None
    }
  }
}

object FwdlfTactic extends  SimpleProofStepRule(TacticsLF.fwd.path) {
  def apply(step: Term , goal: ProofGoal , lgl : OMV , ltm : Term , prover: ImperativeProver ): Option[(List[ProofGoal], Term , List[OMV])] = {
    val TacticsLF.fwd(OML(h, None, None, _, _), hs) = step
    val tmp = try {
      goal.stack.context(h)
    } catch {
      case e => return None
    }

    def loop(t: Term, ls: List[Term]): Option[Term] = (t, ls) match {
      case (thm, Nil) => Some(thm)
      case (Arrow(hd, tl), x :: xs) => {
        val xC = x match {case OML(n , None, None , None, None) => OMV(n)  ; case _ => x }
        val tp = prover.solver.inferType(xC, false)(goal.stack, goal.history).getOrElse(return None)
        prover.solver.check(Equality(goal.stack, tp, hd, Some(Types.tp.term)))(goal.history + "fwd implication") match {
          case true => {
            loop(tl, xs)
          }
          case false => None
        }
      }
      case (Pi(v, ptp ,bd), x :: xs) => {
        val xC = prover.clean(goal.stack, helperFunctions.removeDed( x))
        val tp = prover.solver.inferType(xC, false)(goal.stack, goal.history).getOrElse(return None)

        prover.solver.check(Equality(goal.stack, tp, ptp, None))(goal.history + "fwd forall") match {
          case true => {
            val bodyN =  bd.substitute(Substitution(Sub(v , xC)))(SmartSubstitutionApplier)  // prover.solver.simplify(Apply(bd, xC))(goal.stack, goal.history)
            loop(bodyN, xs)
          }
          case false => None
        }
      }
      case (trm, _) => Some(trm)
    }

    val tmp0 = loop(tmp.tp.getOrElse(return None), hs)
    tmp0 match {
      case None => None
      case Some(a) => {
        val tmp2 = goal.stack.context.variables.filter(p => p.name != h)
        val newCtx = Stack(Context(tmp2: _*)) ++ OMV(h) % a
        //       Some(List(ProofGoal(newCtx, goal.tp, goal.history + "fwd step done")))
        //      val newCtx = Stack(goal.stack.context ++ OMV(h) % a)

        //lambdaterm
        val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext

        val newPG = ProofGoal(newCtx, goal.tp, goal.history + "fwdlfx step done")

        val newG = helperFunctions.genHoleName(ctx  , prover)
        val newGG = prover.solver.Unknown(newG  , newPG.stack.context.variables.map(x => x.toTerm).toList)
        val lam = Apply(Lambda(h , a , newGG ) , ApplySpine(tmp.toTerm , hs : _ * ))
        //lambdaterm



        val sb = Sub(lgl.name , Free(goal.stack.context,lam))
        val tmpsb = new prover.solver.SubstituteUnknowns(sb)
        prover.solver.addUnknowns(Context(VarDecl(newG)) , None)
        val newLam = tmpsb.traverse(ltm)(newPG.stack.context, ())
        prover.solver.solve(lgl.name , TacticsLF.stub /*lam*/)(goal.history)


        Some((List(newPG) , newLam , List(OMV(newG)) ) )
      }
    }
  }
}


object BwdlfTactic extends SimpleProofStepRule(TacticsLF.bwd.path){


  def getHead(tm : Term) : (List[Term] , Term) = {
    def getHeadL(tm: Term): (List[Term], Term) = tm match {
      case Arrow(h, t) => {
        val (ls, hd) = getHeadL(t)
        (h :: ls, hd)
      }
      case _ => (Nil, tm)
    }
    getHeadL(tm)
  }
  def apply(step : Term , goal : ProofGoal , lgl : OMV , ltm : Term ,  prover : ImperativeProver ) = {
    step match {
      case TacticsLF.bwd(trm) => {
        val trmC = prover.clean(goal.stack , trm)
        val tmp = prover.solver.inferType(trmC, false)(goal.stack, goal.history)
        tmp match {
          case None => {
            prover.solver.error("the used term has no type")(goal.history)
            None
          }
          case Some(tptp) => {
            val (t, h) = getHead(tptp)
            val v = goal.tp
            //           val h0 = prover.clean(goal.stack , h)
            prover.solver.check(Equality(goal.stack, h, v, Some(Types.tp.term)))(goal.history + "the conclusion of the backward step has to be equal to the goal")
            val newGoals = t.map(x => ProofGoal(goal.stack, x, goal.history + ("applied bwd with " + prover.solver.presentObj(trm)) ))

            //lambda term

            val numHoles = newGoals.length

            val holes : ListBuffer[LocalName] = ListBuffer()
            val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
            for (i <- 0 until numHoles){
              val hname = helperFunctions.genHoleName(ctx ++ Context(holes.map(ln => VarDecl(ln)) : _*), prover)
              holes.append(hname)
            }
            //applygeneral maybe

            val holeTerms : ListBuffer[Term] = new ListBuffer

            for(i <- 0 until numHoles){
              val tmp = holes(i)
              holeTerms.append(prover.solver.Unknown(tmp , newGoals(i).stack.context.toList.map(x => x.toTerm) ))
            }


            val lterm = ApplySpine(trm , holeTerms :_*)
            val sb = Sub(lgl.name , Free(goal.stack.context , lterm))
            val tmp = new prover.solver.SubstituteUnknowns(sb)
            prover.solver.addUnknowns(Context(holes.map(x => VarDecl(x)) : _* ) , None)
            val newlterm = tmp.traverse(ltm)(goal.stack.context, ())

            //lambda term

            val tmpl = holes.map(x => OMV(x))
        //    prover.solver.check(Equality(goal.stack ,  Free(goal.stack.context, lgl) , Free(goal.stack.context, lterm), None))(goal.history)
            prover.solver.solve(lgl.name , Free(goal.stack.context , lterm) )(goal.history)
            Some((newGoals , newlterm , tmpl.toList))
          }
        }
      }
    }
  }
}



object UselfTactic extends SimpleProofStepRule(TacticsLF.use.path) {
  def apply(step: Term , goal : ProofGoal , lgl : OMV , lpt : Term , prover: ImperativeProver) = {
    val TacticsLF.use(p) = step
    val pC =  p match {case OML(nm , None, None, None, None) => OMV(nm) ; case v => v}  // prover.clean(goal.stack, p)
    val lam =  pC
    prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term") match {
      case true =>  {
        // prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term2")
        val sb = Sub(lgl.name , Free(goal.stack.context , lam))
        val tmp = new prover.solver.SubstituteUnknowns(sb)
        val newLam = tmp.traverse(lpt)(goal.stack.context, ())
   //     prover.solver.check(Equality(goal.stack ,  lgl , lam, None))(goal.history)
        prover.solver.solve(lgl.name, Free(goal.stack.context , lam) )(goal.history + "solving final goal")
        Some((List() ,  newLam , List()))
      }
      case false => prover.solver.error("use needs a term that has exactly the type of the goal")(goal.history); None
    }
  }
}
/*
object SubproofTactic extends ComplexProofStepRule(NewTactics.subproof.path) {
  def apply(step: Term , prover: ImperativeProver ) : Unit =  {
    val NewTactics.subproof(stps) = step
    prover.toDoSteps =  stps ++ prover.toDoSteps
    prover.stepHistory = step :: prover.stepHistory
  }

  //maybe introduce metainf
  def undoStep(t: Term, ip:  ImperativeProver): Unit = {
    val NewTactics.subproof(stps) = t
    ip.toDoSteps  = t :: ip.toDoSteps.drop(stps.length)
    ip.stepHistory = ip.stepHistory.tail

  }
}



object SubgoalTactic extends SimpleProofStepRule(NewTactics.subgoal.path) {
  def apply(step : Term , goal : ProofGoal , prover : ImperativeProver ) : Option[(List[ProofGoal], Term , List[OMV])] = {
    val NewTactics.subgoal(OML(h, None , None , _ , _) , trm) = step
    val newg = ProofGoal(goal.stack ++  OMV(h) % trm , goal.tp , goal.history + ("added hypothesis " + h.toString + ": " + prover.solver.presentObj(trm)))
    val subg = ProofGoal(goal.stack , trm , goal.history + ("added new subgoal " + prover.solver.presentObj(trm)))
    val newFVar = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext , prover )
    val newFVar2 = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext ++ VarDecl(newFVar)  , prover )
    val lt : Term = Apply (Lambda( h, trm , OMV(newFVar) )   , OMV(newFVar2) )
    Some(List(subg , newg) , lt , List(OMV(newFVar), OMV(newFVar2)))
  }
}

 */
/*
object Proofmerule extends InferenceAndTypingRule(TacticsLF.proofme.path) {
  def apply(solver: Solver, tm: Term , tpD : Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term] , Option[Boolean])= {
    val tacticsLF.proofme(loctp) = tm
  }
}

 */

/*
// repeat from coq
object redo extends SimpleProofStepRule(NewTactics.bwd.path){
  def apply(step : Term , goal : ProofGoal ,  prover : ImperativeProver ) = {
    case
  }
}
// apply tactic to several subgoals

 */
/*
object applyto {

}

object rw {

}

object contradiction {

}


// tactical ";" aus coq
object chain {
}

object autostep {

}

object autosteps {

}

object solver {

}

object refl {

}

object oracle {

}

object field {

}

object ring {

}

object linear {

}

object nonlinear {

}

object autotool {

}

object genericPresburger {

}

object counterexampleGenerator {

}

object tableaux {

}
*/