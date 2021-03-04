package latin2.proving

import java.awt.{BorderLayout, Color}
import java.awt.event.{ActionEvent, ActionListener, WindowEvent, WindowListener}
import java.util.Calendar

import info.kwarc.mmt.api.{ErrorThrower, GlobalName}
import info.kwarc.mmt.api.checking.{CheckingUnit, History, InferenceAndTypingRule, SingleTermBasedCheckingRule, Solver, SolverError, TypingRule}
import info.kwarc.mmt.api.documents.InterpretationInstructionContext
import info.kwarc.mmt.api.objects.{Context, Stack, Term}
import info.kwarc.mmt.api.parser.{NotationBasedParser, ParseResult, ParsingUnit, SourceRef}
import info.kwarc.mmt.lf.OfType
import lf.{PropositionsITP, TacticsLF}
import javax.swing._
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter

import scala.collection.mutable.ListBuffer

object InteractiveProof extends InferenceAndTypingRule(TacticsLF.iproof.path ,OfType.path) {
  def apply(solver: Solver, tm: Term, tpO: Option[Term], covered : Boolean)(implicit stack: Stack, history: History): (Option[Term], Option[Boolean]) = {
    val TacticsLF.iproof(stps) = tm
    val tp = tpO.get //.getOrElse(return (None, None)) // for now we only use this as a checking rule, but inference is also possible
    val goal = ProofGoal(stack, tp, history + "starting prover")
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val prover = new InteractiveLFProver(solver, rules, goal)
    prover.executeInteractiveProof(stps)

    (Some(prover.prover.lambdaProofTerm) ,Some(true))
  }
}



class InteractiveLFProver(solver : Solver,  val rules: List[ProofStepRule], initGoal: ProofGoal )  {
  val bla  = info.kwarc.mmt.api.frontend.Run

  val prover = new ImperativeProver(initGoal , rules , solver)

  def executeInteractiveProof(stps : List[Term]): Unit = {
    val lock = new Object
    SwingUtilities.invokeAndWait(new GuiProof)
    lock.synchronized{lock.wait()}


    class GuiProof extends Runnable {


      override def run(): Unit = {

        prover.toDoSteps = stps
      //  val ipp = new ImperativeProofPresenter(prover)
        val jf: JFrame = new JFrame("Interactive Proof")
        jf.getContentPane.setLayout(new BorderLayout)

        jf.setSize(1000, 700)
        jf.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)
        val splt0 = new JSplitPane(SwingConstants.HORIZONTAL)
        val splt1 = new JSplitPane(SwingConstants.VERTICAL)
        val splt2 = new JSplitPane(SwingConstants.HORIZONTAL)
    //    val splt3 = new JSplitPane(SwingConstants.VERTICAL)
        val proofStatePanel = new JPanel
 //       val stepHistoryPanel = new JPanel
        val inputPanel = new JPanel
        val completeProofPanel = new ImperativeProofPresenter(prover)
      //  val completeProofLabel = new JLabel(stps.map(x => solver.presentObj(x)).mkString("; "))

        val lambdaLabel = new JTextPane()
        lambdaLabel.setText((prover.solver.presentObj(prover.lambdaProofTerm)))

        //  lambdaLabel.setEditable(false)
        val lambdaPanel = new JScrollPane(lambdaLabel)

        val outputLabel = new JTextArea()
        outputLabel.setEditable(false)
        val outputPanel = new JScrollPane(outputLabel)



        val errorOutputLabel = new JTextArea()
        errorOutputLabel.setEditable(false)
        val errorOutputPanel = new JScrollPane(errorOutputLabel)

        val rawOutputLabel = new JTextArea()
        rawOutputLabel.setEditable(false)
        val rawOutputPanel = new JScrollPane(rawOutputLabel)

        val searchPanel = new JPanel()
        val rawPrintPanel = new JPanel()
        val unicodePrintPanel = new JPanel()
        val pinRulesPanel = new JPanel()
        val scratchPanel = new JPanel()
        // tabs

        val tabbedOutput = new JTabbedPane()
        tabbedOutput.addTab("Proof/Lambda Term" , lambdaPanel)
        tabbedOutput.addTab("Output" , outputPanel)
        tabbedOutput.addTab("Error Output" , errorOutputPanel)
        tabbedOutput.addTab("Raw Output" , rawOutputPanel)
        tabbedOutput.addTab("Search" , searchPanel)
        tabbedOutput.addTab("Raw Print" , rawPrintPanel)
        tabbedOutput.addTab("Unicode Print" , unicodePrintPanel)
        tabbedOutput.addTab("Pin Rules" , pinRulesPanel)
        tabbedOutput.addTab("Scratch" , scratchPanel)

        //tabs

 //       lambdaPanel.add(lambdaLabel)
     //   completeProofPanel.add(completeProofLabel)
        splt0.setBottomComponent(inputPanel)
        splt0.setTopComponent(splt1)
        splt1.setLeftComponent(completeProofPanel)
        splt1.setRightComponent(splt2)
        splt2.setTopComponent(proofStatePanel)
        splt2.setBottomComponent(tabbedOutput)
     //   splt3.setLeftComponent(completeProofLabel)
     //   splt3.setRightComponent(lambdaPanel)
        val proofStateLabel = new JLabel(helperFunctions.printProofState(solver, List(initGoal)))
     //   val stepHistoryLabel = new JLabel()
        proofStatePanel.add(proofStateLabel)
  //      stepHistoryPanel.add(stepHistoryLabel)
        val undoButton = new JButton("Undo Step")
        val forwardButton = new JButton("Step Forward")
        val jumpButton = new JButton("Jump to Cursor")
        inputPanel.add(forwardButton)
        inputPanel.add(undoButton)
        inputPanel.add(jumpButton)
        forwardButton.addActionListener(new NextStep)
        undoButton.addActionListener(new UndoStep)
        jumpButton.addActionListener(new JumpToStep)
        jf.add(splt0)
        jf.setVisible(true)
        jf.addWindowListener(new WakeUp)





        //start: adding titles to the panes

        proofStatePanel.setBorder(BorderFactory.createTitledBorder("Proof State"))
 //       lambdaPanel.setBorder(BorderFactory.createTitledBorder("Proof/Lambda Term"))
        inputPanel.setBorder(BorderFactory.createTitledBorder("Proof Control"))
        completeProofPanel.setBorder(BorderFactory.createTitledBorder("Proof"))
        //end: adding titles to the panes


        //start: divider ration

        splt0.setDividerLocation(1.0)
   //     splt0.setEnabled( false )
        splt0.setResizeWeight(1.0)


        splt1.setDividerLocation(0.4)
        // splt1.setEnabled( false )
        splt1.setResizeWeight(0.4)
        splt2.setDividerLocation(0.7)
        splt2.setResizeWeight(0.7)
        //end: divider ration


        class WakeUp() extends WindowListener {
          override def windowOpened(windowEvent: WindowEvent): Unit = ()

          override def windowClosing(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowClosed(windowEvent: _root_.java.awt.event.WindowEvent): Unit = {
            lock.synchronized{lock.notifyAll()}
          }

          override def windowIconified(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowDeiconified(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowActivated(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowDeactivated(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()
        }





        class NextStep() extends ActionListener {


          def errorOutput = {
            val errTxt : List[SolverError] = prover.solver.getErrors
            val now = Calendar.getInstance().getTime
            errorOutputLabel.setText(now.toString + "\n" +  errTxt.mkString("\n"))
          }

          def nextStep: Unit = {
            if (prover.toDoSteps.isEmpty || prover.errorstate) {return}
            prover.redoStep()
            if (prover.errorstate) {completeProofPanel.nexterror ; errorOutput ;  return}
            proofStateLabel.setText(helperFunctions.printProofState(solver, prover.getGoals))
            val trmTxt = solver.presentObj(prover.lambdaProofTerm)
            lambdaLabel.setText(trmTxt)
            completeProofPanel.next
          }

          override def actionPerformed(ae: ActionEvent): Unit = {
            nextStep
          }
        }


        class UndoStep() extends ActionListener {

          def undoStep: Unit = {
            if (prover.stepHistory.isEmpty) return
            if (prover.errorstate) {completeProofPanel.undoerror; prover.undoErrorStep()  ; return }
            prover.undoStep()
            proofStateLabel.setText(helperFunctions.printProofState(solver, prover.getGoals))
            val trmTxt = solver.presentObj(prover.lambdaProofTerm)
            lambdaLabel.setText(trmTxt)
            completeProofPanel.undo
          }

          override def actionPerformed(ae: ActionEvent): Unit = {
            undoStep
    /*        undoStep()
            proofStateLabel.setText(helperFunctions.printProofState(solver , getGoals) )
            lambdaLabel.setText(solver.presentObj(lambdaProofTerm).replace("?" , "\\\\?")) */
          }
        }

        class JumpToStep() extends ActionListener {
          override def actionPerformed(ae: ActionEvent): Unit = {
            val cpos = completeProofPanel.getCaretPosition
            val currpos = completeProofPanel.currpos

            if (cpos <= currpos) {
              while(completeProofPanel.posStack.nonEmpty && cpos <=  completeProofPanel.posStack.head){
                undoButton.getActionListeners.filter(p => p.isInstanceOf[UndoStep]).head.asInstanceOf[UndoStep].undoStep
              }
              if (completeProofPanel.posStack.isEmpty){
                undoButton.getActionListeners.filter(p => p.isInstanceOf[UndoStep]).head.asInstanceOf[UndoStep].undoStep
              }
            }else if (currpos < cpos){
              while(completeProofPanel.currpos < cpos  && ! prover.errorstate){
                forwardButton.getActionListeners.filter(p => p.isInstanceOf[NextStep]).head.asInstanceOf[NextStep].nextStep
              }
            }

          }
        }
      }
    }
  }
}




class ImperativeProofPresenter(ip : ImperativeProver) extends  JEditorPane {
  var currpos = 0
  val hl = new DefaultHighlightPainter(Color.GREEN)
  val hl0: AnyRef = getHighlighter.addHighlight(0  , 0 , hl)

  val errorhl = new DefaultHighlightPainter(Color.RED)
  val errorhl0: AnyRef = getHighlighter.addHighlight(0  , 0 , errorhl)

//ordered list
  val delims : List[(String , Int) ] = List((";" , 0), ("subproof" , 0))


  var txt : String = ip.toDoSteps.map(x => ip.solver.presentObj(x)).mkString("; ")
  val maxpos : Int = txt.length
  val posStack : ListBuffer[Int] = ListBuffer()
  setText(txt)


  def nextDelimStart(ls : List[(String , Int)]) : (Int, String) = ls match {
    case Nil =>(maxpos, "")
    case lss@(s , v)::xs => {
      val tmp = lss.takeWhile(n => n._2 == v)
      val tmp0 = lss.dropWhile(n => n._2 == v)

      def loop2(ls0 : List[(String , Int)]) : Option[(Int,String)] = ls0 match{
        case Nil => None
        case (s0 , _)::ys => {
          val tmp1 =  txt.indexOf(s0 , currpos) match {case xx if xx < 0 => None ; case xx => Some(xx) }
          (tmp1, loop2(ys)) match {
            case (None, None) => None
            case (Some(ps) , None) => Some((ps , s0))
            case (None , ret) => ret
            case (Some(ps) , ret@Some((ps0 , ss))) => {
              if (ps < ps0){
                Some((ps , s0))
              }else {
                ret
              }
            }
          }
        }
      }
      loop2(tmp) match {
        case None => nextDelimStart(tmp0)
        case Some(vl) => vl
      }
    }
  }

  def next (): Unit = {

    def loop(ls : List[(String , Int)]) : (Int, String) = ls match {
      case Nil =>(maxpos, "")
      case lss@(s , v)::xs => {
        val tmp = lss.takeWhile(n => n._2 == v)
        val tmp0 = lss.dropWhile(n => n._2 == v)

        def loop2(ls0 : List[(String , Int)]) : Option[(Int,String)] = ls0 match{
          case Nil => None
          case (s0 , _)::ys => {
            val tmp1 =  txt.indexOf(s0 , currpos) match {case xx if xx < 0 => None ; case xx => Some(xx) }
            (tmp1, loop2(ys)) match {
              case (None, None) => None
              case (Some(ps) , None) => Some((ps , s0))
              case (None , ret) => ret
              case (Some(ps) , ret@Some((ps0 , ss))) => {
                if (ps < ps0){
                  Some((ps , s0))
                }else {
                  ret
                }
              }
            }
          }
        }
        loop2(tmp) match {
          case None => loop(tmp0)
          case Some(vl) => vl
        }
      }
    }
    val (pos , ss) = loop(delims)
    posStack.insert(0 , currpos)
    currpos = pos + ss.length
    getHighlighter.changeHighlight(hl0, 0 , currpos)

  }

  def undo() : Unit = {
    currpos = posStack.head
    posStack.remove(0)
    getHighlighter.changeHighlight(hl0 , 0 , currpos)
  }

  def nexterror: Unit = {
    val oldcurr = currpos
    val (pos , ss) = nextDelimStart(delims)
    val newcurr = pos + ss.length
    getHighlighter.changeHighlight(errorhl0 , oldcurr , newcurr)
  }

  def undoerror = {
    getHighlighter.changeHighlight(errorhl0 , 0 , 0)
  }

}

/*
abstract class Presenter{

}





class ImperativeProofPresenter(ip : ImperativeProver) extends  JEditorPane {

  var currpos = 0
  val hl = new DefaultHighlightPainter(Color.GREEN)
  val hl0: AnyRef = getHighlighter.addHighlight(0  , 0 , hl)

 // var prooftxt : List[Term] = ip.toDoSteps
//  var toDoSteps : List[Term] = ip.toDoSteps
//  var doneSteps : List[Term] = List()
  val rules: ListBuffer[PrintingRule] = PrintingRuleCollection.rules
  setText(ip.toDoSteps.map(x => ip.solver.presentObj(x)).mkString("; "))
  val preHook : ListBuffer[ImperativeProofPresenter => Unit] = new ListBuffer()
  val postHook : ListBuffer[ImperativeProofPresenter => Unit] = new ListBuffer()
  val preHookUndo : ListBuffer[ImperativeProofPresenter => Unit] = new ListBuffer()
  val postHookUndo : ListBuffer[ImperativeProofPresenter => Unit] = new ListBuffer()
  var undoInstruction : UndoHL = UndoHLDefault
  var nextInstruction :NextHL =  NextHLDefault

  def undo = undoInstruction.undo()
  def next = nextInstruction.next()



  def defaultNextInstruction(s : Term):Unit = {

    val pstrl = getText().drop(if (currpos == 0){0} else {currpos + 1}).takeWhile(c => c != ';').length
    currpos += (if (ip.toDoSteps.isEmpty) {pstrl} else {pstrl + 1})
    val colpos = currpos + 1
    getHighlighter.changeHighlight(hl0 , 0 , colpos)
  }

  def nextInstructionDefault(): Unit = {
    preHook.foreach(x => x(this))
    val tmp = ip.stepHistory.head
 /*   val tmp = toDoSteps.head
    toDoSteps = toDoSteps.tail
    doneSteps = tmp :: doneSteps */
    val stepRule = rules.find(_.applicable(tmp))
    stepRule match {
      case None => defaultNextInstruction(tmp)
      case Some(v) => v(tmp , this )
    }
    postHook.foreach(x => x(this))
  }



  def defaultUndoInstruction(t : Term): Unit = {
    val tmp = getText()
    if (tmp.charAt(currpos) == ';'){
      currpos -= 1
    }
    while (0 < currpos && tmp.charAt(currpos) != ';'){
      currpos -= 1
    }
    getHighlighter.changeHighlight(hl0 , 0 , if (currpos == 0) {0} else {currpos + 1})
  }

  def undoInstructionDefault():Unit ={
    preHookUndo.foreach(x => x(this))
    val tmp = ip.toDoSteps.head
 //   val tmp = doneSteps.head
 //   doneSteps = doneSteps.tail
 //   toDoSteps = tmp :: toDoSteps
    val stepRule = rules.find(_.applicable(tmp))
    stepRule match {
      case None => defaultUndoInstruction(tmp)
      case Some(v) => v.undoApply(tmp , this )
    }
    postHookUndo.foreach(x => x(this))
  }


  object UndoHLDefault extends  UndoHL{
    override def undo(): Unit = undoInstructionDefault()
  }

  object NextHLDefault extends NextHL{
    override def next(): Unit = nextInstructionDefault()
  }
}


abstract class UndoHL {
  def undo() : Unit
}

abstract class NextHL {
  def next() : Unit
}


abstract class PrintingRule(val head : GlobalName) {
  def apply(t : Term  , ipp : ImperativeProofPresenter) : Unit

  def undoApply(t : Term , ipp : ImperativeProofPresenter) : Unit

  def applicable(t : Term): Boolean = t.head.getOrElse(false) == head

}




object SubproofPrintingRule extends PrintingRule(NewTactics.subproof.path) {



  class NextHLSubP(i : ImperativeProofPresenter) extends NextHL {

    override def next():Unit = {
      val tmp = i.getText.drop(i.currpos)
      val j = tmp.indexOf("subproof")
      i.currpos += j + "subproof".length
      i.getHighlighter.changeHighlight(i.hl0 , 0 , i.currpos)
      i.nextInstruction =  i.NextHLDefault

    }
  }

  class UndoHLSubP(i : ImperativeProofPresenter) extends UndoHL {

    override def undo():Unit = {
      val tmp = i.getText.drop(i.currpos)
      var j = tmp.indexOf("subgoal")
      i.currpos += j + "subgoal".length
      i.getHighlighter.changeHighlight(i.hl0 , 0 , i.currpos)
      i.nextInstruction = i.NextHLDefault

    }
  }

  override def apply(t:  Term, ipp:  ImperativeProofPresenter): Unit = {
    new NextHLSubP(ipp).next()
  }
  override def undoApply(t:  Term, ipp:  ImperativeProofPresenter): Unit = {
  //  ipp.undoInstruction = new UndoHLSubP(ipp)
    ipp.defaultUndoInstruction(t)
  }
/** an MMT URI that is used to indicate when the Rule is applicable */

}


object PrintingRuleCollection {
  val rules : ListBuffer[PrintingRule] = ListBuffer(SubproofPrintingRule)

}
*/
/*


class InteractiveProver(var slvr : Solver, override val rules: List[ProofStepRule], initGoal: ProofGoal)  extends ImperativeProver(slvr , rules, initGoal)  {



  val history  : ListBuffer[(Option[Term] , List[ProofGoal])] = ListBuffer((None, List(initGoal)))


  val nbp : NotationBasedParser = solver.controller.extman.get(classOf[NotationBasedParser]).head
//  val context : Context =
//  val string = "type" // test
  //val pu = ParsingUnit(SourceRef.anonymous("fromGUI"),context,string,InterpretationInstructionContext(solver.controller.getNamespaceMap))
//  nbp(pu)(ErrorThrower)

  // var currentState : ProofHistoryStep = ProofHistoryStep(List(initGoal))


  def executeProof(): Unit = {
    solver.report("itp" , "start exe")
    val jf : JFrame = new JFrame("Interactive Proof")
    jf.setSize(500 , 500)
    jf.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)
    val splt0 = new JSplitPane(SwingConstants.HORIZONTAL)
 //   splt0.setDividerLocation(0.7)
    val splt1 = new JSplitPane(SwingConstants.VERTICAL)
    val proofStatePanel = new JPanel
    val stepHistoryPanel = new JPanel
    val inputPanel = new JPanel
    splt0.setBottomComponent(inputPanel)
    splt0.setTopComponent(splt1)
    splt1.setLeftComponent(proofStatePanel)
    splt1.setRightComponent(stepHistoryPanel)
    val proofStateLabel = new JLabel(helperFunctions.printProofState(solver  , history.head._2))
    val stepHistoryLabel = new JLabel()
    proofStatePanel.add(proofStateLabel)
    stepHistoryPanel.add(stepHistoryLabel)
    val undoButton = new JButton("Undo Step")
    val inputText = new JTextField("input your tactics here" , 40)
    inputPanel.add(inputText)
    inputPanel.add(undoButton)
    inputText.addActionListener(new NextStep)
    undoButton.addActionListener(new UndoStep)
    jf.add(splt0)
    jf.setVisible(true)
    solver.report("itp" , "in execute proof ")

    class NextStep() extends ActionListener {
      override def actionPerformed(ae: ActionEvent): Unit = {
        val input = inputText.getText()
        inputText.setText("")
        val ctx = solver.checkingUnit.context
        val pu = ParsingUnit(SourceRef.anonymous("fromGUI"),ctx,input,InterpretationInstructionContext(solver.controller.getNamespaceMap))
        var res : ParseResult  = nbp(pu)(ErrorThrower)
        val step = res.term
        solver = new Solver(solver.controller , helperFunctions.updateCheckingUnit(solver.checkingUnit , res) , solver.rules)
        makeStep(step)
        genCurrStateAndHistoryStep(step)
        val hsteps = history.map(x => x._1 match {case None => "" ; case (Some(s)) => s.toString }).mkString(";")
        stepHistoryLabel.setText(hsteps)
        proofStateLabel.setText(helperFunctions.printGoals(solver , history.head._2))
        solver.report("itp" , "testtest")
      }
    }


    def genCurrStateAndHistoryStep(s : Term): Unit = {
      history.prepend((Some(s) , getGoals))

    }


    class UndoStep() extends ActionListener{
      override def actionPerformed(ae: ActionEvent): Unit = {

      }
    }

  }









}

 */
