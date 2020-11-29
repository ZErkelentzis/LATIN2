package latin2.sfol

import info.kwarc.mmt.api.GlobalName
import info.kwarc.mmt.api.objects.{OMV, Term}

class GenCriteria(GenMode: Int = 1, variables: Int = 3, literals: Int = 3, RequestedType: Term = null,
                  MinDepth: Int = 0, MaxDepth: Int = -1, escalate: Boolean = false, enum: Int = 100, senum: Int = 100,
                  Ratio: Int = 50, Formula: Boolean = false, TermCriteria: GenCriteria = null,
                  qmin: Int = 0, qmax: Int = 0, quant: Boolean = true, anum: Int = 100, skip: Boolean = false,
                  exclude: List[GlobalName] = List[GlobalName](), temp: Term = null,
                  sublist: List[(OMV, Term, Int)] = null) {
  //todo: do we even have to clarify Formula? We could take that info from the RequestedType. On the other hand,
  //todo: tc generation might require it.
  //todo: here we make all the term criteria
  //form - whether the criteria are for formulas or terms
  //mode - Term generation: Forward or backward generation
  //tp - Term Generation: The requested term type
  //min: the minimal syntax tree depth to be generated
  //max: the maximal syntax tree depth
  //rat: aimed Ratio/Percentage of variables vs literals. 80 means there is a 80% chance a variable is used
  //tc: term generation criteria for formula generation
  //todo: clarify empty functions, as those are (generally?) definition of base values (zero, true, etc)
  //todo: is it even useful to mix those with literals? might be better to seperate them in generation
  def varnum = variables
  def litnum = literals
  def form: Boolean = Formula
  def mode: Int = GenMode
  def tp: Term = RequestedType
  def atomicformulas = anum
  def skipatomics = skip
  //we can propably delete minimum depth
  def min: Int = MinDepth
  def max: Int = MaxDepth
  def escdepth: Int = enum
  def sescdepth: Int = senum
  def escalation: Boolean = escalate
  def rat: Int = Ratio
  //instead of minimal and maximal quantifiers, we should be more concerned with quantifer alteration. Min/Max?
  def quantors: Boolean = quant
  def quantmax: Int = qmax
  def quantmin: Int = qmin
  def tc: GenCriteria = {
    if(Formula && (TermCriteria == null)){
      new GenCriteria()
    }
    else TermCriteria
  }
  //a list that allows the targeted exclusion of operators on both theory level and SFOL level
  def exclusionlist: List[GlobalName] = exclude
  //a template can come in 2 variants - an absolute template, and an infinite template
  //examples for absolute templates:
  //ax^2 + bx + c, where a, b, c are to be substituted with a literal
  //pred1(t1) and pred(t2) or (t3=t4). where t1 to t4 are terms
  //examples for infinite template
  //Horn Formula, CNF, sum.
  //todo: how to handle infinite templates
  def template: Term = temp
  def substitute: List[(OMV, Term, Int)] = sublist

  //todo: here we make formula criteria. What are potential criteria for formulas?
  //todo: 1. min/max depth, like with terms
  //todo: 2. number of different operators (and, or, imply, equal, etc) (we can use that for terms as well?)
  //todo: 3. Implement potential template system. Make new template object for that. Formulate problems.
  //todo: 4. We might require a third mode then - one that can work with templates.


  //todo: As most criteria will affect generation directly, it would make sense to say that GenCriteria is to
  //todo: be given directly to the generator method. Mainquestion: How to handle the different criteria for
  //todo: term and formula generation.
  //todo: What does TermGenerator() want? So far: mode (backwards?), type (output), min (depth), max (depth)
  //todo: potentially: ratio (literals/variables), generation template, number of different operators (min, max)

  //todo: problems with templates: require knowledge of syntax, knowledge of theory, n-ary operators
  //todo: how to save the template (list would only allow for binary operators, n-ary requires workaround)
  //todo: how to save positions of predicates and variables, different data types
  //todo: potential: make template object for positions and save those in list.

  //todo: Class to hand over all criteria for Term generation a user might have
  //todo: What to include here? Depth, complexity, maybe even a template?
  //todo: When to hand over this object? I think initialization.
  //The term generator recieves several parameters.
  //-mode: This chooses whether forwards or backwards generation is applied. Not introduced here, it's better to
  //choose the mode when calling the method
  //-number of variables: important at init, chooses how many different variables per type we have available
  //todo: number of variables
  //-number of literals: how many different literals we will use for generation of terms.
  //todo: number of literals
  //-potentially: ration literals to variables, to ensure certain terms are generated at a higher rate.
  //todo: lit/var (is this even necessary?)
  //-template: if a very special form of a term is required, a template has to be provided. But here, or simply in a
  //-own method?
}
