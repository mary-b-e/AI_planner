import collections, sys, os
from logic import *
from planning import *

############################################################
# Problem 1: propositional logic
# Convert each of the following natural language sentences into a propositional
# logic formula.  See rainWet() in examples.py for a relevant example.

# Sentence: "If it's summer and we're in California, then it doesn't rain."
def formula1a():
    # Predicates to use:
    Summer = Atom('Summer')               # whether it's summer
    California = Atom('California')       # whether we're in California
    Rain = Atom('Rain')                   # whether it's raining
    # BEGIN_YOUR_CODE (our solution is 1 line of code, but don't worry if you deviate from this)
    return Implies(And(Summer, California),Not(Rain))
    # END_YOUR_CODE

# Sentence: "It's wet if and only if it is raining or the sprinklers are on."
def formula1b():
    # Predicates to use:
    Rain = Atom('Rain')              # whether it is raining
    Wet = Atom('Wet')                # whether it it wet
    Sprinklers = Atom('Sprinklers')  # whether the sprinklers are on
    # BEGIN_YOUR_CODE (our solution is 1 line of code, but don't worry if you deviate from this)
    return And(Implies(Wet,Or(Rain, Sprinklers)), Implies(Or(Rain, Sprinklers),Wet))
    # END_YOUR_CODE

# Sentence: "Either it's day or night (but not both)."
def formula1c():
    # Predicates to use:
    Day = Atom('Day')     # whether it's day
    Night = Atom('Night') # whether it's night
    # BEGIN_YOUR_CODE (our solution is 1 line of code, but don't worry if you deviate from this)
    return Or(And(Day, Not(Night)), And(Not(Day),Night))
    # END_YOUR_CODE

############################################################
# Problem 2: first-order logic

# Sentence: "Every person has a mother."
def formula2a():
    # Predicates to use:
    def Person(x): return Atom('Person', x)        # whether x is a person
    def Mother(x, y): return Atom('Mother', x, y)  # whether x's mother is y

    # Note: You do NOT have to enforce that the mother is a "person"
    # BEGIN_YOUR_CODE (our solution is 1 line of code, but don't worry if you deviate from this)
    return Forall('$x', Implies(Person('$x'), Exists('$y', Mother('$x', '$y'))))
    # END_YOUR_CODE

# Sentence: "At least one person has no children."
def formula2b():
    # Predicates to use:
    def Person(x): return Atom('Person', x)        # whether x is a person
    def Child(x, y): return Atom('Child', x, y)    # whether x has a child y

    # Note: You do NOT have to enforce that the child is a "person"
    # BEGIN_YOUR_CODE (our solution is 1 line of code, but don't worry if you deviate from this)
    return Not(Forall('$x', Implies(Person('$x'), Exists('$y', Child('$x', '$y')))))
    # END_YOUR_CODE

# Return a formula which defines Daughter in terms of Female and Child.
# See parentChild() in examples.py for a relevant example.
def formula2c():
    # Predicates to use:
    def Female(x): return Atom('Female', x)            # whether x is female
    def Child(x, y): return Atom('Child', x, y)        # whether x has a child y
    def Daughter(x, y): return Atom('Daughter', x, y)  # whether x has a daughter y
    # BEGIN_YOUR_CODE (our solution is 4 lines of code, but don't worry if you deviate from this)
    return Forall('$x', Forall('$y', Equiv(And(Female('$x'), Child('$y', '$x')), Daughter('$y', '$x'))))
    # END_YOUR_CODE

# Return a formula which defines Grandmother in terms of Female and Parent.
# Note: It is ok for a person to be her own parent
def formula2d():
    # Predicates to use:
    def Female(x): return Atom('Female', x)                  # whether x is female
    def Parent(x, y): return Atom('Parent', x, y)            # whether x has a parent y
    def Grandmother(x, y): return Atom('Grandmother', x, y)  # whether x has a grandmother y
    # BEGIN_YOUR_CODE (our solution is 5 lines of code, but don't worry if you deviate from this)

    return Forall('$gen1', Forall('$gen3', Equiv(Exists( '$gen2',And(And(Female('$gen1'), Parent('$gen2', '$gen1')), Parent('$gen3', '$gen2'))), Grandmother('$gen3', '$gen1'))))
    # END_YOUR_CODE

############################################################
# Problem 3: Liar puzzle

# Facts:
# 0. John: "It wasn't me!"
# 1. Susan: "It was Nicole!"
# 2. Mark: "No, it was Susan!"
# 3. Nicole: "Susan's a liar."
# 4. Exactly one person is telling the truth.
# 5. Exactly one person crashed the server.
# Query: Who did it?
# This function returns a list of 6 formulas corresponding to each of the
# above facts.
# Hint: You might want to use the Equals predicate, defined in logic.py.  This
# predicate is used to assert that two objects are the same.
# In particular, Equals(x,x) = True and Equals(x,y) = False iff x is not equal to y.
def liar():
    def TellTruth(x): return Atom('TellTruth', x)
    def CrashedServer(x): return Atom('CrashedServer', x)
    john = Constant('john')
    susan = Constant('susan')
    nicole = Constant('nicole')
    mark = Constant('mark')
    formulas = []
    # We provide the formula for fact 0 here.
    formulas.append(Equiv(TellTruth(john), Not(CrashedServer(john))))
    
    # You should add 5 formulas, one for each of facts 1-5.
    # BEGIN_YOUR_CODE (our solution is 11 lines of code, but don't worry if you deviate from this)
    formulas.append(Equiv(TellTruth(susan), CrashedServer(nicole)))
    formulas.append(Equiv(TellTruth(mark), CrashedServer(susan)))
    formulas.append(Equiv(TellTruth(nicole), Not(TellTruth(susan))))
    formulas.append(Or(And(TellTruth(john), And(Not(TellTruth(susan)), And(Not(TellTruth(nicole)), Not(TellTruth(mark))))), 
        Or(And(Not(TellTruth(john)), And(TellTruth(susan), And(Not(TellTruth(nicole)), Not(TellTruth(mark))))), 
        Or(And(Not(TellTruth(john)), And(Not(TellTruth(susan)), And(TellTruth(nicole), Not(TellTruth(mark))))),
        And(Not(TellTruth(john)), And(Not(TellTruth(susan)), And(Not(TellTruth(nicole)), TellTruth(mark))))))))
    formulas.append(
        Or(And(CrashedServer(john), And(Not(CrashedServer(susan)), And(Not(CrashedServer(nicole)), Not(CrashedServer(mark))))), 
        Or(And(Not(CrashedServer(john)), And(CrashedServer(susan), And(Not(CrashedServer(nicole)), Not(CrashedServer(mark))))), 
        Or(And(Not(CrashedServer(john)), And(Not(CrashedServer(susan)), And(CrashedServer(nicole), Not(CrashedServer(mark))))),
        And(Not(CrashedServer(john)), And(Not(CrashedServer(susan)), And(Not(CrashedServer(nicole)), CrashedServer(mark))))))))
    # END_YOUR_CODE
    query = CrashedServer('$x')
    return (formulas, query)


############################################################
# Problem 4: Planning 

# Blocks world modification
def blocksWorldModPlan():
    # BEGIN_YOUR_CODE (make modifications to the initial and goal states)
    initial_state = 'On(A, B) & Clear(A) & OnTable(B) & OnTable(D) & On(C,D) & Clear(C)'
    goal_state = 'On(B, A) & On(C, B) & On(D,C)'
    # END_YOUR_CODE

    planning_problem = \
    PlanningProblem(initial=initial_state,
                    goals=goal_state,
                    actions=[Action('ToTable(x, y)',
                                    precond='On(x, y) & Clear(x)',
                                    effect='~On(x, y) & Clear(y) & OnTable(x)'),
                             Action('FromTable(y, x)',
                                    precond='OnTable(y) & Clear(y) & Clear(x)',
                                    effect='~OnTable(y) & ~Clear(x) & On(y, x)')])
    print(linearize(GraphPlan(planning_problem).execute()))
    return linearize(GraphPlan(planning_problem).execute())

def logisticsPlan():
    # BEGIN_YOUR_CODE (use the previous problem as a guide and uncomment the starter code below if you want!)
    initial_state = 'In(C1, R1) & In(C2, D1) & In(C3, D2) & In(R1, D1) & Holding(R1)'
    goal_state = 'In(C1, D3) & In(C2, D3) & In(C3, D3)'

    planning_problem = \
    PlanningProblem(initial = initial_state,
                    goals = goal_state,
                    actions=[Action('PickUp(r, c, d)',
                                    precond='In(r, d) & In (c, d) & ~Holding(r)',
                                    effect='Holding(r) & ~In(c, d) & In(c, r)', 
                                    domain='Robot(r) & Place(d) & Container(c)'),
                             Action('PutDown(r, c, d)', 
                                    precond='In(r, d) & In(c, r) & Holding(r)',
                                    effect='~Holding(r) & ~In(c, r) & In(c, d)',
                                    domain='Robot(r) & Place(d) & Container(c)'),
                             Action('Move(r, d_start, d_end)',
                                    precond='In(r,d_start)',
                                    effect='~In(r, d_start) & In(r, d_end)',
                                    domain='Robot(r) & Place(d_start) & Place(d_end)')],
                    domain='Container(C1) & Container(C2) & Container(C3) & Place(D1) & Place(D2) & Place(D3) & Robot(R1)')
    # END_YOUR_CODE
    
    return linearize(GraphPlan(planning_problem).execute())

""" **IMPORTANT** Reflection (4 pts)
    For this problem I have three different defined actions- pick up, put down, and move. Pick up changes the location of a container 
    from in a room to inside a robot, making sure to update the appropriate states so it is no longer inside the room and is inside the 
    robot. I also use a variable that states whether or not the robot is already holding something as the robot can only carry one thing
    at a time. This variable is also used in the action PutDown since it must check what the robot is holding and changes the location of
    the container from inside the robot to inside the room. Finally in moving the robot, it changes the location of the robot from it's
    starting position to the ending position. Any time a location changes, the previous location predicate is negated to ensure that 
    an object is only in one area at a time. I also included domains specifying whether the variables are containers, places, or a robot
    so that the algorithm doesn't try something like put a container in a container and move that instead of a robot. 
    The output for this algorithm is incorrect however, I believe this is because there appears to be an issue in updating the states as 
    it doesn't always seem to correctly check the preconditions for each action. It also may be due to issues in removing mutually exclusive
    actions, or in removing repeated actions when the environment is in different states, in the planning algorithm due to the need to 
    repeatedly enter the same room. The true action that should be recorded are 

    Move[R1, D1, D3], PutDown[R1, C1, D3], Move[R1, D3, D1], PickUp[R1, C2, D1], Move[R1, D1, D3], PutDown[R1, C2, D3], Move[R1, D3, D2], 
    PickUp[R1, C3, D2], Move[R1, D2, D3], PutDown[R1, C3, D3]

    or 

    Move[R1, D1, D3], PutDown[R1, C1, D3], Move[R1, D3, D2], PickUp[R1, C3, D2], Move[R1, D2, D3], PutDown[R1, C3, D3], Move[R1, D3, D1], 
    PickUp[R1, C2, D1], Move[R1, D1, D3], PutDown[R1, C2, D3]
"""