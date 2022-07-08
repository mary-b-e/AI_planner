#!/usr/bin/env python3

from logic import *
# from submission import *

import pickle, gzip, os, random
import graderUtil

grader = graderUtil.Grader()
submission = grader.load('submission')

# name: name of this formula (used to load the models)
# predForm: the formula predicted in the submission
# preconditionForm: only consider models such that preconditionForm is true
def checkFormula(name, predForm, preconditionForm=None):
    filename = os.path.join('models', name + '.pklz')
    objects, targetModels = pickle.load(gzip.open(filename))
    # If preconditionion exists, change the formula to
    preconditionPredForm = And(preconditionForm, predForm) if preconditionForm else predForm
    predModels = performModelChecking([preconditionPredForm], findAll=True, objects=objects)
    ok = True
    def hashkey(model): return tuple(sorted(str(atom) for atom in model))
    targetModelSet = set(hashkey(model) for model in targetModels)
    predModelSet = set(hashkey(model) for model in predModels)
    for model in targetModels:
        if hashkey(model) not in predModelSet:
            grader.fail("Your formula (%s) says the following model is FALSE, but it should be TRUE:" % predForm)
            ok = False
            printModel(model)
            return
    for model in predModels:
        if hashkey(model) not in targetModelSet:
            grader.fail("Your formula (%s) says the following model is TRUE, but it should be FALSE:" % predForm)
            ok = False
            printModel(model)
            return
    grader.addMessage('You matched the %d models' % len(targetModels))
    grader.addMessage('Example model: %s' % rstr(random.choice(targetModels)))
    grader.assignFullCredit()

# DO NOT MODIFY CODE IN GRADER OR POINTS WILL BE DEDUCTED
def checkBlocksWorldModPlan(name, output):
    print("Output from blocksWorldModPlan(): {output}")
    if len(output) == 3:
        grader.addMessage('Please make modifications to the initial and goal states!')
        grader.fail('No modifications have been made')
    elif len(output) == 5:
        grader.addMessage('Correct!')
        grader.assignFullCredit()

def checkLogisticsPlan(name, output):
    print("Output from blocksWorldModPlan(): {output}")
    grader.assignFullCredit()

# name: name of this formula set (used to load the models)
# predForms: formulas predicted in the submission
# predQuery: query formula predicted in the submission
def addParts(name, numForms, predictionFunc):
    # part is either an individual formula (0:numForms), all (combine everything)
    def check(part):
        predForms, predQuery = predictionFunc()
        if len(predForms) < numForms:
            grader.fail("Wanted %d formulas, but got %d formulas:" % (numForms, len(predForms)))
            for form in predForms: print(('-', form))
            return
        if part == 'all':
            checkFormula(name + '-all', AndList(predForms))
        elif part == 'run':
            # Actually run it on a knowledge base
            #kb = createResolutionKB()  # Too slow!
            kb = createModelCheckingKB()

            # Need to tell the KB about the objects to do model checking
            filename = os.path.join('models', name + '-all.pklz')
            objects, targetModels = pickle.load(gzip.open(filename))
            for obj in objects:
                kb.tell(Atom('Object', obj))

            # Add the formulas
            for predForm in predForms:
                response = kb.tell(predForm)
                showKBResponse(response)
                grader.requireIsEqual(CONTINGENT, response.status)
            response = kb.ask(predQuery)
            showKBResponse(response)

        else:  # Check the part-th formula
            checkFormula(name + '-' + str(part), predForms[part])

    def createCheck(part): return lambda : check(part)  # To create closure

    for part in list(range(numForms)) + ['all', 'run']:
        if part == 'all':
            description = 'test implementation of %s for %s' % (part, name)
        elif part == 'run':
            description = 'test implementation of %s for %s' % (part, name)
        else:
            description = 'test implementation of statement %s for %s' % (part, name)
        grader.addBasicPart(name + '-' + str(part), createCheck(part), maxPoints=1, maxSeconds=10000, description=description)

############################################################
# Problem 1: propositional logic

grader.addBasicPart('1a', lambda : checkFormula('1a', submission.formula1a()), 2, description='Test formula 1a implementation')
grader.addBasicPart('1b', lambda : checkFormula('1b', submission.formula1b()), 2, description='Test formula 1b implementation')
grader.addBasicPart('1c', lambda : checkFormula('1c', submission.formula1c()), 2, description='Test formula 1c implementation')

############################################################
# Problem 2: first-order logic

formula2a_precondition = AntiReflexive('Mother')
formula2b_precondition = AntiReflexive('Child')
formula2c_precondition = AntiReflexive('Child')
formula2d_precondition = AntiReflexive('Parent')
grader.addBasicPart('2a', lambda : checkFormula('2a', submission.formula2a(), formula2a_precondition), 2, description='Test formula 2a implementation')
grader.addBasicPart('2b', lambda : checkFormula('2b', submission.formula2b(), formula2b_precondition), 2, description='Test formula 2b implementation')
grader.addBasicPart('2c', lambda : checkFormula('2c', submission.formula2c(), formula2c_precondition), 2, description='Test formula 2c implementation')
grader.addBasicPart('2d', lambda : checkFormula('2d', submission.formula2d(), formula2d_precondition), 2, description='Test formula 2d implementation')

############################################################
# Problem 3: liar puzzle

# Add 3a-[0-5], 3a-all, 3a-run
addParts('3a', 6, submission.liar)
# grader.addBasicPart('3a', lambda : addParts('3a', 6, submission.liar), 2, description='Test formula 3a implementation')

############################################################
# Problem 4: planning
grader.addBasicPart('4a', lambda : checkBlocksWorldModPlan('6a', submission.blocksWorldModPlan()), 2, description='Test formula 4a implementation')
grader.addBasicPart('4b', lambda : checkLogisticsPlan('6b', submission.logisticsPlan()), 2, description='Test formula 4b implementation')

grader.grade()
