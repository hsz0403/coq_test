import os
import pdb
from coqpyt.coq.structs import TermType
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.changes import ProofAppend, ProofPop
from coqpyt.coq.exceptions import InvalidChangeException,InvalidAddException

'''Print Ltac is_var.
(* Print Ltac Signatures. *)
Print Tables.
Print Grammar constr.
Print Libraries.
Print ML Modules.
Print LoadPath.'''

def reset_proof(file: ProofFile):
    file.run()
    proven = file.proofs[1]
    print(proven)
    file.pop_step(proven)
    file.pop_step(proven)
    file.pop_step(proven)
    file.append_step(proven, "\nAdmitted.")

import inspect

def get_properties(obj):
    properties = []
    for name, value in inspect.getmembers(obj.__class__):
        if isinstance(value, property):
            properties.append(name)
    return properties



#with ProofFile(os.path.join(os.getcwd(), "examples/test.v")) as proof_file:
with ProofFile('/cpfs01/shared/public/llm_math/wangjiayu/szh/coq/coqpyt/examples/test_data/mathd_numbertheory_207.v') as proof_file:
    
    #proof_file.exec(nsteps=4)#=1 no error
    proof_file.run()
   
    print(proof_file.unproven_proofs)
    #pdb.set_trace()
    # Get the first admitted proof
    '''unproven = proof_file.unproven_proofs[0]
    print( proof_file.steps[-1].text)
    proof_file.pop_step(unproven)
    print(proof_file.steps)
    proof_file.pop_step(unproven)
    print(proof_file.steps)
    proof_file.append_step(unproven, '\nProof.')'''
    #print(unproven)
    props = get_properties(proof_file)
    for prop in props:
        try:
            print(f"{prop}: {getattr(proof_file, prop)}")
        except:
            pass
    print(props) 
    #pdb.set_trace()
    exit()
    #proof_file.can_close_proof
    #str(proof_file.current_goals.goals.goals[0])
    #proof_file.prev_step
    #proof_file.unproven_proofs
    #proof_file.steps
    unproven=proof_file.unproven_proofs[0]
    changes=[]
    incorrect = [ " reflexivity."]
    for s in incorrect:
        changes.append(ProofAppend(s))
    #proof_file.change_proof(unproven, changes)
    try:
        proof_file.append_step(unproven, '\nintros.')
    except InvalidAddException:
        print("Proof attempt not valid.")
    #proof_file.pop_step(unproven)
    print(unproven.steps)
    #print( ''.join([unproven.steps[i].text for i in range(len(unproven.steps))]))
    
    exit()


    # Steps for an incorrect proof
    incorrect = [" reflexivity.", "\nQed."]
    # Steps for a correct proof
    correct = [" rewrite app_assoc."] + incorrect

    # Loop through both attempts
    for attempt in [incorrect,incorrect,correct]:
        # Schedule the removal of the "\nAdmitted." step
        changes = [ProofPop()]
        # Schedule the addition of each step in the attempt
        for s in attempt:
            changes.append(ProofAppend(s))
        try:
            # Apply all changes in one batch
            print(unproven, changes)
            proof_file.change_proof(unproven, changes)
            
            print("Proof succeeded!")
            break
        except InvalidChangeException:
            # Some batch of changes was invalid
            # Rollback is automatic, so no rollback needed
            print("Proof attempt not valid.")


'''with ProofFile(os.path.join(os.getcwd(), "examples/test.v")) as proof_file:
    
    proof_file.run()
    # Get the first admitted proof
    unproven = proof_file.proofs[0]
    # Steps for an incorrect proof
    incorrect = [" reflexivity.", "\nQed."]
    # Steps for a correct proof
    correct = [" rewrite app_assoc."] + incorrect
    print(proof_file.unproven_proofs)
    # Loop through both attempts
    for attempt in [incorrect, correct]:
        # Schedule the removal of the "\nAdmitted." step
        changes = [ProofPop()]
        # Schedule the addition of each step in the attempt
        for s in attempt:
            changes.append(ProofAppend(s))
        print(changes)
        #proof_file.change_proof(unproven, changes)
        try:
            # Apply all changes in one batch
            proof_file.change_proof(unproven, changes)
            print("Proof succeeded!")
            break
        except InvalidChangeException:
            # Some batch of changes was invalid
            # Rollback is automatic, so no rollback needed
            print("Proof attempt not valid.")'''