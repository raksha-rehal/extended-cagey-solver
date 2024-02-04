# =============================
# Student Names: Nicholas Tillo & Raksha Rehal
# Group ID: 62
# Date: 2024 - 1 - 28
# =============================
# CISC 352 - W23
# propagators.py
# desc: implementations of two filtering methods, i.e. forward-checking
# and generalized arc consistency. 
#


#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.

from itertools import permutations

'''This file will contain different constraint propagators to be used within
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check_tuple(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''
    
    # pruned will keep track of tuples consisting of a variable and the
    # value pruned from its domain.
    pruned = []

    if not newVar:
        """for forward checking (where we only check constraints with one
        remaining variable)...
        
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints."""

        # for each constraint in the csp...
        for c in csp.get_all_cons():

            # check to see if the current constraint contains exactly one
            # unassigned value... 
            if c.get_n_unasgn() == 1:

                # ... if so, we seek to find this unsassigned variable and can
                # do this by going into the constraint's scope and checking 
                # the assigned value of each variable.

                for i in c.get_scope():
                    if var.get_assigned_value() == None:
                        un_ass_val = i
                        break
                
                # we then check the current domain of this unassigned variables
                # to see if any of them need to be pruned according to the
                # unary constraint.
                    
                for i in un_ass_val.cur_domain():
                    flag = c.check_var_val(un_ass_val,i)
                    
                    # if there are no satisfying tuples involving this value,
                    # we will prune it within the variable and constraint
                    # it is involved in.
                    if not flag:  
                       #PRUNE
                        un_ass_val.prune_value(i)
                        pruned.append((un_ass_val,i))

                    # if the domain is simply empty, we have hit a dead-end
                    # and need to backtrack.
                    if un_ass_val.cur_domain() == []:    
                        return False, pruned
        
        # indicates that the assignment is valid. 
        return True, pruned
    
    else:
        """for forward checking we forward check all constraints with V
         that have one unassigned variable left"""
        
        # the FC algorithm is repeated, except in this case,
        # instead of looping through all constraints within the csp,
        # we loop through only constraints that newVar is involved with.
        for c in csp.get_cons_with_var(newVar):

            if c.get_n_unasgn() == 1:
                vars = c.get_scope()

                for var in vars:
                    if var.get_assigned_value() == None:
                        un_ass_val = var
                        break

                for i in un_ass_val.cur_domain():
                    flag = c.check_var_val(un_ass_val,i)

                    if not flag:  # prune if it cannot satisfy.
                        un_ass_val.prune_value(i)
                        pruned.append((un_ass_val,i))
                      
                if un_ass_val.cur_domain() == []:    
                    return False, pruned
                
        return True, pruned


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''

    pruned = []

    if not newVar:
        """for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp"""
        
        queue = csp.get_all_cons()[:]
        
        while len(queue) > 0:
            # check the consistencies of the arcs within the queue...
            
            # we will go through checking each constraint by accessing
            # them individually from the front of the queue.
            current = queue.pop(0)
            vars_with_c = current.get_scope()

            # we will then check each variable involved in the current
            # constraint to see if its values are consistent with what
            # they are allowed to be assigned as per the constraint...
            for var in vars_with_c:

                # if there are no possible values that can be assigned
                # to a variable, this is a dead-end and we need to
                # backtrack (return False).
                if var.cur_domain() == []:
                    return False, pruned

                # else, we check that the values available in the current
                # domain of var would not cause a conflict as per the
                # constraint...
                for i in var.cur_domain():
                    flag = current.check_var_val(var,i)

                    # in the case of a variable not satisfying...
                    # we will prune it.
                    if not flag: 
                        var.prune_value(i)
                        pruned.append((var,i))

                        # if a value was removed from x_i's domain, we want 
                        # to add all the constraints of the connected variables 
                        # (i.e. connected via x_i due to the scope of the current 
                        # constraint) to the queue to check them for consistency.

                        # this is the propogation step, essentially.
                        temp = vars_with_c[:]
                        temp.remove(var)

                        for neighbour in temp:
                            queue.extend(csp.get_cons_with_var(neighbour))
                
        return True, pruned
    
    else:
        """for gac we initialize the GAC queue with all constraints containing V."""

        # the gac algorithm is repeated the same as described above,
        # however the queue is now initialized with just constraints 
        # that newVar is involved in.
        queue = csp.get_cons_with_var(newVar)[:]
        
        while len(queue) > 0:
            current = queue.pop(0)
            vars_with_c = current.get_scope()

            for var in vars_with_c:

                if var.cur_domain() == []:
                    return False, pruned

                for i in var.cur_domain():
                    flag = current.check_var_val(var,i)

                    if not flag:
                        var.prune_value(i)  # prune if it cannot satisfy.
                        pruned.append((var,i))
                            
                        temp = vars_with_c[:]
                        temp.remove(var)

                        for neighbour in temp:
                            queue.extend(csp.get_cons_with_var(neighbour))
                
        return True, pruned

