# =============================
# Student Names: Nicholas Tillo & Raksha Rehal
# Group ID: 62
# Date: 2024 - 1 - 28
# =============================
# CISC 352 - W23
# propagators.py
# desc:
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
    #IMPLEMENT
    pruned = []
    if not newVar:
        """for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints."""
        for c in csp.get_all_cons():
            if c.get_n_unasgn() == 1:
                for i in c.get_scope():
                    if var.get_assigned_value() == None:
                        un_ass_val = i
                        break
                for i in un_ass_val.cur_domain():
                    flag = c.check_var_val(un_ass_val,i)
                    if not flag:
                       #PRUNE
                        un_ass_val.prune_value(i)
                        pruned.append((un_ass_val,i))
                    if un_ass_val.cur_domain() == []:    
                        return False, pruned
        return True, pruned
    
    else:
        """for forward checking we forward check all constraints with V
         that have one unassigned variable left"""
        #For each constraint. 
        for c in csp.get_cons_with_var(newVar):
            #If it has exactly 1 unassigned variable. 
            if c.get_n_unasgn() == 1:
                #Init Values
 
                #Get all variables within the constraint. 
                vars = c.get_scope()
                #For each var, if its unassigned, save for later.
                for var in vars:
                    if var.get_assigned_value() == None:
                        un_ass_val = var
                        break

                #Test each value out, If it ever returns false, prune it from the old tree. 
                for i in un_ass_val.cur_domain():
                    flag = c.check_var_val(un_ass_val,i)
                    if not flag:
                       #PRUNE
                        un_ass_val.prune_value(i)
                        pruned.append((un_ass_val,i))
                      
                if un_ass_val.cur_domain() == []:    
                    return False, pruned
        return True, pruned


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #IMPLEMENT
    pruned = []

    if not newVar:
        """for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp"""
        
        queue = csp.get_all_cons()[:]
        
        while len(queue) > 0:
            # check the consistencies of the arcs starting from the tail of the queue.
            # this is in the form [x_i, [X]]
            
            # current is a constraint
            current = queue.pop(0)
            vars_with_c = current.get_scope()

            # build the arc
            for var in vars_with_c:

                if var.cur_domain() == []:
                    return False, pruned

                for i in var.cur_domain():
                    flag = current.check_var_val(var,i)

                    if not flag:
                        #PRUNE
                        var.prune_value(i)
                        pruned.append((var,i))

                        # if a value was removed from x_i's domain, we want to add all the neighbours 
                        # (say, x_k) of x_i to the queue in the form of [x_k, [X_K]] where X_K are all
                        # the variables connected to x_k via (all of?) x_k's contraints.

                        # i.e. add the neighbours of newVar and their neighbours to the queue in the same 
                        # way of (x_k, X)
                            
                        temp = vars_with_c[:]
                        temp.remove(var)

                        for neighbour in temp:
                            queue.extend(csp.get_cons_with_var(neighbour))
                
        return True, pruned
    
    else:
        """for gac we initialize the GAC queue with all constraints containing V."""

        queue = csp.get_cons_with_var(newVar)[:]
        
        while len(queue) > 0:
            # check the consistencies of the arcs starting from the tail of the queue.
            # this is in the form [x_i, [X]]
            
            # current is a constraint
            current = queue.pop(0)
            vars_with_c = current.get_scope()

            # build the arc
            for var in vars_with_c:

                if var.cur_domain() == []:
                    return False, pruned

                for i in var.cur_domain():
                    flag = current.check_var_val(var,i)
                    if not flag:
                        #PRUNE
                        var.prune_value(i)
                        pruned.append((var,i))

                        # if a value was removed from x_i's domain, we want to add all the neighbours 
                        # (say, x_k) of x_i to the queue in the form of [x_k, [X_K]] where X_K are all
                        # the variables connected to x_k via (all of?) x_k's contraints.

                        # i.e. add the neighbours of newVar and their neighbours to the queue in the same 
                        # way of (x_k, X)
                            
                        temp = vars_with_c[:]
                        temp.remove(var)

                        for neighbour in temp:
                            queue.extend(csp.get_cons_with_var(neighbour))
                
        return True, pruned

