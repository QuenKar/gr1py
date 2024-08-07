"""Temporal structures, e.g., transition system and game arena
"""
from __future__ import absolute_import
import itertools


from .minnx import DiGraph


def stategen(symtab):
    statestab = []
    for v in symtab:
        if v['type'] == 'boolean':
            # bool 0，1
            statestab.append(range(2))
        elif v['type'] == 'int':
            # int domain
            statestab.append(range(v['domain'][0], v['domain'][1]+1))
        else:
            raise TypeError('Unrecognized type "'+str(v['type'])
                            +'" of variable "'+str(v['name'])+'"')
        # 计算product，返回集合
        # 比如 ((0,1), (0,1), (0,1)) --> (0,0,0) (0,0,1) (0,1,0) (0,1,1) (1,0,0) ...
    return itertools.product(*statestab)

def ts_from_expr(symtab, exprtab):
    """

    symtab and exprtab are as produced by form.util.gen_expr().
    """
    envtrans = dict()
    systrans = list()

    num_uncontrolled = len([i for i in range(len(symtab)) if symtab[i]['uncontrolled']])
    identifiers = [v['name'] for v in symtab] # r1 r2 r3 g1 g2 g3...
    next_identifiers = [v['name']+'_next' for v in symtab]

    evalglobals = {'__builtins__': None, 'True': True, 'False': False}

    envtrans_formula = '(' + ') and ('.join(exprtab['ENVTRANS']) + ')'
    for state in stategen(symtab):
        stated = dict(zip(identifiers, state))
        envtrans[state] = []
        for next_state in stategen([v for v in symtab if v['uncontrolled']]):
            stated.update(dict(zip(next_identifiers, next_state)))
            if eval(envtrans_formula, evalglobals, stated):
                envtrans[state].append(next_state)
    # print("envtrans:"+str(envtrans))

    systrans_formula = '(' + ') and ('.join(exprtab['SYSTRANS']) + ')'
    for state in stategen(symtab):
        stated = dict(zip(identifiers, state))
        for next_state in stategen(symtab):
            stated.update(dict(zip(next_identifiers, next_state)))
            if eval(systrans_formula, evalglobals, stated):
                systrans.append((state, next_state))

    G = DiGraph()
    G.add_edges_from(systrans)
    for nd in G.nodes():
        G.nodes[nd]['sat'] = list()
        # 把 node 中0 1值和r1 r2..g1 g2映射起来，下面的计算把exprtab公式中r1，r2替换成0，1
        stated = dict(zip(identifiers, nd))
        # stated:{'r1': 1, 'r2': 1, 'r3': 0, 'g1': 1, 'g2': 0, 'g3': 1}...
        # print("stated:" + str(stated))
        for subformula in ['ENVINIT', 'SYSINIT']:
            # 计算公式，如果为真，添加ENVINIT和SYSINIT
            if eval(exprtab[subformula], evalglobals, stated):
                G.nodes[nd]['sat'].append(subformula)
        for subformula in ['ENVGOAL', 'SYSGOAL']:
            for (i, goalexpr) in enumerate(exprtab[subformula]):
                if eval(goalexpr, evalglobals, stated):
                    # 计算公式，如果为真，添加子公式
                    G.nodes[nd]['sat'].append(subformula+str(i))
                    
    return AnnTransitionSystem(symtab, G, envtrans,
                               num_egoals=len(exprtab['ENVGOAL']),
                               num_sgoals=len(exprtab['SYSGOAL']))

class AnnTransitionSystem(object):
    """Annotated transition system
    """
    def __init__(self, symtab, G, envtrans, num_egoals, num_sgoals):
        """

        Parameters are stored by reference, not copied.
        """
        self.G = G
        self.symtab = symtab
        self.envtrans = envtrans
        self.num_egoals = num_egoals
        self.num_sgoals = num_sgoals
        # example里面的ind_uncontrollered:[0, 1, 2]
        self.ind_uncontrolled = [i for i in range(len(symtab)) if symtab[i]['uncontrolled']]
    
    def __str__(self) -> str:
        return "\nGraph:\n" + str(self.G) + "\nsymtab:" + str(self.symtab) + "\nenvtrans:" + str(self.envtrans) + "\nind_uncontrollered:" + str(self.ind_uncontrolled) 
