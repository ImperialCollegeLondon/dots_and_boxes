# -*- coding: utf-8 -*-
"""
Created on Tue Nov  5 14:46:06 2019

@author: ellen
"""
import numpy as np

def value(Chains,Loops):
    if Chains.size == 0 and Loops.size == 0 :
        return 0
    elif Loops.size == 0:
        return Chains[0] - 2 + np.abs(2 - value(np.delete(Chains,0),Loops))
    elif Chains.size == 0:
        return Loops[0] - 4 + np.abs(4 - value(Chains,np.delete(Loops,0)))   
    else:
        return min(Loops[0] - 4 + np.abs(4 - value(Chains,np.delete(Loops,0))),Chains[0] - 2 + np.abs(2 - value(np.delete(Chains,0),Loops)))
    


def value_comp(Chains,Loops):
    np.sort(Chains)
    np.sort(Loops)
    return value(Chains,Loops)

def rand_chains():
    length = np.random.randint(1,10)
    return np.random.randint(3,10,length)

def rand_loops():
    length = np.random.randint(1,20)
    return 2*np.random.randint(2,6,length)

def test():
    Chains = rand_chains()
    Loops = rand_loops()
    print('Chains = ',Chains)
    print('Loops = ' ,Loops)
    return value_comp(Chains,Loops)