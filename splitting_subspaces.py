r"""
Demo code for splitting subspaces.

This code demonstrates the results of [PR2022]_.

EXAMPLES:

Computation of the similarity class type of a matrix over a finite field::

    sage: A = Matrix(GF(2),[[0,0,0,1],[0,0,1,0],[0,1,0,0],[0,0,0,0]])
    sage: similarity_class_type(A)
    [[1, [2]], [1, [2]]]

Computing the invariant subspace generating function::

    sage: invariant_subspace_generating_function(SimilarityClassType([[1, [2,2]]]))
    t^4 + (q + 1)*t^3 + (q^2 + q + 1)*t^2 + (q + 1)*t + 1
    sage: A = Matrix(GF(2),[(0, 1, 0, 0), (0, 1, 1, 1), (1, 0, 1, 0), (1, 1, 0, 0)])
    sage: invariant_subspace_generating_function(A)
    t^4 + 1

Computing the number of splitting subspaces::

    sage: splitting_subspaces(SimilarityClassType([[1, [2,2]]]))
    q^4
    sage: A = Matrix(GF(2),[(0, 1, 0, 0), (0, 1, 1, 1), (1, 0, 1, 0), (1, 1, 0, 0)])
    sage: splitting_subspaces(A)
    20.

NOTE::

    When the input is a matrix, the output is an integer. When the input is a
    similarity class type, the output is a polynomial in ``q``.


AUTHORS:

- AMRITANSHU PRASAD (2022-05-18)

REFERENCES:

.. [PR2022] \A. Prasad, S. Ram, Splitting subspaces and a finite field
            interpretation of the Touchard-Riordan Formula, 2022.

"""

# ****************************************************************************
#       Copyright (C) 2022 AMRITANSHU PRASAD
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from itertools import combinations
from sage.combinat.q_analogues import q_int
from sage.structure.element import is_Matrix
from sage.combinat.similarity_class_type import SimilarityClassType, PrimarySimilarityClassType
from sage.combinat.partition import Partition

def similarity_class_type(A):
    """
    Return the similarity class of type ``A``.

    INPUT:

    - ``A`` -- square matrix with entries in a finite field.
    """
    n = A.nrows()
    F = A.base_ring()
    R = PolynomialRing(F,'t')
    t = R.gen()
    S = (t-A).smith_form(transformation=False)
    L = reversed([S[i,i] for i in range(n) if S[i,i]])
    f = [dict(list(p.factor())) for p in L]
    d = dict()
    for p in f[0].keys():
        d[p] = Partition([h[p] for h in f if p in h.keys()])
    return SimilarityClassType([[p.degree(), d[p]] for p in d.keys()])

def invariant_subspace_generating_function(la,q=None,t=None):
    """
    Return the invariant subspace generating function of ``la``.

    INPUT:

    - ``la`` -- similarity class type, primary similarity class type, or a matrix over a finite field.

    EXAMPLES::

        sage: invariant_subspace_generating_function(SimilarityClassType([[1, [2,2]]]))
        t^4 + (q + 1)*t^3 + (q^2 + q + 1)*t^2 + (q + 1)*t + 1
        sage: A = Matrix(GF(2),[(0, 1, 0, 0), (0, 1, 1, 1), (1, 0, 1, 0), (1, 1, 0, 0)])
        sage: invariant_subspace_generating_function(A)
        t^4 + 1
        sage: invariant_subspace_generating_function([2,2])
        t^4 + (q + 1)*t^3 + (q^2 + q + 1)*t^2 + (q + 1)*t + 1
    """
    if q is None:
        q = PolynomialRing(QQ,'q').gen()
    S = q.parent()
    if t is None:
        t = PolynomialRing(S,'t').gen()
    R = t.parent()
    Rff = R.fraction_field()
    if is_Matrix(la):
        q = la.base_ring().cardinality()
        return invariant_subspace_generating_function(similarity_class_type(la),q=q,t=t)
    elif isinstance(la,SimilarityClassType):
        return prod(invariant_subspace_generating_function(p,q=q,t=t) for p in la)
    elif isinstance(la,PrimarySimilarityClassType):
        return invariant_subspace_generating_function(la.partition(),q=q,t=t).substitute(q=q**la.degree()).substitute(t=t**la.degree())
    if len(la)==0:
        return Rff(1)
    else:
        u = invariant_subspace_generating_function(la[1:])
        return R((t**(la[0]+1)*q**(sum(la[1:]))*u.substitute(t=t/q)-u.substitute(t=t*q))/(t-1))

def splitting_subspaces(tau,q=None,t=None):
    """
    Return the number of ``tau``-splitting subspaces.

    INPUT:

    - ``tau`` -- similarity class type, primary similarity class type, or a matrix over a finite field.

    EXAMPLES::

        sage: splitting_subspaces(SimilarityClassType([[1, [2,2]]]))
        q^4
        sage: A = Matrix(GF(2),[(0, 1, 0, 0), (0, 1, 1, 1), (1, 0, 1, 0), (1, 1, 0, 0)])
        sage: splitting_subspaces(A)
        20.
    """
    if q is None:
        q = PolynomialRing(QQ,'q').gen()
    S = q.parent()
    if t is None:
        t = PolynomialRing(S,'t').gen()
    R = t.parent()
    Rff = R.fraction_field()
    if is_Matrix(tau):
        q = tau.base_ring().cardinality()
        return splitting_subspaces(similarity_class_type(tau),q=q,t=t)
    if tau.size()%2 ==1:
        return 0
    m = tau.size()/2
    coeffs = invariant_subspace_generating_function(tau,q=q,t=t).list()
    return q**binomial(m,2)*sum((-1)**j*X*q**binomial(m-j+1,2) for j,X in enumerate(coeffs))
