/*
 * IndependenceAnalysis.h
 *
 *  Created on: Jan 29, 2015
 *      Author: ericrizzi
 */

#ifndef KLEE_UTIL_INDEPENDENCEANALYSIS_H_
#define KLEE_UTIL_INDEPENDENCEANALYSIS_H_

#include "klee/Solver.h"

#include "klee/Expr.h"
#include "klee/Constraints.h"
#include "klee/SolverImpl.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Common.h"

#include "klee/util/ExprUtil.h"

#include "llvm/Support/raw_ostream.h"
#include <list>
#include <map>
#include <ostream>
#include <vector>

using namespace klee;
using namespace llvm;

template<class T>
class DenseSet {
  typedef std::set<T> set_ty;
  set_ty s;

public:
  DenseSet() {}

  void add(T x) {
    s.insert(x);
  }
  void add(T start, T end) {
    for (; start<end; start++)
      s.insert(start);
  }

  // returns true iff set is changed by addition
  bool add(const DenseSet &b) {
    bool modified = false;
    for (typename set_ty::const_iterator it = b.s.begin(), ie = b.s.end();
         it != ie; ++it) {
      if (modified || !s.count(*it)) {
        modified = true;
        s.insert(*it);
      }
    }
    return modified;
  }

  bool intersects(const DenseSet &b) {
    for (typename set_ty::iterator it = s.begin(), ie = s.end();
         it != ie; ++it)
      if (b.s.count(*it))
        return true;
    return false;
  }

  std::set<unsigned>::iterator begin(){
	  return s.begin();
  }

  std::set<unsigned>::iterator end(){
  	  return s.end();
  }

  void print(llvm::raw_ostream &os) const {
    bool first = true;
    os << "{";
    for (typename set_ty::iterator it = s.begin(), ie = s.end();
         it != ie; ++it) {
      if (first) {
        first = false;
      } else {
        os << ",";
      }
      os << *it;
    }
    os << "}";
  }
};

template <class T>
inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ::DenseSet<T> &dis) {
  dis.print(os);
  return os;
}

/*
 * Keeps track of all reads in a single Constraint.  Maintains
 * a list of indices that are accessed in a concrete way.  This
 * can be superseded, however, by a set of arrays (wholeObjects)
 * that have been symbolically accessed.
 */
class IndependentElementSet {


public:
	typedef std::map<const Array*, ::DenseSet<unsigned> > elements_ty;

	elements_ty elements;                   //Represents individual elements of array accesses (arr[1])
	std::set<const Array*> wholeObjects;    //Represents symbolically accessed arrays (arr[x])
	std::vector<ref<Expr> > exprs;  		//All expressions that are associated with this factor

	IndependentElementSet();
	IndependentElementSet(ref<Expr> e);
	IndependentElementSet(const IndependentElementSet &ies);

	void print(llvm::raw_ostream &os) const;

	// more efficient when this is the smaller set
	bool intersects(const IndependentElementSet &b);

	/*
	 * Calculates whether two particular IndependentElementSets intersect
	 * by examining ONLY the indices of the arrays that they operate on.
	 * This means that IES's that do not share elements but do share
	 * whole objects are not considering intersecting.
	 *
	 * As a clarifying example, if IES1 = {arr[1]>6} and IES2 = {arr[1]<10},
	 * this function would consider IES1 and IES2 to be intersecting.
	 *
	 * If, instead IES1 = {arr[x]>6} and IES2 == {arr[1]<10}, this function
	 * would consider them independent.
	 *
	 * NOTE: As seen in the name, this is an unsafe operation and is only
	 * suitable for optimizations that account for this... Namely the
	 * GuessSplit optimization in the CexCachingSolver.
	 */
	bool intersectsUnsafe(const IndependentElementSet &b);

	// returns true iff set is changed by addition
	bool add(const IndependentElementSet &b);

	IndependentElementSet &operator=(const IndependentElementSet &ies) {
		elements = ies.elements;
		wholeObjects = ies.wholeObjects;

		for(unsigned i = 0; i < ies.exprs.size(); i ++){
			ref<Expr> expr = ies.exprs[i];
			exprs.push_back(expr);
		}

		return *this;
	}
};

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const IndependentElementSet &ies) {
	ies.print(os);
	return os;
}

IndependentElementSet getFreshFactor(const Query& query, std::vector<ref<Expr> > &result);

/*
 * Breaks down a constraint into all of it's individual pieces, returning a
 * list of IndependentElementSets or the independent factors.
 */
void getAllFactors(const Query& query, std::list<IndependentElementSet> * &factors );

/*
 * As detailed in IndependentElementSet::intersectsUnsafe(), this function only considers
 * the ref<Expr> of a query to intersect if they directly and explicitly reference the
 * same element of the array.  They do not consider ref<Expr> that share "wholeObjects"
 * to be intersecting.  As stated above, this is an unsafe funtion and should only be
 * use for optimizations that handle it correctly...Namely the GuessSplit optimization of
 * the CexCachingSolver.
 */
IndependentElementSet getFreshFactorUnsafe(const std::set<ref<Expr> > parentKey, const ref<Expr> &expr, std::vector<ref<Expr> > &result);

/*
 * Extracts which arrays are referenced from a particular independent set.  Examines both
 * the actual known array accesses arr[1] plus the undetermined accesses arr[x].
 */
void calculateArrays(const IndependentElementSet & ie, std::vector<const Array *> &returnVector);

#endif /* KLEE_UTIL_INDEPENDENCEANALYSIS_H_ */
