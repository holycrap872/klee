//===-- Assignment.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_UTIL_ASSIGNMENT_H
#define KLEE_UTIL_ASSIGNMENT_H

#include <map>

#include "klee/util/ExprEvaluator.h"
#include "klee/util/IndependenceAnalysis.h"

// FIXME: Rename?

namespace klee {
  class Array;

  class Assignment {
  public:
    typedef std::map<const Array*, std::vector<unsigned char> > bindings_ty;

    bool allowFreeValues;
    bindings_ty bindings;
    
  public:
    Assignment(bool _allowFreeValues=false) 
      : allowFreeValues(_allowFreeValues) {}
    Assignment(const std::vector<const Array*> &objects,
               std::vector< std::vector<unsigned char> > &values,
               bool _allowFreeValues=false) 
      : allowFreeValues(_allowFreeValues){
      std::vector< std::vector<unsigned char> >::iterator valIt = 
        values.begin();
      for (std::vector<const Array*>::const_iterator it = objects.begin(),
             ie = objects.end(); it != ie; ++it) {
        const Array *os = *it;
        std::vector<unsigned char> &arr = *valIt;
        bindings.insert(std::make_pair(os, arr));
        ++valIt;
      }
    }
    
    // Overwrites an existing solution with selected (via the ies) parts of
    // a new solution.
    Assignment(const Assignment &existing,
               const Assignment &overwriting,
               const IndependentElementSet &ies,
               bool _allowFreeValues=false)
      : allowFreeValues(_allowFreeValues){
      //Fill the new assignment with all of the existing values
      for (bindings_ty::const_iterator it = existing.bindings.begin();
           it != existing.bindings.end(); it ++){
        const Array * array = it->first;
        std::vector<unsigned char> answers = it -> second;
        this->bindings.insert(std::make_pair(array, answers));
      }
      // Go through the new, overwriting answer's array's.
      for (std::map<const Array*,
           ::DenseSet<unsigned> >::const_iterator it2 = ies.elements.begin();
           it2 != ies.elements.end(); it2 ++){
        const Array * array = it2 -> first;  //the array we're working with
        bindings_ty::const_iterator overWriteITE = overwriting.bindings.find(array);
        assert(overWriteITE!=bindings.end() && "this would mean that the SMT solver"
               " didn't return a full answer");
        std::vector<unsigned char> newAnswers = overWriteITE->second;
        //above is equivalent to "newAnswers = overwriting.bindings[array]"
        if (this->bindings.count(array)){
          // If there is a colliding solution, we need to carefully go through
          // and only replace the elements of the answer that are in the factor
          bindings_ty::const_iterator existingWriteITE = bindings.find(array);
          assert(existingWriteITE!=bindings.end());
          std::vector<unsigned char> oldAnswers = existingWriteITE->second;
          this->bindings.erase(array);
          // above is equivalent to "oldAnswers = bindings[array]"

          ::DenseSet<unsigned> ds = it2 -> second;
          for (std::set<unsigned>::const_iterator it2 = ds.begin(); it2 != ds.end(); it2++){
            unsigned index = * it2;
            oldAnswers[index] = newAnswers[index];
          }
          this->bindings.insert(std::make_pair(array, oldAnswers));
        }else{
          // If there is no colliding solution, we can just through the answer
          // of new solution into the answer without fear of overwriting any
          // old useful information.  On second through, this seems highly unlikely
          // since previous solver, (think independence solver) would have caught
          // this case.
          this->bindings.insert(std::make_pair(array, newAnswers));
        }
      }
    }

    ref<Expr> evaluate(const Array *mo, unsigned index) const;
    ref<Expr> evaluate(ref<Expr> e);

    template<typename InputIterator>
    bool satisfies(InputIterator begin, InputIterator end);
  };
  
  class AssignmentEvaluator : public ExprEvaluator {
    const Assignment &a;

  protected:
    ref<Expr> getInitialValue(const Array &mo, unsigned index) {
      return a.evaluate(&mo, index);
    }
    
  public:
    AssignmentEvaluator(const Assignment &_a) : a(_a) {}    
  };

  /***/

  inline ref<Expr> Assignment::evaluate(const Array *array, 
                                        unsigned index) const {
    assert(array);
    bindings_ty::const_iterator it = bindings.find(array);
    if (it!=bindings.end() && index<it->second.size()) {
      return ConstantExpr::alloc(it->second[index], array->getRange());
    } else {
      if (allowFreeValues) {
        return ReadExpr::create(UpdateList(array, 0), 
                                ConstantExpr::alloc(index, array->getDomain()));
      } else {
        return ConstantExpr::alloc(0, array->getRange());
      }
    }
  }

  inline ref<Expr> Assignment::evaluate(ref<Expr> e) { 
    AssignmentEvaluator v(*this);
    return v.visit(e); 
  }

  template<typename InputIterator>
  inline bool Assignment::satisfies(InputIterator begin, InputIterator end) {
    AssignmentEvaluator v(*this);
    for (; begin!=end; ++begin)
      if (!v.visit(*begin)->isTrue())
        return false;
    return true;
  }
}

#endif
