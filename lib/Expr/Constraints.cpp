//===-- Constraints.cpp ---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Constraints.h"

#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprVisitor.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#else
#include "llvm/Function.h"
#endif
#include "llvm/Support/CommandLine.h"
#include "klee/Internal/Module/KModule.h"

#include <map>

using namespace klee;

namespace {
  llvm::cl::opt<bool>
  SimplifyInequalities("simplify-inequalities",
                           llvm::cl::desc("Check to see if inequalities reduce the range of a variable to the point it can be concretized (default=on"),
                           llvm::cl::init(true));
}

class ExprReplaceVisitor : public ExprVisitor {
private:
  ref<Expr> src, dst;

public:
  ExprReplaceVisitor(ref<Expr> _src, ref<Expr> _dst) : src(_src), dst(_dst) {}

  Action visitExpr(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }

  Action visitExprPost(const Expr &e) {
    if (e == *src.get()) {
      return Action::changeTo(dst);
    } else {
      return Action::doChildren();
    }
  }
};

class ExprReplaceVisitor2 : public ExprVisitor {
private:
  const std::map< ref<Expr>, ref<Expr> > &replacements;

public:
  ExprReplaceVisitor2(const std::map< ref<Expr>, ref<Expr> > &_replacements) 
    : ExprVisitor(true),
      replacements(_replacements) {}

  Action visitExprPost(const Expr &e) {
    std::map< ref<Expr>, ref<Expr> >::const_iterator it =
      replacements.find(ref<Expr>(const_cast<Expr*>(&e)));
    if (it!=replacements.end()) {
      return Action::changeTo(it->second);
    } else {
      return Action::doChildren();
    }
  }
};

bool ConstraintManager::rewriteConstraints(ExprVisitor &visitor) {
  ConstraintManager::constraints_ty old;
  bool changed = false;

  constraints.swap(old);
  for (ConstraintManager::constraints_ty::iterator 
         it = old.begin(), ie = old.end(); it != ie; ++it) {
    ref<Expr> &ce = *it;
    ref<Expr> e = visitor.visit(ce);

    if (e!=ce) {
      addConstraintInternal(e); // enable further reductions
      changed = true;
    } else {
      constraints.push_back(ce);
    }
  }

  return changed;
}

void ConstraintManager::simplifyForValidConstraint(ref<Expr> e) {
  // XXX 
}

void insertInLeftBoundedMap (ref<Expr> key, ref<ConstantExpr> value,
                             std::map< ref<Expr>, ref<ConstantExpr> > &leftBounded) {
  if (leftBounded.count(key) == 0) {
    leftBounded.insert(std::make_pair(key, value));
  } else if (leftBounded[key]->compareContents(* value.get()) < 0) {
    leftBounded[key] = value;
  }
}

void insertInRightBoundedMap (ref<Expr> key, ref<ConstantExpr> value,
                             std::map< ref<Expr>, ref<ConstantExpr> > &rightBounded) {
  if (rightBounded.count(key) == 0) {
    rightBounded.insert(std::make_pair(key, value));
  } else if (rightBounded[key]->compareContents(* value.get()) > 0) {
    rightBounded[key] = value;
  }
}

// A better name for this function may be "removeRedundantInformationInE
// AlreadyContainedInTheConstraintManager", but that's clearly a little too
// long. This shows, however, that simplifyExpr is about using concrete
// information already in the ConstraintManager to remove bits that incoming
// constraints that are more general than what is already in the constraint
// list. An example would be e > 7 when e is already concretely determined
// to be 8. Basically, we are eliminating pieces of e that do not actually
// constrain the state any further.
ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e) const {
  if (isa<ConstantExpr>(e))
    return e;

  std::map< ref<Expr>, ref<Expr> > equalities;
  // The two "bound" maps are used to track the left and right bounds
  // that a variable's range could possibly be. Should the left and right
  // bounds be constrained to a single value, then we will be able to
  // concretize the variable leading to what is hopefully a useful
  // simplification.
  std::map< ref<Expr>, ref<ConstantExpr> > leftBounded; //3 < x or 4 <= 6
  std::map< ref<Expr>, ref<ConstantExpr> > rightBounded; //x < 9 or x <= 17
  
  for (ConstraintManager::constraints_ty::const_iterator 
         it = constraints.begin(), ie = constraints.end(); it != ie; ++it) {
    bool topFalse = false;
    ref<Expr> expr = *it;
    if (const EqExpr *ee = dyn_cast<EqExpr>(expr)) {
      if (isa<ConstantExpr>(ee->left)) {
        // There are two possibilities that can reach here.
        // 1) We have a simple expression with a constant != false on the left
        // side. An example would be something like (x==6). In this case, we
        // will have mined all the information possible from the constraint,
        // and, in the if/else below, we will continue on to the next constraint
        //
        // 2) We have an operation that has been negated. For example, this
        // would look like (= false (op x... y...) ). In this case, we will
        // examine the interior operation to see if we can get any information
        // out of it. Ones where we can get extra information are
        // op = {>, >=} x {signed, unsigned}. We cannot get extra information
        // from the (= false (= x... y...) ) since this is equivalent to !=
        // and is much more difficult to use. We use the if/else below to
        // "continue" on this case.
        equalities.insert(std::make_pair(ee->right,
                                         ee->left));
      } else {
        // This case is much less useful since we have an equality between two
        // complex operations. All we can can do is to add it to the equalities
        // list hoping for a complete match of "e" (i.e. duplicate). The
        // if/else below simply continues in this case
        equalities.insert(std::make_pair(expr,
                                         ConstantExpr::alloc(1, Expr::Bool)));
      }

      if (isa<ConstantExpr>(ee->left) && cast<ConstantExpr>(ee->left)->isFalse()
          && ee->right->getKind() != Expr::Eq) {
        // If the top level is false, it's possible the constraint is of the
        // form (false (> x... y...) ) which we can use.
        expr = ee->right;
        topFalse = true;
      } else {
        // Otherwise, we've gotten all the information possible out of it
        continue;
      }
    } else {
      equalities.insert(std::make_pair(expr,
                                       ConstantExpr::alloc(1, Expr::Bool)));
    }

    if (SimplifyInequalities && isa<CmpExpr>(expr)) {
      // Find inequalities that constrain a variable to a specific range. The hope
      // is to find two constraints such as (x > 5) and (x < 7) that force a
      // variable to become a concrete value (x = 6). This transformation to an
      // equality allows for further simplification. The one difficult is that we
      // must track whether the constraint had an upper level negative,
      // (= false (< 6 x) ) which would flip the inequality.
      const CmpExpr *ex = dyn_cast<CmpExpr>(expr);
      ref<Expr> left, right;
      Expr::Kind kind = expr->getKind();
      if (topFalse) {
        // If the top negated the type of expression (ex. (= false (9 < x))
        // actually means (x <= 9) then we need to change <= to < and < to <=
        // and flip the children. This maintains the canonical form used
        // throughout klee
        if (kind == Expr::Ult) {
          kind = Expr::Ule;
        } else if (kind == Expr::Ule) {
          kind = Expr::Ult;
        } else if (kind == Expr::Slt) {
          kind = Expr::Sle;
        } else if (kind == Expr::Sle) {
          kind = Expr::Slt;
        } else {
          assert(false && "Should be in Klee canonical form and should have all "
                 "equality expressions filtered function calling this one");
        }
        left = ex->right;
        right = ex->left;
      }else{
        left = ex->left;
        right = ex->right;
      }
      ref<ConstantExpr> constantValue = 0;
      if (kind == Expr::Ult || kind == Expr::Slt) {
        if (isa<ConstantExpr>(right)) {
          // ex. (x < 10). Another way of saying this is x <= 0. We therefore
          // subtract 1 to the left hand constant in order to have a value that is
          // easier to work with
          ref<ConstantExpr> oneTooBig = dyn_cast<ConstantExpr>(right);
          constantValue = oneTooBig->Sub(ConstantExpr::alloc(1,oneTooBig->getWidth()));
          if (kind == Expr::Slt &&
              oneTooBig->getAPValue().slt(constantValue->getAPValue())) {
            assert(false && "Overflow should not happen in this instance");
          } else if (kind == Expr::Ult &&
                     oneTooBig->getAPValue().ult(constantValue->getAPValue())) {
            assert(false && "Overflow should not happen in this instance");
          }
          insertInRightBoundedMap(left, constantValue, rightBounded);
        } else if (isa<ConstantExpr>(left)) {
          // ex. (9 < x). Another way of saying this is 10 <= x. We therefore
          // add 1 to the left hand constant in order to have a value that is
          // easier to work with
          ref<ConstantExpr> oneTooSmall = dyn_cast<ConstantExpr>(left);
          constantValue = oneTooSmall->Add( ConstantExpr::alloc(1,oneTooSmall->getWidth()));
          if (kind == Expr::Slt &&
              constantValue->getAPValue().slt(oneTooSmall->getAPValue())) {
            assert(false && "Overflow should not happen in this instance");
          } else if (kind == Expr::Ult &&
                     constantValue->getAPValue().ult(oneTooSmall->getAPValue())) {
            assert(false && "Overflow should not happen in this instance");
          }
          insertInLeftBoundedMap(right, constantValue, leftBounded);
        }
      } else if (kind == Expr::Ule || kind  == Expr::Sle) {
        if (isa<ConstantExpr>(right)) {
          // x <=10
          constantValue = dyn_cast<ConstantExpr>(right);
          insertInRightBoundedMap(left, constantValue, rightBounded);
        } else if (isa<ConstantExpr>(left)) {
          // 10 <=x
          constantValue = dyn_cast<ConstantExpr>(left);
          insertInLeftBoundedMap(right, constantValue, leftBounded);
        }
      } else {
        assert(false && "Should be in Klee canonical form and should have all "
               "equality expressions filtered function calling this one");
      }
    }
  }

  // Now we check to see whether there are any variables that are constrained
  // on both the left and right side s.t. that can only be a single value.  If
  // this happens, then we can add the concretized value to the equalities map
  // so the incoming expression "e" can, hopefully, be simplified further.
  for (std::map<ref<Expr>, ref<ConstantExpr> >::iterator it = leftBounded.begin();
       it != leftBounded.end(); it++) {
    ref<Expr> key = it->first;
    // If the key has a left and right bound, and they're the same, then
    // key must be a single value
    if (rightBounded.count(key) && leftBounded[key]->
        compareContents(*rightBounded[key]) == 0) {
      equalities.insert(std::make_pair(key, leftBounded[key]));
    }
  }
  return ExprReplaceVisitor2(equalities).visit(e);
}

void ConstraintManager::addConstraintInternal(ref<Expr> e) {
  // rewrite any known equalities 

  // XXX should profile the effects of this and the overhead.
  // traversing the constraints looking for equalities is hardly the
  // slowest thing we do, but it is probably nicer to have a
  // ConstraintSet ADT which efficiently remembers obvious patterns
  // (byte-constant comparison).

  switch (e->getKind()) {
  case Expr::Constant:
    assert(cast<ConstantExpr>(e)->isTrue() && 
           "attempt to add invalid (false) constraint");
    break;
    
    // split to enable finer grained independence and other optimizations
  case Expr::And: {
    BinaryExpr *be = cast<BinaryExpr>(e);
    addConstraintInternal(be->left);
    addConstraintInternal(be->right);
    break;
  }

  case Expr::Eq: {
    BinaryExpr *be = cast<BinaryExpr>(e);
    if (isa<ConstantExpr>(be->left)) {
      ExprReplaceVisitor visitor(be->right, be->left);
      rewriteConstraints(visitor);
    }
    constraints.push_back(e);
    break;
  }
    
  default:
    constraints.push_back(e);
    break;
  }
}

void ConstraintManager::addConstraint(ref<Expr> e) {
  e = simplifyExpr(e);
  addConstraintInternal(e);
}
