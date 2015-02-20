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

#include <iostream>

using namespace klee;

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

ref<Expr> ConstraintManager::simplifyExpr(ref<Expr> e) const {
	if (isa<ConstantExpr>(e))
		return e;

	std::map< ref<Expr>, ref<Expr> > equalities;
	std::map< ref<Expr>, ref<ConstantExpr> > leftBounded; //3 < x or 4 <= 6
	std::map< ref<Expr>, ref<ConstantExpr> > rightBounded; //x < 9 or x <= 17

	for (ConstraintManager::constraints_ty::const_iterator
			it = constraints.begin(), ie = constraints.end(); it != ie; ++it) {

		bool topFalse = false;
		ref<Expr> expr = *it;
		if (expr->getKind() == Expr::Eq){
			const EqExpr *ee = dyn_cast<EqExpr>(expr);
			if(isa<ConstantExpr>(ee->left) && ! cast<ConstantExpr>(ee->left)->isFalse()) {
				//if we have a simple expression like x == 6, then add that to the equality pair
				equalities.insert(std::make_pair(ee->right, ee->left));
				continue;
			}else{
				expr = ee->right;
				topFalse = true;
			}
		}

		//Eric's stuff .... ugly :(
		std::map< ref<Expr>, ref<ConstantExpr> > * which = 0;
		ref<Expr> key = 0;
		ref<ConstantExpr> value = 0;

		switch (expr->getKind()){
		case Expr::Ult:{
			const UltExpr *ex = dyn_cast<UltExpr>(expr);
			if(isa<ConstantExpr>(ex->right)) {
				key = ex->left;
				if(topFalse){
					//x >=10
					value = dyn_cast<ConstantExpr>(ex->right);
					which = &leftBounded;
				}else{
					//x < 10
					ref<ConstantExpr> oneTooBig = dyn_cast<ConstantExpr>(ex->right);
					value = oneTooBig->Sub(ConstantExpr::alloc(1,oneTooBig->getWidth()));
					which = &rightBounded;
				}
			}else if(isa<ConstantExpr>(ex->left)){
				key = ex->right;
				if(topFalse){
					//9 >= x
					value = dyn_cast<ConstantExpr>(ex->left);
					which = &rightBounded;
				}else{
					//9 < x
					ref<ConstantExpr> oneTooSmall = dyn_cast<ConstantExpr>(ex->left);
					value = oneTooSmall->Add( ConstantExpr::alloc(1,oneTooSmall->getWidth()));
					which = & leftBounded;
				}
			}
		} break;

		case Expr::Slt :{
			const SltExpr *ex = dyn_cast<SltExpr>(expr);
			if(isa<ConstantExpr>(ex->right)) {
				key = ex->left;
				if(topFalse){
					//x >=10
					value = dyn_cast<ConstantExpr>(ex->right);
					which = &leftBounded;
				}else{
					//x < 10
					ref<ConstantExpr> oneTooBig = dyn_cast<ConstantExpr>(ex->right);
					value = oneTooBig->Sub(ConstantExpr::alloc(1,oneTooBig->getWidth()));
					which = &rightBounded;
				}
			}else if(isa<ConstantExpr>(ex->left)){
				key = ex->right;
				if(topFalse){
					//9 >= x
					value = dyn_cast<ConstantExpr>(ex->left);
					which = &rightBounded;
				}else{
					//9 < x
					ref<ConstantExpr> oneTooSmall = dyn_cast<ConstantExpr>(ex->left);
					value = oneTooSmall->Add( ConstantExpr::alloc(1,oneTooSmall->getWidth()));
					which = &leftBounded;
				}
			}
		} break;

		case Expr::Ule : {
			const UleExpr *ex = dyn_cast<UleExpr>(expr);
			if(isa<ConstantExpr>(ex->right)) {
				key = ex->left;
				if(topFalse){
					//x > 10
					ref<ConstantExpr> oneTooSmall = dyn_cast<ConstantExpr>(ex->right);
					value = oneTooSmall->Add(ConstantExpr::alloc(1,oneTooSmall->getWidth()));
					which = &leftBounded;
				}else{
					//x <=10
					value = dyn_cast<ConstantExpr>(ex->right);
					which = &rightBounded;
				}
			}else if(isa<ConstantExpr>(ex->left)){
				key = ex->right;
				if(topFalse){
					//10 > x
					ref<ConstantExpr> oneTooBig = dyn_cast<ConstantExpr>(ex->left);
					value = oneTooBig->Sub(ConstantExpr::alloc(1,oneTooBig->getWidth()));
					which = &rightBounded;
				}else{
					//10 <=x
					value = dyn_cast<ConstantExpr>(ex->left);
					which = &leftBounded;
				}
			}
		}break;

		case Expr::Sle : {
			const SleExpr *ex = dyn_cast<SleExpr>(expr);
			if(isa<ConstantExpr>(ex->right)) {
				key = ex->left;
				if(topFalse){
					//x > 10
					ref<ConstantExpr> oneTooSmall = dyn_cast<ConstantExpr>(ex->right);
					value = oneTooSmall->Add(ConstantExpr::alloc(1,oneTooSmall->getWidth()));
					which = &leftBounded;
				}else{
					//x <=10
					value = dyn_cast<ConstantExpr>(ex->right);
					which = &rightBounded;
				}
			}else if(isa<ConstantExpr>(ex->left)){
				key = ex->right;
				if(topFalse){
					//10 > x
					ref<ConstantExpr> oneTooBig = dyn_cast<ConstantExpr>(ex->left);
					value = oneTooBig->Sub(ConstantExpr::alloc(1,oneTooBig->getWidth()));
					which = &rightBounded;
				}else{
					//10 <=x
					value = dyn_cast<ConstantExpr>(ex->left);
					which = &leftBounded;
				}
			}
		}break;

		default: {

		} break;
		}

		equalities.insert(std::make_pair(*it, ConstantExpr::alloc(1, Expr::Bool)));

		if(which != 0){
			assert(value.get() != 0 && key.get() != 0);
			if(which->count(key) == 0){
				which->insert(std::make_pair(key, value));
			}else if(which == &leftBounded){
				if(leftBounded[key]->compareContents(* value.get()) < 0){
					leftBounded[key] = value;
				}
			}else{
				if(rightBounded[key]->compareContents(* value.get()) > 0){
					rightBounded[key] = value;
				}
			}
		}else{
			assert(key.get() == 0 && value.get() == 0);
		}
	}

	for(std::map<ref<Expr>, ref<ConstantExpr> >::iterator it = leftBounded.begin(); it != leftBounded.end(); it++){
		ref<Expr> key = it->first;
		if(rightBounded.count(key) && leftBounded[key]->compareContents(*rightBounded[key]) == 0){
			equalities.insert(std::make_pair(key, leftBounded[key]));
			std::cout << "We narrowed it down to a single concrete value\n";
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
