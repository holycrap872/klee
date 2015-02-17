//===-- SolverStats.h -------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SOLVERSTATS_H
#define KLEE_SOLVERSTATS_H

#include "klee/Statistic.h"

namespace klee {
namespace stats {

  extern Statistic queries;
  extern Statistic queriesInvalid;
  extern Statistic queriesValid;

  extern Statistic independentTime;

  extern Statistic cacheHits;
  extern Statistic cacheMisses;
  extern Statistic cacheTime;

  extern Statistic cexCacheHits;
  extern Statistic cexCacheMisses;
  extern Statistic cexCacheTime;

  extern Statistic smtTime;

  extern Statistic queryConstructTime;
  extern Statistic queryConstructs;
  extern Statistic queryCounterexamples;
  
#ifdef DEBUG
  extern Statistic arrayHashTime;
#endif

}
}

#endif
