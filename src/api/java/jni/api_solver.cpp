/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include "api_solver.h"

#include <cvc5/cvc5.h>

using namespace cvc5;

ApiSolver::ApiSolver(TermManager& tm) : Solver(tm) {}

jweak ApiSolver::addWeakGlobalReference(JNIEnv* env, jobject object)
{
  jweak reference = env->NewWeakGlobalRef(object);
  d_weakGlobalReferences.push_back(reference);
  return reference;
}

void ApiSolver::deletePointers(JNIEnv* env)
{
  for (jweak ref : d_weakGlobalReferences)
  {
    env->DeleteWeakGlobalRef(ref);
  }
  d_weakGlobalReferences.clear();
}
