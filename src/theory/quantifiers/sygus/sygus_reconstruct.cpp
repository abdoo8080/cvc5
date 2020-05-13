/*********************                                                        */
/*! \file sygus_reconstruct.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for reconstruct
 **
 **/
#include "theory/quantifiers/sygus/sygus_reconstruct.h"


using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusReconstruct::SygusReconstruct(TermDbSygus* tds) : d_tds(tds)
{
}

Node SygusReconstruct::reconstructSolution(Node sol,
                                          TypeNode stn,
                                          int& reconstructed,
                                          int enumLimit)
{
  Trace("sygus-rcons") << "SygusReconstruct::reconstructSolution: " << sol << std::endl;
  Trace("sygus-rcons") << "- target sygus type is " << stn << std::endl;
  Trace("sygus-rcons") << "- enumeration limit is " << enumLimit << std::endl;
  
  // TODO
  
  // we ran out of elements, return null
  reconstructed = -1;
  Warning() << CommandFailure(
      "Cannot get synth function: reconstruction to syntax failed.");
  // could return sol here, however, we choose to fail by returning null, since
  // it indicates a failure.
  return Node::null();
}

}
}
}
