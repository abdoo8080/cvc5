/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A context-dependent object.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__CONTEXT__CDO_H
#define CVC5__CONTEXT__CDO_H

#include "context/context.h"

namespace cvc5::context {

/**
 * Most basic template for context-dependent objects.  Simply makes a copy
 * (using the copy constructor) of class T when saving, and copies it back
 * (using operator=) during restore.
 */
template <class T>
class CDO : public ContextObj {

  /**
   * The data of type T being stored in this context-dependent object.
   */
  T d_data;

protected:

  /**
   * Copy constructor - it's private to ensure it is only used by save().
   * Basic CDO objects, cannot be copied-they have to be unique.
   */
  CDO(const CDO<T>& cdo) : ContextObj(cdo), d_data(cdo.d_data) {}

  /**
   * operator= for CDO is private to ensure CDO object is not copied.
   */
  CDO<T>& operator=(const CDO<T>& cdo) = delete;

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current data to a copy using the copy constructor.  Memory is allocated
   * using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) override
  {
    return new (pCMM) CDO<T>(*this);
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply copies the
   * saved data back from the saved copy using operator= for T.
   */
  void restore(ContextObj* pContextObj) override
  {
    CDO<T>* p = static_cast<CDO<T>*>(pContextObj);
    d_data = p->d_data;
    // Explicitly call destructor as it will not otherwise get called.
    p->d_data.~T();
  }

public:

  /**
   * Main constructor - uses default constructor for T to create the initial
   * value of d_data.
   */
  CDO(Context* context) :
    ContextObj(context),
    d_data(T()) {
  }

  /**
   * Constructor from object of type T.  Creates a ContextObj and sets the data
   * to the given data value.  Note that this value is only valid in the
   * current Scope.  If the Scope is popped, the value will revert to whatever
   * is assigned by the default constructor for T
   */
  CDO(Context* context, const T& data) :
    ContextObj(context),
    d_data(T()) {
    makeCurrent();
    d_data = data;
  }

  /**
   * Destructor - call destroy() method
   */
  ~CDO() { destroy(); }

  /**
   * Set the data in the CDO.  First call makeCurrent.
   */
  void set(const T& data) {
    makeCurrent();
    d_data = data;
  }

  /**
   * Get the current data from the CDO.  Read-only.
   */
  const T& get() const { return d_data; }

  /**
   * For convenience, define operator T() to be the same as get().
   */
  operator T() { return get(); }

  /**
   * For convenience, define operator const T() to be the same as get().
   */
  operator const T() const { return get(); }

  /**
   * For convenience, define operator= that takes an object of type T.
   */
  CDO<T>& operator=(const T& data) {
    set(data);
    return *this;
  }

};/* class CDO */

}  // namespace cvc5::context

#endif /* CVC5__CONTEXT__CDO_H */
