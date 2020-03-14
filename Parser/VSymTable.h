// -*- C++ -*-
//*************************************************************************
//
// Copyright 2009-2020 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the
// GNU Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Parse: Symbol table accessing
///
/// Authors: Wilson Snyder
///
/// Code available from: https://www.veripool.org/verilog-perl
///
//*************************************************************************

#ifndef _VSYMTABLE_H_
#define _VSYMTABLE_H_ 1

#include "VFileLine.h"
#include "VAst.h"
#include <vector>
#include <cassert>
using namespace std;

//######################################################################
// List of symbol tables

class VSymStack {
    typedef vector<VAstEnt*>	SymStack;

    SymStack		m_sympStack;	// Stack of symbol tables
    VAstEnt*		m_currentSymp;	// Current symbol table

public:
    // CONSTRUCTORS
    VSymStack(VFileLine* fl, struct av* symp);	// Pass in top-level symbol table array
    ~VSymStack() {}

    // ACCESSORS
    VAstEnt* currentSymp() const { return m_currentSymp; }
    VAstEnt* netlistSymp() const { return m_sympStack.front(); }

    // METHODS
    /// Insert a new entry, and return the new entry
    VAstEnt* replaceInsert(VAstType type, const string& name) {
	return m_currentSymp->replaceInsert(type,name);
    }
    /// Insert an entry if it doesn't exist
    VAstEnt* findInsert(VAstType type, const string& name) {
	return m_currentSymp->findInsert(type,name);
    }

    /// Return type of current lookup
    VAstType curType() { return m_currentSymp->type(); }

    void showUpward() {
	cout<<"SymTable Stack:\n";
	for (SymStack::reverse_iterator it=m_sympStack.rbegin(); it!=m_sympStack.rend(); ++it) {
	    VAstEnt* symp = *it;
	    cout<<"\t"<<symp->ascii()<<endl;
	}
	cout<<"SymTable Parents of current:\n";
	for (VAstEnt* symp=currentSymp(); symp; symp=symp->parentp()) {
	    cout<<"\t"<<symp->ascii()<<endl;
	}
    }

    /// Lookup the given string as an identifier, return type of the id
    // This recurses upwards if not found; for flat lookup use symp->findSym
    VAstEnt* findEntUpward(const string& name) {
	for (VAstEnt* symp=currentSymp(); symp; symp=symp->parentp()) {
	    if (VAstEnt* subp = symp->findSym(name)) {
		return subp;
	    }
	}
	return NULL;
    }
    VAstType findTypeUpward(const string& name) {
	if (VAstEnt* subp = findEntUpward(name)) {
	    return subp->type();
	} else {
	    return VAstType::NOT_FOUND;
	}
    }

    /// Return what this object is a member of, ignoring blocks
    string objofUpward() {
	for (VAstEnt* symp=currentSymp(); symp; symp=symp->parentp()) {
	    if (!symp->typeIgnoreObjof()) {
		return symp->type().ascii();
	    }
	}
	assert(0);  // Should have been a NETLIST if nothing else
	return "";  // Asserts maybe NOPed
    }

    /// Push current scope down to a new scope
    void pushScope(VAstEnt* symp) {
	m_sympStack.push_back(symp);
	m_currentSymp = symp;
    }

    /// Pop current scope up to a previous scope
    void popScope(VFileLine* fl) {
	m_sympStack.pop_back();
	// Must always have one remaining - it's globals.  Thus this is after the pop.
	if (m_sympStack.empty()) { fl->error("symbol stack underflow"); return; }
	m_currentSymp = m_sympStack.back();
    }

    /// Import from package::id_or_star to this
    void import(VFileLine* fl, const string& pkg, const string& id_or_star) {
	import(fl, pkg, findEntUpward(pkg), id_or_star);
    }
    void import(VFileLine* fl, const string& pkg, VAstEnt* entp, const string& id_or_star) {
	if (!entp) {  // Internal problem, because we earlier found pkg to label it an ID__aPACKAGE
	    fl->error("Internal: Import package not found: "+pkg);
	    return;
	}
	m_currentSymp->import(entp, id_or_star);
    }

    static void selftest();
};

#endif // guard
