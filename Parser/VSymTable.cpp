// -*- C++ -*-
//*************************************************************************
//
// Copyright 2009-2013 by Wilson Snyder.  This program is free software;
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
/// Code available from: http://www.veripool.org/verilog-perl
///
//*************************************************************************
//
// Verilog Name spaces:
//	Namespace	Under		Holds
//	(*attributes*)	objects		Not implemented
//	`textmacros	comp-unit	Preproc handles
//	.ports/inout	module/cell	ports
//	packages	Global		package
//	definitions	comp-unit	Non-nested (macro)module, primitive, program, interface
//	comp-unit	comp-unit	Func, task, param, events, nets, vars, types
//	module		(macro)module,primitive,program,interface,package
//					module, intf, program,
//					blocks, func, task, inst, param, events,
//					vars, nets, types
//	block		blocks(begin/fork), specify, func, task
//					blocks, specify, func, task, inst*, param, events,
//					vars, nets*, types
//					(*IEEE doesn't list but can be under generate blocks)
//
//	Testcase:  "generate if (1) begin wire b; ..." proves b is local.
//
// Turning this on its head:
//
//	Object				   Namespace	Under
//	ports/inouts			   .ports	module/cell
//
//	package				   packages	comp-unit
//
//	module, program, interface	   definitions	comp-unit
//	[primitive(defs)]		OR module	module,primitive,program,interface,package
//
//	func, task, param, events,	   comp-unit	comp-unit
//	vars, nets, types, [blocks]	   module	module,primitive,program,interface,package
//	[inst], [[specify]]		OR block	blocks(begin/fork), specify, func, task
//
//	[...] indicates can only be under one of the lower name spaces, but won't
//	matter if the others are searched since the grammar won't create the
//	conflicting case.
//
//	Since packages can't be declared under modules, and modules under
//	blocks.  we can just have one hierarchical namespace that combines
//	comp-unit, module and block.
//*************************************************************************


#include "VSymTable.h"
#include <cassert>
#include <iostream>

/* Perl */
extern "C" {
# include "EXTERN.h"
# include "perl.h"
# include "XSUB.h"
}

//######################################################################
// VAstEnt
//
// A symtable is simply a hash(HV) by name of the object
// Under each hash entry (HE) is an array (AV)
// Under each array (AV) is an [SV with type, SV with HV of lower symtab]

#if 0
# define DBG_UINFO(z,msg) {printf("%s:%d: ", __FILE__,__LINE__); cout << msg; }
#else
# define DBG_UINFO(z,msg)
#endif

//######################################################################
// VSymStack

VSymStack::VSymStack(VFileLine* fl, struct av* symp) {
    assert(symp);
    ((VAstEnt*)(symp))->initNetlist(fl);
    pushScope((VAstEnt*)(symp));
}

//######################################################################
// Self test

class VFileLineTest : public VFileLine {
public:
    VFileLineTest(int called_only_for_default) : VFileLine(called_only_for_default) {}
    virtual ~VFileLineTest() { }
    virtual VFileLine* create(const string& filename, int lineno) { return new VFileLineTest(true); }
    virtual void error(const string& msg) { cout << msg; }
};

void VSymStack::selftest() {
    // GCC 3.3.5 requires this temporary string, so can't be a one liner
    { string max = VAstType(VAstType::_MAX).ascii(); assert(max == "_MAX"); } // Else probably missing word in ascii()
    //
    VFileLineTest flt(1);  // GCC 3.3.5 requires temporary
    VFileLine* fl = flt.create(__FILE__,__LINE__);

    AV* topavp = newAV();
    VSymStack stack (fl, topavp);
    //
    DBG_UINFO(9,"=============\n");
    assert(stack.objofUpward() == "netlist");
    assert(stack.findTypeUpward("missing") == VAstType::NOT_FOUND);

    DBG_UINFO(9,"=============\n");
    stack.pushScope(stack.findInsert(VAstType::PACKAGE, "top"));
    {
	assert(stack.objofUpward() == "package");
	assert(stack.findTypeUpward("top") == VAstType::PACKAGE);

	stack.findInsert(VAstType::TYPE, "a");

	DBG_UINFO(9,"=============\n");
	stack.pushScope(stack.findInsert(VAstType::MODULE, "lower"));
	{
	    assert(stack.findTypeUpward("lower") == VAstType::MODULE);  // IE ../lower exists.

	    DBG_UINFO(9,"=============\n");
	    stack.pushScope(stack.findInsert(VAstType::FORK, "fork"));
	    {
		assert(stack.findTypeUpward("lower") == VAstType::MODULE);  // Ignores the fork
	    }
	    stack.popScope(fl);

	    DBG_UINFO(9,"=============\n");
	    stack.pushScope(stack.findInsert(VAstType::CLASS, "a"));  // Hides upper a
	    {
		assert(stack.objofUpward() == "class");
		assert(stack.findTypeUpward("a") == VAstType::CLASS);
		assert(stack.findTypeUpward("top") == VAstType::PACKAGE);
	    }
	    stack.popScope(fl);

	    DBG_UINFO(9,"=============\n");
	    assert(stack.objofUpward() == "module");
	    assert(stack.findTypeUpward("a") == VAstType::CLASS);
	    assert(stack.findTypeUpward("top") == VAstType::PACKAGE);
	}
	stack.popScope(fl);

	DBG_UINFO(9,"=============\n");
	assert(stack.findTypeUpward("a") == VAstType::TYPE);
    }
    //
    av_undef(topavp); topavp=NULL;
};

#undef DBG_UINFO
