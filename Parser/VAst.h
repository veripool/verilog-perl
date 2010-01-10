// -*- C++ -*-
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder.  This program is free software;
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

#ifndef _VAST_H_
#define _VAST_H_ 1

#include <string>
#include <cstdlib>
#include <cassert>
using namespace std;

// We don't include perl.h as it gets upset when merged with bison
// code.  So just grab a minimal set.
struct av;
struct hv;

//######################################################################
// Enumeration that indicates what type of symbol is in the symbol tree.
// We may later change to use a different object for each type

class VAstType {
public:
    enum en {
	NOT_FOUND = 0,
	NETLIST = 1,	// Top of structure, created by Parser.pm:sub new{}
	ERROR = 2,	// Consistency error in internal tables
	UNKNOWN = 3,	// Things that need scope, but don't know type yet
	//
	BLOCK,
	CLASS,		// For yaID__CLASS
	CLOCKING,
	COVERGROUP,	// For yaID__COVERGROUP
	ENUM,
	FORK,
	FUNCTION,
	INTERFACE,
	MODPORT,
	MODULE,
	PACKAGE,	// For yaID__PACKAGE
	PROGRAM,
	PROPERTY,
	SEQUENCE,
	STRUCT,
	TASK,
	TYPE,		// For yaID__TYPE
	UNION,
	_MAX
    };
    enum en m_e;
    inline VAstType () {};
    inline VAstType (en _e) : m_e(_e) {};
    explicit inline VAstType (int _e) : m_e(static_cast<en>(_e)) {};
    operator en () const { return m_e; };
    const char* ascii() const {
	static const char* names[] = {
	"NOT_FOUND", "netlist", "error", "unknown",
	"block", "class", "clocking", "covergroup",
	"enum", "fork", "function", "interface",
	"modport", "module", "package", "program", "property",
	"sequence", "struct", "task", "type", "union",
	"_MAX"
	};
	return names[m_e];
    }
  };
  inline bool operator== (VAstType lhs, VAstType rhs) { return (lhs.m_e == rhs.m_e); }
  inline bool operator== (VAstType lhs, VAstType::en rhs) { return (lhs.m_e == rhs); }
  inline bool operator== (VAstType::en lhs, VAstType rhs) { return (lhs == rhs.m_e); }

//######################################################################
// Single symbol table

class VAstEnt {
private:
    // MEMBERS
    // NOT ALLOWED - this class really has this==AV*

    // STATIC MEMBERS
    static int s_debug;
public:
    static void debug(int flag) { s_debug=flag; }
    static int debug() { return s_debug; }

private:
    // CREATORS
    VAstEnt() { assert(0); }	// Not made by users, it's an AV*
    ~VAstEnt() { assert(0); }	// Not made by users, it's an AV*

    av* newAVEnt (VAstType type);
    static void initAVEnt (struct av* avp, VAstType type, struct av* parentp);

    // ACCESSORS
    inline struct av* castAVp() { return (struct av*)(this); }
    inline VAstEnt* avToSymEnt(struct av* avp) { return (VAstEnt*)(avp); }

    /// $self->[2]: For current entry, the hash of symbols under it
    struct hv* subhash();

    /// Insert into current table
    void insert(VAstEnt* newentp, const string& name);

public:
    // ACCESSORS

    /// $self->[0]: For current entry, the node type
    VAstType type();

    /// $self->[1]: For current entry, what node it is under or NULL if netlist
    VAstEnt* parentp();

    /// type() indicates we shouldn't report this as a containing object
    bool typeIgnoreObjof() { VAstType t=type(); return t==VAstType::BLOCK || t==VAstType::FORK; }

    /// Info on current node, for debug
    string ascii(const string& name="");

    // METHODS
    /// Return internal pointer for given name or null
    VAstEnt* findSym (const string& name);

    /// Insert into current table
    VAstEnt* insert(VAstType type, const string& name);

    /// Find or create a symbol entry under current entry
    VAstEnt* findNewTable (VAstType type, const string& name);

    /// Insert into current table from another imported package's table
    void import(VAstEnt* fromEntp, const string& id_or_star);

protected:
    friend class VSymStack;
    void initNetlist(VFileLine* fl);
};

#endif // guard
