// -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2012 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Parse: Parseess verilog code
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.org/verilog-perl
///
//*************************************************************************

#ifndef _VPARSEGRAMMAR_H_
#define _VPARSEGRAMMAR_H_ 1

#include <string>
#include <map>
#include <deque>
#include <iostream>
using namespace std;
#include "VFileLine.h"
#include "VParse.h"
#include "VAst.h"

//============================================================================
// Container of things to put out later

struct VParseGPin {
    VFileLine* m_fl;
    string m_name;
    string m_conn;
    int m_number;
    VParseGPin(VFileLine* fl, const string& name, const string& conn, int number)
	: m_fl(fl), m_name(name), m_conn(conn), m_number(number) {}
};

//============================================================================
// We can't use bison's %union as the string type doesn't fit in a union.
// It's fine to use a struct though!

struct VParseBisonYYSType {
    string	str;
    VFileLine*	fl;
    VAstEnt*	scp;	// Symbol table scope for future lookups
};
#define YYSTYPE VParseBisonYYSType

//============================================================================

class VParseGrammar {
    static VParseGrammar*	s_grammarp;	///< Current THIS, bison() isn't class based
    VParse*	   m_parsep;
    //int debug() { return 9; }

public: // Only for VParseBison
    int		m_pinNum;		///< Pin number being parsed
    string	m_varDecl;
    string	m_varNet;
    string	m_varIO;
    string	m_varDType;
    string	m_varRange;

    string	m_cellMod;
    bool	m_cellParam;


    deque<VParseGPin> m_pinStack;

public: // But for internal use only
    static VParseGrammar* staticGrammarp() { return s_grammarp; }
    static VParse* staticParsep() { return staticGrammarp()->m_parsep; }

    static void bisonError(const char* text) {
	staticParsep()->error(text);
    }
    //static VFileLine* fileline() { return s_grammarp->m_fileline; }

public:
    // CREATORS
    VParseGrammar(VParse* parsep) : m_parsep(parsep) {
	s_grammarp = this;
	m_pinNum = 0;
	m_cellParam = false;
    }
    ~VParseGrammar() {
	s_grammarp = NULL;
    }

    // ACCESSORS
    void debug(int level);
    int pinNum() const { return m_pinNum; }
    void pinNum(int flag) { m_pinNum = flag; }
    void pinNumInc() { m_pinNum++; }

    // METHODS
    int parse();  // See VParseBison.y
    static const char* tokenName(int token);
};

#endif // Guard
