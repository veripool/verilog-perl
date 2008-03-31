// $Id$  -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2008 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Parse: Internal implementation of default preprocessor
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.com/verilog-perl
///
//*************************************************************************

#include <stdio.h>
#include <fstream>
#include <stack>
#include <vector>
#include <map>
#include <deque>
#include <assert.h>

#include "VParse.h"
#include "VParseLex.h"
#include "VParseGrammar.h"

//*************************************************************************

VParse::VParse(VFileLine* filelinep, bool sigParser, bool useUnreadbackFlag) {
    m_inFilelinep = filelinep;
    m_sigParser = sigParser;
    m_useUnreadback = useUnreadbackFlag;
    m_debug = 0;
    m_lexp = new VParseLex(this);
    m_grammarp = new VParseGrammar(this);
    m_eof = false;
}

VParse::~VParse() {
    if (m_lexp) {
	delete m_lexp;
	m_lexp = NULL;
    }
    if (m_grammarp) {
	delete m_grammarp;
	m_grammarp = NULL;
    }
}

void VParse::debug(int level) {
    m_debug = level;
    if (level>5) m_grammarp->debug(level);
    if (level>5) m_lexp->debug(level);
}

VFileLine* VParse::inFilelinep() const { return m_inFilelinep; }

bool VParse::inCellDefine() const { return m_lexp->m_inCellDefine; }

void VParse::language(const char* valuep) { m_lexp->language(valuep); }

void VParse::parse(const string& text) {
    if (debug()>=10) { cout<<"VParse::parse: '"<<text<<"'\n"; }
    // We can't process immediately because bison has no nice way of returning
    // to us when a complete token is recognized.
    // YYACCEPT is one possibility, but where to call it depends on the user's callbacks.
    // Instead, buffer until eof.
    m_buffers.push_back(text);
}

void VParse::setEof() {
    m_eof = true;
    if (debug()) { cout<<"VParse::setEof: for "<<(void*)(this)<<endl; }
    m_lexp->restart();
    if (sigParser()) {
	// Use the bison parser
	m_grammarp->parse();
    } else {
	fakeBison();
    }
    // End of parsing callback
    endparseCb(inFilelinep());
    if (debug()) { cout<<"VParse::setEof: DONE\n"; }
}

void VParse::fakeBison() {
    // Verilog::Parser and we don't care about the syntax, so just Lex.
    static const size_t chunk = 8192;
    VParseBisonYYSType yylval;
    char buffer[chunk+10];
    while (int tok = lexToBison(&yylval)) {
    }
}

int VParse::lexToBison(VParseBisonYYSType* yylvalp) {
    int tok = m_lexp->lexToken(yylvalp);
    if (debug()>=9) { cout<<"   lexToBison  TOKEN="<<tok<<" "<<VParseGrammar::tokenName(tok)<<endl; }
    return tok;
}

int VParse::inputToLex(char* buf, int max_size) {
    int got = 0;
    while (got < max_size	// Haven't got enough
	   && !m_buffers.empty()) {	// And something buffered
	string front = m_buffers.front(); m_buffers.pop_front();
	int len = front.length();
	if (len > (max_size-got)) {  // Front string too big
	    string remainder = front.substr(max_size-got);
	    front = front.substr(0, max_size-got);
	    m_buffers.push_front(remainder);  // Put back remainder for next time
	    len = (max_size-got);
	}
	strncpy(buf+got, front.c_str(), len);
	got += len;
    }
    if (debug()>=9) {
	string out = string(buf,got);
	cout<<"   inputToLex  got="<<got<<" '"<<out<<"'"<<endl;
    }
    return got;
}
