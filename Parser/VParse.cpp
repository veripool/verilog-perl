// -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2018 by Wilson Snyder.  This program is free software;
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
/// \brief Verilog::Parse: Internal implementation of default preprocessor
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.org/verilog-perl
///
//*************************************************************************

#include <cstdio>
#include <cstring>
#include <fstream>
#include <stack>
#include <vector>
#include <map>
#include <deque>
#include <cassert>

#include "VParse.h"
#include "VParseLex.h"
#include "VParseGrammar.h"
#include "VSymTable.h"

VParseGrammar*	VParseGrammar::s_grammarp = NULL;

//*************************************************************************

VParse::VParse(VFileLine* filelinep, av* symsp,
	       bool sigParser, bool useUnreadbackFlag, bool useProtected, bool usePinselects)
    : m_syms(filelinep, symsp)
{
    m_inFilelinep = filelinep;
    m_sigParser = sigParser;
    m_useUnreadback = useUnreadbackFlag;
    m_useProtected = useProtected;
    m_usePinselects = usePinselects;
    m_debug = 0;
    m_lexp = new VParseLex(this);
    m_grammarp = new VParseGrammar(this);
    m_eof = false;
    m_anonNum = 0;
    m_symTableNextId = NULL;
    m_callbackMasterEna = true;
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
    // But, don't buffer too large a chunk, as it we need to peel off up to 8KB chunks from it
    const size_t max_chunk = 8191; // Flex uses 8KB chunks, so if slightly less, we won't have to move data
    size_t pos = 0;
    while (pos < text.length()) {
	size_t chunk = text.length() - pos;
	if (chunk > max_chunk) chunk = max_chunk;
	m_buffers.push_back(string(text.data()+pos, chunk));
	pos += chunk;
    }
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
    endparseCb(inFilelinep(),"");
    if (debug()) { cout<<"VParse::setEof: DONE\n"; }
}

void VParse::fakeBison() {
    // Verilog::Parser and we don't care about the syntax, so just Lex.
    VParseBisonYYSType yylval;
    while (int tok = lexToBison(&yylval)) {
	if (tok) {} // Prevent unused on some GCCs
    }
}

int VParse::lexToBison(VParseBisonYYSType* yylvalp) {
    return m_lexp->lexToBison(yylvalp);
}

size_t VParse::inputToLex(char* buf, size_t max_size) {
    size_t got = 0;
    while (got < max_size	// Haven't got enough
	   && !m_buffers.empty()) {	// And something buffered
	string front = m_buffers.front(); m_buffers.pop_front();
	size_t len = front.length();
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
