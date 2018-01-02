#/* Verilog.xs -- Verilog Booter  -*- C++ -*-
#*********************************************************************
#*
#* DESCRIPTION: Verilog::Parser Perl XS interface
#*
#* Author: Wilson Snyder <wsnyder@wsnyder.org>
#*
#* Code available from: http://www.veripool.org/
#*
#*********************************************************************
#*
#* Copyright 2000-2018 by Wilson Snyder.  This program is free software;
#* you can redistribute it and/or modify it under the terms of either the GNU
#* Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
#*
#* This program is distributed in the hope that it will be useful,
#* but WITHOUT ANY WARRANTY; without even the implied warranty of
#* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#* GNU General Public License for more details.
#*
#* You should have received a copy of the Perl Artistic License
#* along with this module; see the file COPYING.  If not, see
#* www.cpan.org
#*
#***********************************************************************
#* Note with C++ XS libraries, the CLASS parameter is implied...
#***********************************************************************/

/* Mine: */
#include "VParse.h"
#include "VSymTable.h"
#include "VAst.h"
#include <cstring>
#include <deque>

/* Perl */
extern "C" {
# include "EXTERN.h"
# include "perl.h"
# include "XSUB.h"
}

#ifdef open
# undef open	/* Perl 64 bit on solaris has a nasty hack that redefines open */
#endif

// This is a global constant pointer initialized to its own address to
// produce a unique address to distinguish hashes (pointers to
// struct VParseHashElem) from the strings (character pointers) used by
// callbackgen in its variadic parameters for VParserXs::call().
static void *hasharray_param = &hasharray_param;

class VFileLineParseXs;

#//**********************************************************************
#// Parseressor derived classes, so we can override the callbacks to call perl.

class VParserXs : public VParse {
public:
    SV*		m_self;	// Class called from (the hash, not SV pointing to the hash)
    VFileLine*	m_cbFilelinep;	///< Last callback's starting point
    deque<VFileLineParseXs*> m_filelineps;

    // CALLBACKGEN_H_MEMBERS
    // CALLBACKGEN_GENERATED_BEGIN - GENERATED AUTOMATICALLY by callbackgen
    struct {  // Bit packed to help the cache
        bool m_useCb_attribute:1;
        bool m_useCb_class:1;
        bool m_useCb_comment:1;
        bool m_useCb_contassign:1;
        bool m_useCb_covergroup:1;
        bool m_useCb_defparam:1;
        bool m_useCb_endcell:1;
        bool m_useCb_endclass:1;
        bool m_useCb_endgroup:1;
        bool m_useCb_endinterface:1;
        bool m_useCb_endmodport:1;
        bool m_useCb_endmodule:1;
        bool m_useCb_endpackage:1;
        bool m_useCb_endparse:1;
        bool m_useCb_endprogram:1;
        bool m_useCb_endtaskfunc:1;
        bool m_useCb_function:1;
        bool m_useCb_import:1;
        bool m_useCb_instant:1;
        bool m_useCb_interface:1;
        bool m_useCb_keyword:1;
        bool m_useCb_modport:1;
        bool m_useCb_module:1;
        bool m_useCb_number:1;
        bool m_useCb_operator:1;
        bool m_useCb_package:1;
        bool m_useCb_parampin:1;
        bool m_useCb_pin:1;
        bool m_useCb_pinselects:1;
        bool m_useCb_port:1;
        bool m_useCb_preproc:1;
        bool m_useCb_program:1;
        bool m_useCb_string:1;
        bool m_useCb_symbol:1;
        bool m_useCb_sysfunc:1;
        bool m_useCb_task:1;
        bool m_useCb_var:1;
    };
    // CALLBACKGEN_GENERATED_END - GENERATED AUTOMATICALLY by callbackgen

    VFileLine* cbFilelinep() const { return m_cbFilelinep; }
    void cbFileline(VFileLine* filelinep) { m_cbFilelinep = filelinep; }

    VParserXs(VFileLine* filelinep, av* symsp,
	      bool sigparser, bool useUnreadback, bool useProtected, bool usePinselects)
	: VParse(filelinep, symsp, sigparser, useUnreadback, useProtected, usePinselects)
	, m_cbFilelinep(filelinep)
	{ set_cb_use(); }
    virtual ~VParserXs();

    // CALLBACKGEN_CB_USE
    // CALLBACKGEN_GENERATED_BEGIN - GENERATED AUTOMATICALLY by callbackgen
    void set_cb_use() {
       m_useCb_attribute = true;
       m_useCb_class = true;
       m_useCb_comment = true;
       m_useCb_contassign = true;
       m_useCb_covergroup = true;
       m_useCb_defparam = true;
       m_useCb_endcell = true;
       m_useCb_endclass = true;
       m_useCb_endgroup = true;
       m_useCb_endinterface = true;
       m_useCb_endmodport = true;
       m_useCb_endmodule = true;
       m_useCb_endpackage = true;
       m_useCb_endparse = true;
       m_useCb_endprogram = true;
       m_useCb_endtaskfunc = true;
       m_useCb_function = true;
       m_useCb_import = true;
       m_useCb_instant = true;
       m_useCb_interface = true;
       m_useCb_keyword = true;
       m_useCb_modport = true;
       m_useCb_module = true;
       m_useCb_number = true;
       m_useCb_operator = true;
       m_useCb_package = true;
       m_useCb_parampin = true;
       m_useCb_pin = true;
       m_useCb_pinselects = true;
       m_useCb_port = true;
       m_useCb_preproc = true;
       m_useCb_program = true;
       m_useCb_string = true;
       m_useCb_symbol = true;
       m_useCb_sysfunc = true;
       m_useCb_task = true;
       m_useCb_var = true;
   }
    // CALLBACKGEN_GENERATED_END - GENERATED AUTOMATICALLY by callbackgen
    // CALLBACKGEN_H_VIRTUAL
    // CALLBACKGEN_GENERATED_BEGIN - GENERATED AUTOMATICALLY by callbackgen
    // Verilog::Parser Callback methods
    virtual void attributeCb(VFileLine* fl, const string& text);
    virtual void commentCb(VFileLine* fl, const string& text);
    virtual void endparseCb(VFileLine* fl, const string& text);
    virtual void keywordCb(VFileLine* fl, const string& text);
    virtual void numberCb(VFileLine* fl, const string& text);
    virtual void operatorCb(VFileLine* fl, const string& text);
    virtual void preprocCb(VFileLine* fl, const string& text);
    virtual void stringCb(VFileLine* fl, const string& text);
    virtual void symbolCb(VFileLine* fl, const string& text);
    virtual void sysfuncCb(VFileLine* fl, const string& text);
    // Verilog::SigParser Callback methods
    virtual void classCb(VFileLine* fl, const string& kwd, const string& name, const string& virt);
    virtual void contassignCb(VFileLine* fl, const string& kwd, const string& lhs, const string& rhs);
    virtual void covergroupCb(VFileLine* fl, const string& kwd, const string& name);
    virtual void defparamCb(VFileLine* fl, const string& kwd, const string& lhs, const string& rhs);
    virtual void endcellCb(VFileLine* fl, const string& kwd);
    virtual void endclassCb(VFileLine* fl, const string& kwd);
    virtual void endgroupCb(VFileLine* fl, const string& kwd);
    virtual void endinterfaceCb(VFileLine* fl, const string& kwd);
    virtual void endmodportCb(VFileLine* fl, const string& kwd);
    virtual void endmoduleCb(VFileLine* fl, const string& kwd);
    virtual void endpackageCb(VFileLine* fl, const string& kwd);
    virtual void endprogramCb(VFileLine* fl, const string& kwd);
    virtual void endtaskfuncCb(VFileLine* fl, const string& kwd);
    virtual void functionCb(VFileLine* fl, const string& kwd, const string& name, const string& data_type);
    virtual void importCb(VFileLine* fl, const string& package, const string& id);
    virtual void instantCb(VFileLine* fl, const string& mod, const string& cell, const string& range);
    virtual void interfaceCb(VFileLine* fl, const string& kwd, const string& name);
    virtual void modportCb(VFileLine* fl, const string& kwd, const string& name);
    virtual void moduleCb(VFileLine* fl, const string& kwd, const string& name, bool, bool celldefine);
    virtual void packageCb(VFileLine* fl, const string& kwd, const string& name);
    virtual void parampinCb(VFileLine* fl, const string& name, const string& conn, int index);
    virtual void pinCb(VFileLine* fl, const string& name, const string& conn, int index);
    virtual void pinselectsCb(VFileLine* fl, const string& name, unsigned int arraycnt2, unsigned int elemcnt2, const VParseHashElem* conns2, int index);
    virtual void portCb(VFileLine* fl, const string& name, const string& objof, const string& direction, const string& data_type
	, const string& array, int index);
    virtual void programCb(VFileLine* fl, const string& kwd, const string& name);
    virtual void taskCb(VFileLine* fl, const string& kwd, const string& name);
    virtual void varCb(VFileLine* fl, const string& kwd, const string& name, const string& objof, const string& net
	, const string& data_type, const string& array, const string& value);
    // CALLBACKGEN_GENERATED_END - GENERATED AUTOMATICALLY by callbackgen

    void useCbEna(const char* name, bool flag);
    void call(string* rtnStrp, int params, const char* method, ...);
};

class VFileLineParseXs : public VFileLine {
    VParserXs*	m_vParserp;		// Parser handling the errors

public:
    VFileLineParseXs(VParserXs* pp) : VFileLine(true), m_vParserp(pp) { if (pp) pushFl(); }
    virtual ~VFileLineParseXs() { }
    virtual VFileLine* create(const string& filename, int lineno) {
	VFileLineParseXs* filelp = new VFileLineParseXs(m_vParserp);
	filelp->init(filename, lineno);
	return filelp;
    }
    virtual void error(const string& msg);	// Report a error at given location
    void setParser(VParserXs* pp) {
	m_vParserp=pp;
	pushFl(); // The very first construction used pp=NULL, as pp wasn't created yet so make it now
    }
    // Record the structure so we can delete it later
    void pushFl() { m_vParserp->m_filelineps.push_back(this); }
};

#//**********************************************************************
#// Overrides error handling virtual functions to invoke callbacks

void VFileLineParseXs::error(const string& msg) {
    static string holdmsg; holdmsg = msg;
    m_vParserp->cbFileline(this);
    // Call always, not just if callbacks enabled
    m_vParserp->call(NULL, 1,"error",holdmsg.c_str());
}

#//**********************************************************************
#// Overrides of virtual functions to invoke callbacks

#include "Parser_callbackgen.cpp"

#//**********************************************************************
#// VParserXs functions

VParserXs::~VParserXs() {
    for (deque<VFileLineParseXs*>::iterator it=m_filelineps.begin(); it!=m_filelineps.end(); ++it) {
	delete *it;
    }
}

#//**********************************************************************
#// General callback invoker

void VParserXs::call (
    string* rtnStrp,	/* If non-null, load return value here */
    int params,		/* Number of parameters */
    const char* method,	/* Name of method to call */
    ...)		/* Arguments to pass to method's @_ */
{
    // Call $perlself->method (passedparam1, parsedparam2)
    if (debug()) cout << "CALLBACK "<<method<<endl;
    va_list ap;
    va_start(ap, method);
    {
	dSP;				/* Initialize stack pointer */
	ENTER;				/* everything created after here */
	SAVETMPS;			/* ...is a temporary variable. */
	PUSHMARK(SP);			/* remember the stack pointer */
	SV* selfsv = newRV_inc(m_self);	/* $self-> */
	XPUSHs(sv_2mortal(selfsv));

	while (params--) {
	    char* textp = va_arg(ap, char *);
	    if (textp == hasharray_param) {
		// First hasharray param defines number of array elements
		unsigned int arrcnt = va_arg(ap, unsigned int);
		AV* av = newAV();
		av_extend(av, arrcnt);

		// Second hasharray param defines how many keys are within one hash
		unsigned int elemcnt = va_arg(ap, unsigned int);
		// Followed by the hash array pointer...
		const VParseHashElem* arrp = va_arg(ap, const VParseHashElem*);  // [arrcnt][elemcnt]
		for (unsigned int i = 0; i < arrcnt; i++) {
		    HV* hv = newHV();
		    const VParseHashElem* elemp = arrp + elemcnt*i;
		    for (unsigned int j = 0; j < elemcnt; j++) {
			if (!elemp[j].keyp)
			    continue;
			SV* sv;
			switch (elemp[j].val_type) {
			case VParseHashElem::ELEM_INT:
			    sv = newSViv(elemp[j].val_int);
			    break;
			case VParseHashElem::ELEM_STR:
			default:
			    sv = newSVpv(elemp[j].val_str.c_str(), 0);
			    break;
			}
			hv_store(hv, elemp[j].keyp, strlen(elemp[j].keyp), sv, 0);
		    }
		    av_store(av, i, newRV_noinc((SV*)hv));
		    elemp++;
		}
		XPUSHs(sv_2mortal(newRV_noinc((SV*)av)));
	    } else if (textp) {  // Non hasharray_param, so is text
		XPUSHs(sv_2mortal(newSVpv (textp, 0)));
	    } else {
		XPUSHs(&PL_sv_undef);
	    }
	}

	PUTBACK;			/* make local stack pointer global */

	if (rtnStrp) {
	    int rtnCount = perl_call_method ((char*)method, G_SCALAR);
	    SPAGAIN;			/* refresh stack pointer */
	    if (rtnCount > 0) {
		SV* sv = POPs;
		//printf("RTN %ld %d %s\n", SvTYPE(sv),SvTRUE(sv),SvPV_nolen(sv));
#ifdef SvPV_nolen	// Perl 5.6 and later
		*rtnStrp = SvPV_nolen(sv);
#else
		*rtnStrp = SvPV(sv,PL_na);
#endif
	    }
	    PUTBACK;
	} else {
	    perl_call_method ((char*)method, G_DISCARD | G_VOID);
	}

	FREETMPS;			/* free that return value */
	LEAVE;				/* ...and the XPUSHed "mortal" args.*/
    }
    va_end(ap);
}

#//**********************************************************************

MODULE = Verilog::Parser  PACKAGE = Verilog::Parser

#//**********************************************************************
#// self->_new (class, sigparser)

static VParserXs *
VParserXs::_new (SV* SELF, AV* symsp, bool sigparser, bool useUnreadback, bool useProtected, bool usePinselects)
PROTOTYPE: $$$$
CODE:
{
    if (CLASS) {}  /* Prevent unused warning */
    if (!SvROK(SELF)) { warn("${Package}::$func_name() -- SELF is not a hash reference"); }
    VFileLineParseXs* filelinep = new VFileLineParseXs(NULL/*ok,for initial*/);
    VParserXs* parserp = new VParserXs(filelinep, symsp, sigparser, useUnreadback, useProtected, usePinselects);
    filelinep->setParser(parserp);
    parserp->m_self = SvRV(SELF);
    RETVAL = parserp;
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->_DESTROY()

void
VParserXs::_DESTROY()
PROTOTYPE: $
CODE:
{
    delete THIS;
}

#//**********************************************************************
#// self->debug(level)

void
VParserXs::_debug (level)
int level
PROTOTYPE: $$
CODE:
{
    THIS->debug(level);
    VAstEnt::debug(level);
}

#//**********************************************************************
#// self->_callback_master_enable(flag)
#// Turn off callbacks during std:: parsing

void
VParserXs::_callback_master_enable (flag)
bool flag
PROTOTYPE: $$
CODE:
{
    THIS->callbackMasterEna(flag);
}

#//**********************************************************************
#// self->_use_cb(name,flag)
#// Turn off specified callback

void
VParserXs::_use_cb(const char* name, bool flag)
PROTOTYPE: $$$
CODE:
{
    THIS->useCbEna(name,flag);
}

#//**********************************************************************
#// self->eof()

void
VParserXs::eof ()
PROTOTYPE: $
CODE:
{
    THIS->setEof();
}
#//**********************************************************************
#// self->filename([setit])

SV*
VParserXs::filename (const char* flagp="")
PROTOTYPE: $;$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    if (items > 1) {
	THIS->inFileline(flagp, THIS->inFilelinep()->lineno());
	THIS->cbFileline(THIS->inFilelinep());
    }
    string ret = THIS->cbFilelinep()->filename();
    RETVAL = newSVpv(ret.c_str(), ret.length());
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->language()

void
VParserXs::language (valuep)
const char* valuep
PROTOTYPE: $$
CODE:
{
    if (items > 1) {
        THIS->language(valuep);
    }
}

#//**********************************************************************
#// self->lineno([setit])

int
VParserXs::lineno (int flag=0)
PROTOTYPE: $;$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    if (items > 1) {
	THIS->inFileline(THIS->inFilelinep()->filename(), flag);
	THIS->cbFileline(THIS->inFilelinep());
    }
    RETVAL = (THIS->cbFilelinep()->lineno());
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->parse()

void
VParserXs::parse (const char* textp)
PROTOTYPE: $$
CODE:
{
    THIS->parse(textp);
}

#//**********************************************************************
#// self->selftest()

void
VParserXs::selftest ()
PROTOTYPE: $
CODE:
{
    VSymStack::selftest();
    assert(VParse::isKeyword("wire",strlen("wire")));
    assert(!VParse::isKeyword("wire99",strlen("wide99")));
}

#//**********************************************************************
#// self->unreadback()

SV*
VParserXs::unreadback (const char* flagp="")
PROTOTYPE: $;$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    // Set RETVAL to a SV before we replace with the new value, and c_str may change
    string ret = THIS->unreadback();
    RETVAL = newSVpv(ret.c_str(), ret.length());
    if (items > 1) {
	THIS->unreadback(flagp);
    }
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->unreadbackCat()

void
VParserXs::unreadbackCat (SV* textsvp)
PROTOTYPE: $$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    STRLEN textlen;
    const char* textp = SvPV(textsvp, textlen);
    THIS->unreadbackCat(textp, textlen);
}
