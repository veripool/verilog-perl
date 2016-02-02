// -*- C++ -*-
//*************************************************************************
//
// Copyright 2009-2016 by Wilson Snyder.  This program is free software;
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


#include "VSymTable.h"
#include "VAst.h"
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
# define DBG_SV_DUMP(SVp) {printf("%s:%d:\n",__FILE__,__LINE__); Perl_sv_dump(aTHX_ (SV*)(SVp)); }
# define DBG_UINFO(z,msg) {printf("%s:%d: ", __FILE__,__LINE__); cout << msg; }
#else
# define DBG_SV_DUMP(SVp)
# define DBG_UINFO(z,msg)
#endif

int VAstEnt::s_debug = 0;

// ACCESSORS
VAstType VAstEnt::type() {
    assert(this);
    AV* avp = castAVp();
    if (!avp || SvTYPE(avp) != SVt_PVAV || av_len(avp)<1) return VAstType::AN_ERROR;
    // $type_svpp = $this->[0]
    SV** type_svpp = av_fetch(avp, 0, 0);
    if (!type_svpp) return VAstType::AN_ERROR;
    VAstType type = (VAstType)(SvIV(*type_svpp));
    return type;
}

HV* VAstEnt::subhash() {
    assert(this);
    AV* avp = castAVp();
    if (!avp || SvTYPE(avp) != SVt_PVAV) return NULL; /*Error*/
    // $type_svpp = $this->[2]
    SV** hash_svpp = av_fetch(avp, 2, 0);
    if (!hash_svpp || !SvROK(*hash_svpp) || SvTYPE(SvRV(*hash_svpp)) != SVt_PVHV) return NULL; /*Error*/
    // $hash_hvp = %{$this->[2]}
    HV* hash_hvp = (HV*)(SvRV(*hash_svpp));
    return hash_hvp;
}

VAstEnt* VAstEnt::parentp() {
    assert(this);
    AV* avp = castAVp();
    if (!avp || SvTYPE(avp) != SVt_PVAV) return NULL; /*Error*/
    // $parent_svpp = $this->[1]
    SV** parent_svpp = av_fetch(avp, 1, 0);
    if (!parent_svpp || !SvROK(*parent_svpp) || SvTYPE(SvRV(*parent_svpp)) != SVt_PVAV) return NULL; /*Error*/
    // $parent_svp = @{$this->[1]}
    AV* parent_avp = (AV*)(SvRV(*parent_svpp));
    return avToSymEnt(parent_avp);
}

// METHODS
void VAstEnt::initNetlist(VFileLine* fl) {
    // Called on initial creation to check if this is a netlist, and/or create it
    assert(this);
    AV* avp = castAVp();
    if (!avp || SvTYPE(avp) != SVt_PVAV) { fl->error("Parser->symbol_table isn't an array reference"); }
    if (type() == VAstType::AN_ERROR) { // Need init
	initAVEnt(avp, VAstType::NETLIST, NULL);
    } else if (type() == VAstType::NETLIST) { // Already inited
    } else { fl->error("Parser->symbol_table isn't a netlist object (not created by the parser?)"); }
}

AV* VAstEnt::newAVEnt(VAstType type) {
    AV* avp = newAV();
    initAVEnt(avp, type, this->castAVp());
    return avp;
}

void VAstEnt::initAVEnt(AV* avp, VAstType type, AV* parentp) {
    // $avp = [type, parent, {}]
    av_push(avp, newSViv(type));
    if (parentp) {
	SV* parentsv = newRV((SV*)parentp);
#ifdef SvWEAKREF // Newer perls
	// We're making a circular reference, so to garbage collect properly we need to break it
	// On older Perl's we'll just leak.
	sv_rvweaken(parentsv);
#endif
	av_push(avp, parentsv );
    } else { // netlist top
	av_push(avp, &PL_sv_undef);
    }
    av_push(avp, newRV_noinc((SV*)newHV()) );
}

void VAstEnt::replaceInsert(VAstEnt* newentp, const string& name) {
    if (debug()) cout<<"VAstEnt::replaceInsert under="<<this<<" "<<newentp->ascii(name)<<"\"\n";
    HV* hvp = subhash(); assert(hvp);

    // $svpp = $table{$name}
    SV** svpp = hv_fetch(hvp, name.c_str(), name.length(), 1/*create*/);
    if (svpp) {} // unused

    // $avp = $newentp (premade avp)
    hv_store(hvp, name.c_str(), name.length(), newRV((SV*)newentp), 0);
}

VAstEnt* VAstEnt::replaceInsert(VAstType type, const string& name) {
    if (debug()) cout<<"VAstEnt::replaceInsert under="<<this<<" "<<type.ascii()<<"-\""<<name<<"\"\n";
    HV* hvp = subhash(); assert(hvp);

    // $svpp = $table{$name}
    SV** svpp = hv_fetch(hvp, name.c_str(), name.length(), 1/*create*/);
    if (svpp) {} // unused

    // $avp = [type, this, {}]
    AV* sub_avp = newAVEnt(type);
    hv_store(hvp, name.c_str(), name.length(), newRV_noinc((SV*)sub_avp), 0);
    return avToSymEnt(sub_avp);
}

VAstEnt* VAstEnt::findSym (const string& name) {
    HV* hvp = subhash();  assert(hvp);
    // $svpp = $table{$name}
    SV** svpp = hv_fetch(hvp, name.c_str(), name.length(), 0/*no-change*/);
    if (!svpp) return NULL;
    SV* svp = *svpp;
    if (!svp || !SvROK(svp) || SvTYPE(SvRV(svp)) != SVt_PVAV) return NULL;
    // $sub_avp = @{$table{$name}}
    AV* sub_avp = (AV*)(SvRV(svp));
    VAstEnt* entp = avToSymEnt(sub_avp);
    if (debug()) cout<<"VAstEnt::find found under="<<this<<" "<<entp->ascii(name)<<"\n";
    return entp;
}

VAstEnt* VAstEnt::findInsert (VAstType type, const string& name) {
    if (debug()) cout<<"VAstEnt::findInsert under="<<this<<" "<<type.ascii()<<"-\""<<name<<"\"\n";
    VAstEnt* symp = findSym(name);
    if (!symp) {
	symp = replaceInsert(type,name);
	assert(symp && symp == findSym(name));
    }
    return symp;
}

void VAstEnt::import(VAstEnt* pkgEntp, const string& id_or_star) {
    if (id_or_star != "*") {  // Import single entry
	if (VAstEnt* idEntp = pkgEntp->findSym(id_or_star)) {
	    // We can just add a second reference to the same AstEnt object
	    if (debug()) cout<<"VAstEnt::import under="<<this<<" "<<idEntp->ascii()<<"\n";
	    replaceInsert(idEntp, id_or_star);
	}
    } else {
	// Walk old sym table
	HV* hvp = pkgEntp->subhash();  assert(hvp);
	hv_iterinit(hvp);
	while (HE* hep = hv_iternext(hvp)) {
	    I32 retlen;
	    const char* namep = hv_iterkey(hep, &retlen);
	    string name = string(namep,retlen);
	    SV* svp = hv_iterval(hvp, hep);
	    VAstEnt* idEntp = avToSymEnt((AV*)(SvRV(svp)));
	    if (debug()) cout<<"VAstEnt::import under="<<this<<" "<<idEntp->ascii(name)<<"\n";
	    replaceInsert(idEntp, name);
	}
    }
}

string VAstEnt::ascii(const string& name) {
    string out = cvtToStr((void*)this)+"-"+type().ascii();
    if (name!="") out += "-\""+name+"\"";
    return out;
}

#undef DBG_SV_DUMP
#undef DBG_UINFO
