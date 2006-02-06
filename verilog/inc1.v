// DESCRIPTION: Verilog::Preproc: Example source code
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2006 by Wilson Snyder.
text.

`define FOOBAR  foo /*but not */ bar   /* or this either */
`define FOOBAR2  foobar2 // but not
`FOOBAR
`FOOBAR2

`define MULTILINE first part \
  		second part

/*******COMMENT*****/
`MULTILINE

//===========================================================================
`define syn_negedge_reset_l or negedge reset_l

`define DEEP deep
`define DEEPER `DEEP `DEEP
`DEEPER

`define nosubst NOT_SUBSTITUTED
`define WITHTICK "`nosubst"
"Inside: `nosubst"
`WITHTICK		  

`define withparam(a, b) a b LLZZ a b
`withparam(x,y)
`withparam(`withparam(p,q),`withparam ( r , s ))

`withparam(firstline
	,
	comma","line)

`define withquote(a, bar) a bar LLZZ "a" bar
`withquote( x , y)

`define noparam (a,b)
`noparam(a,b)

`define msg(x,y) `"x: `\`"y`\`"`"
$display(`msg(left side, right side))

`define foo(f) f``_suffix
`foo(bar)  

`define zap(which)   \
   	$c("Zap(\"",which,"\");");
`zap(bug1);
`zap("bug2");

/* Define inside comment: `DEEPER and `WITHTICK */
// More commentary: `zap(bug1); `zap("bug2");

`define EMPTY_TRUE
`ifndef EMPTY_TRUE
  `error "Empty is still true"
`endif
