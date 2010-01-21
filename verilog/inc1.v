// DESCRIPTION: Verilog::Preproc: Example source code
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2010 by Wilson Snyder.
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
`foo(bar)  more

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

//======================================================================
// RT bug 34429

`define ls left_side
`define rs right_side
`define noarg  na
`define thru(x) x
`define thruthru `ls `rs	// Doesn't expand
`define msg(x,y) `"x: `\`"y`\`"`"
   initial begin
      //$display(`msg( \`, \`));  // Illegal
      $display(`msg(pre `thru(thrupre `thru(thrumid) thrupost) post,right side));
      $display(`msg(left side,right side));
      $display(`msg( left side , right side ));
      $display(`msg( `ls , `rs ));
      $display(`msg( `noarg , `rs ));
      $display(`msg( prep ( midp1 `ls midp2 ( outp ) ) , `rs ));
      $display(`msg(`noarg,`noarg`noarg));
      $display(`msg( `thruthru , `thruthru ));   // Results vary between simulators
      $display(`msg(`thru(),));  // Empty
      $display(`msg(`thru(left side),`thru(right side)));
      $display(`msg( `thru( left side ) , `thru( right side ) ));

`define twoline first \
 second
      $display(`msg(twoline, `twoline));

      //$display(`msg(left side, \ right side \ ));  // Not sure \{space} is legal.
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

`define ADD_UP(a,c)          \
wire  tmp_``a = a; \
wire  tmp_``c = tmp_``a + 1; \
assign c = tmp_``c ;

module add1 ( input wire d1, output wire o1);
 `ADD_UP(d1,o1)   // expansion is OK
endmodule
module add2 ( input wire d2, output wire o2);
 `ADD_UP( d2 , o2 )  // expansion is bad
endmodule

//======================================================================
// Quotes are legal in protected blocks.  Grr.
module prot();
`protected
    I!#r#e6<_Q{{E2+]I3<[3s)1@D|'E''i!O?]jD>Jo_![Cl)
    #nj1]p,3^1~,="E@QZB\T)eU\pC#C|7=\$J$##A[@-@{Qk]
`endprotected
endmodule
//"

//======================================================================
// macro call with define that has comma
`define REG_H   6
`define REG_L   7
`define _H      regs[`REG_H]
`define _L      regs[`REG_L]
`define _HL     {`_H, `_L}
`define EX_WRITE(ad, da)      begin addr <= (ad); wdata <= (da); wr <= 1; end
`define EX_READ(ad)           begin addr <= (ad); rd <= 1; end

`EX_READ((`_HL + 1)) and `EX_WRITE((`_HL), rdata)
`EX_READ(`_HL + 1)
`EX_WRITE(`_HL, rdata)  more

//======================================================================
// include of parameterized file
`define INCNAME "inc4.v"
`include `INCNAME
`ifndef INC4
 `error "No Inc4"
`endif
`undef INC4

`ifdef NOT_DEFINED_INC
 `include NOT_DEFINED_INC
`endif

//======================================================================
// macro call with , in {}

`define xxerror(logfile, msg) $blah(logfile,msg)
`xxerror("ab,cd","e,f");
`xxerror(this.logfile, vec);
`xxerror(this.logfile, vec[1,2,3]);
`xxerror(this.logfile, {blah.name(), " is not foo"});

//======================================================================
// pragma/default net type

`pragma foo = 1
`default_nettype none
`default_nettype uwire

//======================================================================
// bug84

`define ARGPAR(a,  // Hello, comments MIGHT not be legal
  /*more,,)cmts*/ b  // But newlines ARE legal... who speced THAT?
  ) (a,b)
`ARGPAR(p,q)
`ARGPAR( //Here
	      x,
  y   //Too
  )
Line: `__LINE__

//======================================================================
// defines split arguments

`define BEGIN begin
`define END end
`define BEGINEND `BEGIN`END
`define quoteit(x) `"x`"
`BEGIN`END   // 2001 spec doesn't require two tokens, so "beginend" ok
`BEGINEND    // 2001 spec doesn't require two tokens, so "beginend" ok
`quoteit(`BEGIN`END)  // No space "beginend"

//======================================================================
// bug106
`define \esc`def got_escaped
`ifdef \esc`def
  `\esc`def
`endif
Not a \`define

//======================================================================
// misparsed comma in submacro
`define sb bee
`define appease_emacs_paren_matcher (
`define sa(l) x,y)
`define sfoo(q,r) q--r
`sfoo(`sa(el),`sb)  submacro has comma paren

//======================================================================
// bug191
`define bug191(bits) $display("bits %d %d", $bits(foo), `bits);
`bug191(10)

//======================================================================
// 1800-2009
`define UDALL
`ifndef PREDEF_COMMAND_LINE `error "Test setup error, PREDEF_COMMAND_LINE pre-missing" `endif
`undefineall
`ifdef UDALL `error "undefineall failed" `endif
`ifndef PREDEF_COMMAND_LINE `error "Deleted too much, no PREDEF_COMMAND_LINE" `endif
