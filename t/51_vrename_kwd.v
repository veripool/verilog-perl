// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010-2012 by Wilson Snyder.

module 51_vrename_kwd;
   // Keyword
   wire do;
   wire \do ;
   // Non escapes
   wire non_2non;
   wire non_2non_nospace
        ;
   wire non_2ext;
   wire non_2ext_nospace
        ;
   wire non_2esc;
   wire non_2esc_nospace
        ;
   // Extra unnecessary escapes
   // Note we cannot legally remove spaces if replacing with non-escaped name
   wire \ext_2non ;
   wire \ext_2non_nospace
        ;
   wire \ext_2ext ;
   wire \ext_2ext_nospace
        ;
   wire \ext_2esc ;
   wire \ext_2esc_nospace
        ;
   // Necessary escapes
   wire \esc[ape]_2non ;
   wire \esc[ape]_2non_nospace
	;
   wire \esc[ape]_2ext ;
   wire \esc[ape]_2ext_nospace
	;
   wire \esc[ape]_2esc ;
   wire \esc[ape]_2esc_nospace
	;
   // Strings
   initial $display("foo");
   initial $display("foo.foo");
   initial $display("baz_foo");
   initial $display("foo_baz");
endmodule
