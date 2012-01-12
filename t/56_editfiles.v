// DESCRIPTION: Verilog::Preproc: Example source code
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007-2012 by Wilson Snyder.

a_front_matter;

module a;
   wire inside_module_a;  /* // double cmt */
endmodule

b_front_matter;

`ifdef B_HAS_X
module b;
`elsif
module b (input x);
`endif
   wire inside_module_b;
   // synopsys translate_off
   wire in_translate_off;
   // synopsys translate_on
endmodule
