// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009-2012 by Wilson Snyder.

`include "v_sv_pkg"

interface sv_if_ported (input clk);
endinterface

module v_sv_mod (v_sv_intf intf, input clk);

   // Import types
   import v_sv_pkg::*;

   // Internal interface (unconnected)
   sv_if_ported if_ported(.clk(clk));

   // Grab a program
   v_sv_pgm pgm();

endmodule

