// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009-2009 by Wilson Snyder.

`include "v_sv_pkg"

module v_sv_mod (v_sv_intf intf);

   // Import types
   import v_sv_pkg::*;

   // Grab a program
   v_sv_pgm pgm();

endmodule
