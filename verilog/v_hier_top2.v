// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2012 by Wilson Snyder.

module v_hier_top2 (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   v_hier_noport noport ();

   v_hier_noport #(.P(1)) noportp ();

   inout [2:0] iosig/* synthesis useioff = 1 //*synthesis fpga_attr = "BLAH=ON"//* synthesis fpga_pin = "A22"*/;/* synthesis aftersemi*/ // NetListName=F12_IO

endmodule
