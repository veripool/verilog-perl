// $Revision: 1.10 $$Date: 2004/11/15 15:45:14 $$Author: wsnyder $
// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2004 by Wilson Snyder.

module v_hier_sub (/*AUTOARG*/
   // Outputs
   qvec, 
   // Inputs
   clk, avec
   );
   input clk;
   input [3:0] avec;
   output [3:0] qvec;

   v_hier_subsub #(
		   .IGNORED(20)
		   )
     subsub0 (
	      // Outputs
	      .q		(qvec[0]),
	      // Inputs
	      .a		(1'b1));

   // By pin position
   v_hier_subsub subsub2 (qvec[2], 1'b0);

endmodule
