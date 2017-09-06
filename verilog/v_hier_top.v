// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2012 by Wilson Snyder.

`define hsub v_hier_sub

module v_hier_top (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;	/* pragma jsc_clk */

   defparam sub.FROM_DEFPARAM = 2;
   `hsub sub (/*AUTOINST*/
	      // Outputs
	      .qvec			(qvec[3:0]),
	      // Inputs
	      .avec			({avec[3],avec[2:0]}),
	      .clk			(1'b0));

   missing missing ();

   v_recursive #(.DEPTH(3)) recursive ();

   // Width checks, bug65
   wire  	WC_w1;
   wire [0:0]   WC_w1b;
   wire [2:0]   WC_w3;
   wire [-1:2]  WC_w4;
   localparam         WC_p32=0;
   localparam [0:0]   WC_p1=0;
   localparam [2:0]   WC_p3=0;
   localparam [-1:2]  WC_p4=0;
   localparam integer WC_pint=0;

   // Assignments
   wire  asn_clk;
   assign asn_clk = clk;

endmodule

localparam  GLOBAL_PARAM = 1;

// Local Variables:
// eval:(verilog-read-defines)
// End:
