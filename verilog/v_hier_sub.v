// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2010 by Wilson Snyder.

module v_hier_sub (/*AUTOARG*/
   input clk,
   input [3:0] avec,	// Comment for v_hier_sub, avec
   output [3:0] qvec	/* Comment for v_hier_sub, qvec */
   );

   supply1 	a1;

   v_hier_subsub #(
		   .IGNORED('sh20)
		   )
     \subsub0 (
	      // Outputs
	      .q		(qvec[0]),
	      // Inputs
	      .a		(a1));  // Comment for subsub cell


   generate
      genvar 	K, K_UNUSED;
      for (K=0; K<1; K=K+1) begin : genloop
	 // By pin position, inside generate
	 v_hier_subsub subsub2 (qvec[2], 1'b0);
      end
   endgenerate

   function foo;
      (* attribute *)
      /* synopsys metacommenttest */
      input not_part_of_pinlist;
      foo = not_part_of_pinlist;
   endfunction

endmodule
