module v_recursive ();
   parameter DEPTH = 1;
   generate
      if (DEPTH > 1) begin : rec
	v_recursive #(.DEPTH(DEPTH-1)) recurse ();
      end
   endgenerate
endmodule
