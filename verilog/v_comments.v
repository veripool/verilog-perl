`define ThirtyTwo 32

module v_comments ( a,                // Pragma for a
		    b,                // pragma for b
		    c,
		    d, d1, d2, d3 );
   input a;                     // comment for a
   inout [10:0] b;
   output [0:10] c;             // comment for c
   output [ ((2*`ThirtyTwo) - 1) : 0 ] d;
   output [ `ThirtyTwo : 0 ] d1;
   output [ ( `math - 1 ): 0 ] d2;
   output [ `ThirtyTwo - 1: 0 ] d3;

   reg           d;
   reg [11:0]    e;             // Comment for e

endmodule
