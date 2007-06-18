module buffer (
    output Z,
    input  A);
   buf u_buf(Z, A);
endmodule

module gate (
    output Z,
    input  A);
   buffer u_buf(Z, A);
endmodule
