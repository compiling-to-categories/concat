/***
* cmplx.v - General purpose utilities for working with complex numbers
*           in Verilog.
*
* Original author: David Banas <capn.freako@gmail.com>
* Original date:   August 28, 2017
*
* Copyright (c) 2017 David Banas; all rights reserved World wide.
***/

module cmplx;
  parameter pi = 3.1416;

// Complex addition.
task add;
  input  real x1_r, x1_i, x2_r, x2_i;
  output real y_r, y_i;

  begin
    y_r = x1_r + x2_r
    y_i = x1_i + x2_i
  end
endtask

// Complex multiplication.
task mul;
  input  real x1_r, x1_i, x2_r, x2_i;
  output real y_r, y_i;

  begin
    y_r = x1_r * x2_r - x1_i * x2_i;
    y_i = x1_r * x2_i + x1_i * x2_r;
  end
endtask

// Complex identity scalar.
task cis;
  input  real theta;
  output real y_r, y_i;

  begin
    y_r = trig.cos(theta);
    y_i = trig.sin(theta);
  end
endtask

endmodule

