def vminpd1 : instruction :=
  definst "vminpd" $ do
    pattern fun (v_2605 : reg (bv 128)) (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) => do
      v_4484 <- getRegister v_2606;
      v_4485 <- eval (extract v_4484 0 64);
      v_4486 <- getRegister v_2605;
      v_4487 <- eval (extract v_4486 0 64);
      v_4491 <- eval (extract v_4484 64 128);
      v_4492 <- eval (extract v_4486 64 128);
      setRegister (lhs.of_reg v_2607) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4485 v_4487) (expression.bv_nat 1 1)) v_4485 v_4487) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4491 v_4492) (expression.bv_nat 1 1)) v_4491 v_4492));
      pure ()
    pat_end;
    pattern fun (v_2616 : reg (bv 256)) (v_2617 : reg (bv 256)) (v_2618 : reg (bv 256)) => do
      v_4503 <- getRegister v_2617;
      v_4504 <- eval (extract v_4503 0 64);
      v_4505 <- getRegister v_2616;
      v_4506 <- eval (extract v_4505 0 64);
      v_4510 <- eval (extract v_4503 64 128);
      v_4511 <- eval (extract v_4505 64 128);
      v_4515 <- eval (extract v_4503 128 192);
      v_4516 <- eval (extract v_4505 128 192);
      v_4520 <- eval (extract v_4503 192 256);
      v_4521 <- eval (extract v_4505 192 256);
      setRegister (lhs.of_reg v_2618) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4504 v_4506) (expression.bv_nat 1 1)) v_4504 v_4506) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4510 v_4511) (expression.bv_nat 1 1)) v_4510 v_4511) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4515 v_4516) (expression.bv_nat 1 1)) v_4515 v_4516) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4520 v_4521) (expression.bv_nat 1 1)) v_4520 v_4521))));
      pure ()
    pat_end;
    pattern fun (v_2599 : Mem) (v_2600 : reg (bv 128)) (v_2601 : reg (bv 128)) => do
      v_10118 <- getRegister v_2600;
      v_10119 <- eval (extract v_10118 0 64);
      v_10120 <- evaluateAddress v_2599;
      v_10121 <- load v_10120 16;
      v_10122 <- eval (extract v_10121 0 64);
      v_10126 <- eval (extract v_10118 64 128);
      v_10127 <- eval (extract v_10121 64 128);
      setRegister (lhs.of_reg v_2601) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10119 v_10122) (expression.bv_nat 1 1)) v_10119 v_10122) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10126 v_10127) (expression.bv_nat 1 1)) v_10126 v_10127));
      pure ()
    pat_end;
    pattern fun (v_2610 : Mem) (v_2611 : reg (bv 256)) (v_2612 : reg (bv 256)) => do
      v_10133 <- getRegister v_2611;
      v_10134 <- eval (extract v_10133 0 64);
      v_10135 <- evaluateAddress v_2610;
      v_10136 <- load v_10135 32;
      v_10137 <- eval (extract v_10136 0 64);
      v_10141 <- eval (extract v_10133 64 128);
      v_10142 <- eval (extract v_10136 64 128);
      v_10146 <- eval (extract v_10133 128 192);
      v_10147 <- eval (extract v_10136 128 192);
      v_10151 <- eval (extract v_10133 192 256);
      v_10152 <- eval (extract v_10136 192 256);
      setRegister (lhs.of_reg v_2612) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10134 v_10137) (expression.bv_nat 1 1)) v_10134 v_10137) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10141 v_10142) (expression.bv_nat 1 1)) v_10141 v_10142) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10146 v_10147) (expression.bv_nat 1 1)) v_10146 v_10147) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10151 v_10152) (expression.bv_nat 1 1)) v_10151 v_10152))));
      pure ()
    pat_end
