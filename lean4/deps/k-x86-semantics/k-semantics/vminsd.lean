def vminsd1 : instruction :=
  definst "vminsd" $ do
    pattern fun (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) (v_2663 : reg (bv 128)) => do
      v_4993 <- getRegister v_2662;
      v_4995 <- eval (extract v_4993 64 128);
      v_4996 <- getRegister v_2661;
      v_4997 <- eval (extract v_4996 64 128);
      setRegister (lhs.of_reg v_2663) (concat (extract v_4993 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4995 v_4997) (expression.bv_nat 1 1)) v_4995 v_4997));
      pure ()
    pat_end;
    pattern fun (v_2656 : Mem) (v_2657 : reg (bv 128)) (v_2658 : reg (bv 128)) => do
      v_11043 <- getRegister v_2657;
      v_11045 <- eval (extract v_11043 64 128);
      v_11046 <- evaluateAddress v_2656;
      v_11047 <- load v_11046 8;
      setRegister (lhs.of_reg v_2658) (concat (extract v_11043 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_11045 v_11047) (expression.bv_nat 1 1)) v_11045 v_11047));
      pure ()
    pat_end
