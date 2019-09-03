def cmovnlel1 : instruction :=
  definst "cmovnlel" $ do
    pattern fun (v_2944 : reg (bv 32)) (v_2945 : reg (bv 32)) => do
      v_4780 <- getRegister zf;
      v_4783 <- getRegister sf;
      v_4785 <- getRegister of;
      v_4789 <- getRegister v_2944;
      v_4790 <- getRegister v_2945;
      setRegister (lhs.of_reg v_2945) (mux (bit_and (notBool_ (eq v_4780 (expression.bv_nat 1 1))) (eq (eq v_4783 (expression.bv_nat 1 1)) (eq v_4785 (expression.bv_nat 1 1)))) v_4789 v_4790);
      pure ()
    pat_end;
    pattern fun (v_2940 : Mem) (v_2941 : reg (bv 32)) => do
      v_8316 <- getRegister zf;
      v_8319 <- getRegister sf;
      v_8321 <- getRegister of;
      v_8325 <- evaluateAddress v_2940;
      v_8326 <- load v_8325 4;
      v_8327 <- getRegister v_2941;
      setRegister (lhs.of_reg v_2941) (mux (bit_and (notBool_ (eq v_8316 (expression.bv_nat 1 1))) (eq (eq v_8319 (expression.bv_nat 1 1)) (eq v_8321 (expression.bv_nat 1 1)))) v_8326 v_8327);
      pure ()
    pat_end
