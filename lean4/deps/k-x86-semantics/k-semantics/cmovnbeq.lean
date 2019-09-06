def cmovnbeq1 : instruction :=
  definst "cmovnbeq" $ do
    pattern fun (v_2869 : reg (bv 64)) (v_2870 : reg (bv 64)) => do
      v_4572 <- getRegister cf;
      v_4574 <- getRegister zf;
      v_4577 <- getRegister v_2869;
      v_4578 <- getRegister v_2870;
      setRegister (lhs.of_reg v_2870) (mux (bit_and (notBool_ v_4572) (notBool_ v_4574)) v_4577 v_4578);
      pure ()
    pat_end;
    pattern fun (v_2865 : Mem) (v_2866 : reg (bv 64)) => do
      v_7947 <- getRegister cf;
      v_7949 <- getRegister zf;
      v_7952 <- evaluateAddress v_2865;
      v_7953 <- load v_7952 8;
      v_7954 <- getRegister v_2866;
      setRegister (lhs.of_reg v_2866) (mux (bit_and (notBool_ v_7947) (notBool_ v_7949)) v_7953 v_7954);
      pure ()
    pat_end
