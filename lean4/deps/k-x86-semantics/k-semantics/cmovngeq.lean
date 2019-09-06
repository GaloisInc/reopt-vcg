def cmovngeq1 : instruction :=
  definst "cmovngeq" $ do
    pattern fun (v_2977 : reg (bv 64)) (v_2978 : reg (bv 64)) => do
      v_4700 <- getRegister sf;
      v_4701 <- getRegister of;
      v_4704 <- getRegister v_2977;
      v_4705 <- getRegister v_2978;
      setRegister (lhs.of_reg v_2978) (mux (notBool_ (eq v_4700 v_4701)) v_4704 v_4705);
      pure ()
    pat_end;
    pattern fun (v_2973 : Mem) (v_2974 : reg (bv 64)) => do
      v_8039 <- getRegister sf;
      v_8040 <- getRegister of;
      v_8043 <- evaluateAddress v_2973;
      v_8044 <- load v_8043 8;
      v_8045 <- getRegister v_2974;
      setRegister (lhs.of_reg v_2974) (mux (notBool_ (eq v_8039 v_8040)) v_8044 v_8045);
      pure ()
    pat_end
