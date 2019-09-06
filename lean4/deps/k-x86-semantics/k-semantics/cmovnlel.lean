def cmovnlel1 : instruction :=
  definst "cmovnlel" $ do
    pattern fun (v_3025 : reg (bv 32)) (v_3026 : reg (bv 32)) => do
      v_4766 <- getRegister zf;
      v_4768 <- getRegister sf;
      v_4769 <- getRegister of;
      v_4772 <- getRegister v_3025;
      v_4773 <- getRegister v_3026;
      setRegister (lhs.of_reg v_3026) (mux (bit_and (notBool_ v_4766) (eq v_4768 v_4769)) v_4772 v_4773);
      pure ()
    pat_end;
    pattern fun (v_3018 : Mem) (v_3021 : reg (bv 32)) => do
      v_8090 <- getRegister zf;
      v_8092 <- getRegister sf;
      v_8093 <- getRegister of;
      v_8096 <- evaluateAddress v_3018;
      v_8097 <- load v_8096 4;
      v_8098 <- getRegister v_3021;
      setRegister (lhs.of_reg v_3021) (mux (bit_and (notBool_ v_8090) (eq v_8092 v_8093)) v_8097 v_8098);
      pure ()
    pat_end
