def cmovngq1 : instruction :=
  definst "cmovngq" $ do
    pattern fun (v_3004 : reg (bv 64)) (v_3005 : reg (bv 64)) => do
      v_4738 <- getRegister zf;
      v_4739 <- getRegister sf;
      v_4740 <- getRegister of;
      v_4744 <- getRegister v_3004;
      v_4745 <- getRegister v_3005;
      setRegister (lhs.of_reg v_3005) (mux (bit_or v_4738 (notBool_ (eq v_4739 v_4740))) v_4744 v_4745);
      pure ()
    pat_end;
    pattern fun (v_3000 : Mem) (v_3001 : reg (bv 64)) => do
      v_8068 <- getRegister zf;
      v_8069 <- getRegister sf;
      v_8070 <- getRegister of;
      v_8074 <- evaluateAddress v_3000;
      v_8075 <- load v_8074 8;
      v_8076 <- getRegister v_3001;
      setRegister (lhs.of_reg v_3001) (mux (bit_or v_8068 (notBool_ (eq v_8069 v_8070))) v_8075 v_8076);
      pure ()
    pat_end
