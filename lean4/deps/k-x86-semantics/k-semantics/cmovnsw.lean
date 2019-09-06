def cmovnsw1 : instruction :=
  definst "cmovnsw" $ do
    pattern fun (v_3172 : reg (bv 16)) (v_3173 : reg (bv 16)) => do
      v_4936 <- getRegister sf;
      v_4938 <- getRegister v_3172;
      v_4939 <- getRegister v_3173;
      setRegister (lhs.of_reg v_3173) (mux (notBool_ v_4936) v_4938 v_4939);
      pure ()
    pat_end;
    pattern fun (v_3164 : Mem) (v_3165 : reg (bv 16)) => do
      v_8206 <- getRegister sf;
      v_8208 <- evaluateAddress v_3164;
      v_8209 <- load v_8208 2;
      v_8210 <- getRegister v_3165;
      setRegister (lhs.of_reg v_3165) (mux (notBool_ v_8206) v_8209 v_8210);
      pure ()
    pat_end
