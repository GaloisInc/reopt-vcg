def cmovnsw1 : instruction :=
  definst "cmovnsw" $ do
    pattern fun (v_3146 : reg (bv 16)) (v_3147 : reg (bv 16)) => do
      v_5024 <- getRegister sf;
      v_5027 <- getRegister v_3146;
      v_5028 <- getRegister v_3147;
      setRegister (lhs.of_reg v_3147) (mux (notBool_ (eq v_5024 (expression.bv_nat 1 1))) v_5027 v_5028);
      pure ()
    pat_end;
    pattern fun (v_3137 : Mem) (v_3138 : reg (bv 16)) => do
      v_8468 <- getRegister sf;
      v_8471 <- evaluateAddress v_3137;
      v_8472 <- load v_8471 2;
      v_8473 <- getRegister v_3138;
      setRegister (lhs.of_reg v_3138) (mux (notBool_ (eq v_8468 (expression.bv_nat 1 1))) v_8472 v_8473);
      pure ()
    pat_end
