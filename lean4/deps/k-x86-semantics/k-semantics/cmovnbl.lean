def cmovnbl1 : instruction :=
  definst "cmovnbl" $ do
    pattern fun (v_2797 : reg (bv 32)) (v_2798 : reg (bv 32)) => do
      v_4575 <- getRegister cf;
      v_4578 <- getRegister v_2797;
      v_4579 <- getRegister v_2798;
      setRegister (lhs.of_reg v_2798) (mux (notBool_ (eq v_4575 (expression.bv_nat 1 1))) v_4578 v_4579);
      pure ()
    pat_end;
    pattern fun (v_2793 : Mem) (v_2794 : reg (bv 32)) => do
      v_8196 <- getRegister cf;
      v_8199 <- evaluateAddress v_2793;
      v_8200 <- load v_8199 4;
      v_8201 <- getRegister v_2794;
      setRegister (lhs.of_reg v_2794) (mux (notBool_ (eq v_8196 (expression.bv_nat 1 1))) v_8200 v_8201);
      pure ()
    pat_end
