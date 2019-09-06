def cmovnzw1 : instruction :=
  definst "cmovnzw" $ do
    pattern fun (v_3199 : reg (bv 16)) (v_3200 : reg (bv 16)) => do
      v_4966 <- getRegister zf;
      v_4968 <- getRegister v_3199;
      v_4969 <- getRegister v_3200;
      setRegister (lhs.of_reg v_3200) (mux (notBool_ v_4966) v_4968 v_4969);
      pure ()
    pat_end;
    pattern fun (v_3195 : Mem) (v_3196 : reg (bv 16)) => do
      v_8227 <- getRegister zf;
      v_8229 <- evaluateAddress v_3195;
      v_8230 <- load v_8229 2;
      v_8231 <- getRegister v_3196;
      setRegister (lhs.of_reg v_3196) (mux (notBool_ v_8227) v_8230 v_8231);
      pure ()
    pat_end
