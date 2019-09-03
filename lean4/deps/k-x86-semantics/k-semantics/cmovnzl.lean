def cmovnzl1 : instruction :=
  definst "cmovnzl" $ do
    pattern fun (v_3103 : reg (bv 32)) (v_3104 : reg (bv 32)) => do
      v_4984 <- getRegister zf;
      v_4987 <- getRegister v_3103;
      v_4988 <- getRegister v_3104;
      setRegister (lhs.of_reg v_3104) (mux (notBool_ (eq v_4984 (expression.bv_nat 1 1))) v_4987 v_4988);
      pure ()
    pat_end;
    pattern fun (v_3099 : Mem) (v_3100 : reg (bv 32)) => do
      v_8463 <- getRegister zf;
      v_8466 <- evaluateAddress v_3099;
      v_8467 <- load v_8466 4;
      v_8468 <- getRegister v_3100;
      setRegister (lhs.of_reg v_3100) (mux (notBool_ (eq v_8463 (expression.bv_nat 1 1))) v_8467 v_8468);
      pure ()
    pat_end
